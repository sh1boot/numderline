#!/usr/bin/env python3
# Based on https://github.com/powerline/fontpatcher/blob/develop/scripts/powerline-fontpatcher
# Used under the MIT license

import argparse
import sys
import random
import re
import subprocess
import os.path
import json
import shutil
import zipfile

from itertools import chain
from collections import defaultdict

try:
    import fontforge
    import psMat
    # from fontTools.misc.py23 import *
    from fontTools.ttLib import TTFont
    from fontTools.feaLib.builder import addOpenTypeFeatures, Builder
except ImportError:
    sys.stderr.write('The required FontForge and fonttools modules could not be loaded.\n\n')
    sys.stderr.write('You need FontForge with Python bindings for this script to work.\n')
    sys.exit(1)


FONT_NAME_RE = re.compile(r'^([^-]*)(?:(-.*))?$')

DECIMAL_LIST = '0123456789'
HEXADECIMAL_LIST = '0123456789abcdefABCDEF'

class deferred_map:
    def __init__(self, function, sequence):
        self._f = function
        self._sequence = sequence

    def __iter__(self):
        return map(self._f, self._sequence)
    def __getitem__(self, i):
        return self._f(self._sequence[ord(i) if isinstance(i, str) else i])

def gen_feature(names, digit_groups, monospace, feature_name):
    feature_commas = 'dgco'
    feature_dots = 'dgdo'
    feature_comma_decimals = 'dgcd'
    feature_dot_decimals = 'dgdd'

    dot_name = names['.']
    comma_name = names[',']

    preamble = f"""languagesystem DFLT dflt;
languagesystem latn dflt;
languagesystem cyrl dflt;
languagesystem grek dflt;
languagesystem kana dflt;
"""

    setup = ''.join([ f'@{key}=[{" ".join(value)}];\n' for key, value in digit_groups.items() ])

    # a rule to avoid treating `..0` as decimal point captures the first digit,
    # but actually it may be a part of `..0x` so allow this rule to override
    # that capture.
    false_capture = digit_groups['capture_L'][0]

    def ifdef(group): return '' if group in digit_groups else '#'
    def ifndf(group): return '#' if group in digit_groups else ''

    m = '' if monospace else '#'
    not_m = '#' if monospace else ''

    lookups = f"""
## Lookups are executed in the order they are listed below, regardless of the
## order they are referenced in the feature rules that follow.

lookup CAPTURE {{
    # capture digits following `.`, but not `..`
    sub {dot_name} {dot_name} @digits' by @capture_L;
    sub {dot_name} @digits' by @capture_R;
    sub @capture_R @digits' by @capture_R;

    # capture hex digits following 0x
    sub [{names['0']} {false_capture}] [{names['x']} {names['X']}] @xdigits' by @xcapture_L;
    sub @xcapture_L @xdigits' by @xcapture_L;

    # capture digits that didn't match above
    sub @digits' by @capture_L;
}} CAPTURE;

lookup DOTS_TO_COMMAS {{
    # YIKES!!
    sub @capture_L {dot_name}' @capture_R by {comma_name};
}} DOTS_TO_COMMAS;

lookup GROUP_DIGITS {{
    rsub @capture_L @capture_L @capture_L' @capture_L @capture_L by @group_L;
    rsub @xcapture_L @xcapture_L' @xcapture_L @xcapture_L @xcapture_L by @xgroup_L;
}} GROUP_DIGITS;

lookup GROUP_DECIMALS {{
    sub [ {dot_name} {comma_name} @group_R ] @capture_R @capture_R @capture_R' @capture_R by @group_R;
}} GROUP_DECIMALS;

lookup REFLOW_DIGITS {{
    {ifdef("phase1_L")} sub @group_L @capture_L' by @phase1_L;
    {ifdef("phase2_L")} sub @phase1_L @capture_L' by @phase2_L;
    {ifdef("phase3_L")} sub @phase2_L @capture_L' by @phase3_L;

    {ifdef("xphase1_L")} sub @xgroup_L @xcapture_L' by @xphase1_L;
    {ifdef("xphase2_L")} sub @xphase1_L @xcapture_L' by @xphase2_L;
    {ifdef("xphase3_L")} sub @xphase2_L @xcapture_L' by @xphase3_L;

    {ifdef("phase2_R")} sub [ @group_R {dot_name} {comma_name} ] @capture_R' by @phase2_R;
    {ifdef("phase2_R")} sub @phase2_R @capture_R' by @phase1_R;

    sub @capture_L' by @digits;
    sub @xcapture_L' by @xdigits;
    sub @capture_R' by @digits;
}} REFLOW_DIGITS;
"""

    features = f"""
feature {feature_name} {{
    lookup CAPTURE;
    lookup GROUP_DIGITS;
    lookup GROUP_DECIMALS;
    lookup REFLOW_DIGITS;
}} {feature_name};

feature {feature_commas} {{
    lookup CAPTURE;
    lookup GROUP_DIGITS;
    #lookup GROUP_DECIMALS;
    lookup REFLOW_DIGITS;
    sub @group_L' by @group_L_comma;
}} {feature_commas};

feature {feature_comma_decimals} {{
    lookup CAPTURE;
    lookup GROUP_DIGITS;
    #lookup GROUP_DECIMALS;
    lookup REFLOW_DIGITS;
    sub @group_L' by @group_L_comma;
    sub @group_R' by @group_R_comma;
}} {feature_comma_decimals};

feature {feature_dots} {{
    lookup CAPTURE;
    lookup DOTS_TO_COMMAS;
    lookup GROUP_DIGITS;
    #lookup GROUP_DECIMALS;
    lookup REFLOW_DIGITS;
    sub @group_L' by @group_L_dot;
}} {feature_dots};

feature {feature_dot_decimals} {{
    lookup CAPTURE;
    lookup DOTS_TO_COMMAS;
    lookup GROUP_DIGITS;
    lookup GROUP_DECIMALS;
    lookup REFLOW_DIGITS;
    sub @group_L' by @group_L_dot;
    sub @group_R' by @group_R_dot;
}} {feature_dot_decimals};
"""
    wholefile = '\n'.join([ preamble, setup, lookups, features ])
    with open('mods.fea', 'w') as f:
        f.write(wholefile)
    #for line, txt in enumerate(wholefile.split('\n')):
    #    print(line + 1, txt)

def shift_layer(layer, shift):
    layer = layer.dup()
    mat = psMat.translate(shift, 0)
    layer.transform(mat)
    return layer

def squish_layer(layer, squish, squishy):
    layer = layer.dup()
    mat = psMat.scale(squish, squishy)
    layer.transform(mat)
    return layer

def insert_separator(glyph, comma_glyph, gap_size, monospace, l=1):
    comma_layer = comma_glyph.layers[l].dup()
    x_shift = (abs(gap_size) - comma_glyph.width) / 2
    if gap_size < 0:
        x_shift += glyph.width
    if monospace:
        if gap_size < 0:
            x_shift -= abs(gap_size)
    else:
        if gap_size > 0:
            mat = psMat.translate(gap_size, 0)
            glyph.transform(mat)
        else:
            glyph.width += abs(gap_size)

    mat = psMat.translate(x_shift, 0)
    comma_layer.transform(mat)
    glyph.layers[l] += comma_layer

def annotate_glyph(glyph, extra_glyph, l=1):
    layer = extra_glyph.layers[l].dup()
    mat = psMat.translate(-(extra_glyph.width/2), 0)
    layer.transform(mat)
    mat = psMat.scale(0.3, 0.3)
    layer.transform(mat)
    mat = psMat.translate((extra_glyph.width/2), 0)
    layer.transform(mat)
    mat = psMat.translate(0, -600)
    layer.transform(mat)
    glyph.layers[l] += layer

def out_path(name):
    return f'out/{name}.ttf'

def patch_one_font(font, rename_font, feature_name, monospace, gap_size, squish, squishy, squish_all, debug_annotate):
    font.encoding = 'ISO10646'
    names = deferred_map(lambda o: o.glyphname, font)
    sizes = deferred_map(lambda o: o.width, font)

    if isinstance(gap_size, str):
        if len(gap_size) == 1:
            gap_size = sizes[gap_size]
            if gap_size == sizes['0']: gap_size = sizes['0'] // 3
        else:
            gap_size = int(gap_size)

    # Rename font
    if rename_font:
        mod_name = 'DigitGrouping'
        if gap_size != 0:
            mod_name += f'Gap{gap_size}'
            if squish != 1.0:
                mod_name += f'Squish{squish}'
            if squishy != 1.0:
                mod_name += f'SquishY{squishy}'
        if debug_annotate:
            mod_name += f'Debug{random.randrange(65536):04X}'

        mod_name = mod_name.replace('.', 'p')

        font.familyname += ' with '+mod_name
        font.fullname += ' with '+mod_name
        fontname, style = FONT_NAME_RE.match(font.fontname).groups()
        font.fontname = fontname + 'With' + mod_name
        if style is not None:
            font.fontname += style
        font.appendSFNTName(
            'English (US)', 'Preferred Family', font.familyname)
        font.appendSFNTName(
            'English (US)', 'Compatible Full', font.fullname)

    print(f'Sizes of dot: {sizes["."]}  comma: {sizes[","]}  space: {sizes[" "]}  zero: {sizes["0"]}  Gap: {gap_size}')
    # print(f'Squish: {squish}, recommended: {(3 * sizes["0"] - gap_size) / (3 * sizes["0"])}')

    layer = 1  # is it ever anything else?

    def make_copy(to_name, from_name, shift, gap_size=0, separator=None, annotation=None):
        font.selection.select(from_name)
        font.copy()
        glyph = font.createChar(-1, to_name)
        font.selection.select(glyph)
        font.paste()
        if squish != 1.0:
            glyph.layers[layer] = squish_layer(glyph.layers[layer], squish, squishy)
        if shift != 0:
            glyph.layers[layer] = shift_layer(glyph.layers[layer], shift)
        if separator is not None:
            insert_separator(glyph, font[ord(separator)], gap_size, monospace, layer)
        else:
            glyph.width += gap_size
        if annotation is not None:
            annotate_glyph(glyph, font[annotation], layer)

    shift_step = gap_size / 3 if monospace else 0
    shift = shift_step * 2.5
    digit_groups = {
            "digits": [ names[d] for d in DECIMAL_LIST ],
            "xdigits": [ names[d] for d in HEXADECIMAL_LIST ],
            }

    for group, sep, right, digits, anno in [
            ( 'xgroup_L',      ' ', False, HEXADECIMAL_LIST, '<' ),
            ( 'group_R',       ' ',  True, DECIMAL_LIST,     '>' ),
            ( 'group_L_dot',   '.', False, DECIMAL_LIST,     '[' ),
            ( 'group_R_dot',   '.',  True, DECIMAL_LIST,     ']' ),
            ( 'group_L_comma', ',', False, DECIMAL_LIST,     '(' ),
            ( 'group_R_comma', ',',  True, DECIMAL_LIST,     ')' ),
            ]:
        anno = names[anno] if debug_annotate else None
        table = []
        for digit_i, digit in enumerate(digits):
            name = group + f'_d{digit_i}'
            if right:
                make_copy(name, names[digit], -shift, -gap_size, sep, anno)
            else:
                make_copy(name, names[digit], shift, gap_size, sep, anno)
            table.append(name)
        digit_groups[group] = table
        if group[0] == 'x': digit_groups[group[1:]] = table[:10]

    if monospace:
        for step, group, right, digits, anno in [
                ( shift_step, 'xphase1_L', False, HEXADECIMAL_LIST, '1' ),
                ( 0,           'phase1_R',  True, DECIMAL_LIST,     '9' ),
                ( shift_step, 'xphase2_L', False, HEXADECIMAL_LIST, '2' ),
                ( 0,           'phase2_R',  True, DECIMAL_LIST,     '8' ),
                ]:
            anno = names[anno] if debug_annotate else None
            shift -= step
            table = []
            for digit_i, digit in enumerate(digits):
                name = group + f'_d{digit_i}'
                if right:
                    make_copy(name, digit, -shift, annotation=anno)
                else:
                    make_copy(name, digit, shift, annotation=anno)
                table.append(name)
            digit_groups[group] = table
            if group[0] == 'x': digit_groups[group[1:]] = table[:10]

    # create placeholder glyphs, not to be rendered.
    font.selection.select(ord(' '))  # prefer select(0x2007) which is space the same width as '0', but may not exist
    font.copyReference()
    for group, digits in [
            ( 'xcapture_L', HEXADECIMAL_LIST ),
            ( 'capture_L', DECIMAL_LIST ),
            ( 'capture_R', DECIMAL_LIST ),
            ]:
        table = []
        for digit_i, digit in enumerate(digits):
            name = group + f'_d{digit_i}'
            table.append(name)
            font.selection.select(font.createChar(-1, name))
            #font.selection.select(name)
            font.paste()
        digit_groups[group] = table

    if squish_all and squish != 1.0:
        for digit in DECIMAL_LIST:
            glyph = font[digit]
            glyph.layers[layer] = squish_layer(glyph.layers[layer], squish, squishy)

    gen_feature(names, digit_groups, monospace, feature_name)

    font.generate('out/tmp.ttf')
    ft_font = TTFont('out/tmp.ttf')
    addOpenTypeFeatures(ft_font, 'mods.fea', tables=['GSUB'])
    # replacement to comply with SIL Open Font License
    out_name = font.fullname.replace('Source ', 'Sauce ')
    ft_font.save(out_path(out_name))
    print(f"> Created '{out_name}'")

    return out_name


def patch_fonts(target_fonts, **kwargs):
    res = None
    for target_file in target_fonts:
        for font in fontforge.fontsInFile(target_file.name):
            target_font = fontforge.open(f'{target_file.name}({font})')
            try:
                res = patch_one_font(target_font, **kwargs)
            finally:
                target_font.close()
    return res


def main(argv):
    parser = argparse.ArgumentParser(
        description=('Font patcher for Numderline. '
                     'Requires FontForge with Python bindings. '
                     'Stores the patched font as a new, renamed font file by default.')
    )
    parser.add_argument('target_fonts', help='font files to patch', metavar='font',
                        nargs='*', type=argparse.FileType('rb'))
    parser.add_argument('--no-rename',
                        help='don\'t add " with Numderline" to the font name',
                        default=True, action='store_false', dest='rename_font')
    parser.add_argument('--feature-name',
                        help='feature name to use to enable ligation, try "calt" for always-on',
                        type=str, default="dgsp")
    parser.add_argument('--monospace',
                        help='squish all numbers, including decimals and ones less than 4 digits, use with --squish flag',
                        default=False, action='store_true')
    parser.add_argument('--gap-size', help='size of space for thousand separator, try 300 or ","', type=str, default=",")
    parser.add_argument('--squish', help='horizontal scale to apply to the digits to maybe make them more readable when shifted', type=float, default=1.0)
    parser.add_argument('--squishy', help='vertical scale to apply to the digits to balance horizontal squish', type=float, default=1.0)
    parser.add_argument('--squish-all',
                        help='squish all numbers, including decimals and ones less than 4 digits, use with --squish flag',
                        default=False, action='store_true')
    parser.add_argument('--debug-annotate',
                        help='annotate glyph copies with debug digits',
                        default=False, action='store_true')
    args = parser.parse_args(argv)

    return patch_fonts(**vars(args))


main(sys.argv[1:])
