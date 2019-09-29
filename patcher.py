# Based on https://github.com/powerline/fontpatcher/blob/develop/scripts/powerline-fontpatcher
# Used under the MIT license

import argparse
import sys
import re
import os.path

from itertools import chain

try:
    import fontforge
    import psMat
except ImportError:
    sys.stderr.write('The required FontForge modules could not be loaded.\n\n')
    sys.stderr.write('You need FontForge with Python bindings for this script to work.\n')
    sys.exit(1)


def get_argparser(ArgumentParser=argparse.ArgumentParser):
    parser = ArgumentParser(
        description=('Font patcher for Numderline. '
                     'Requires FontForge with Python bindings. '
                     'Stores the patched font as a new, renamed font file by default.')
    )
    parser.add_argument('target_fonts', help='font files to patch', metavar='font',
                        nargs='+', type=argparse.FileType('rb'))
    parser.add_argument('--no-rename',
                        help='don\'t add " with Numderline" to the font name',
                        default=True, action='store_false', dest='rename_font')
    return parser


FONT_NAME_RE = re.compile(r'^([^-]*)(?:(-.*))?$')

def gen_feature(digit_names):
    feature = """
languagesystem DFLT dflt;
languagesystem latn dflt;
languagesystem cyrl dflt;
languagesystem grek dflt;
languagesystem kana dflt;
@digits=[{digit_names}];

feature calt {{
  sub two three by nine;
}} calt;
"""[1:]
    feature = feature.format(digit_names=' '.join(digit_names))
    with open('mods.fea', 'w') as f:
        f.write(feature)


def patch_one_font(target_font, rename_font=True):
    target_font_em_original = target_font.em
    target_font.em = 2048
    target_font.encoding = 'ISO10646'

    # Rename font
    if rename_font:
        target_font.familyname += ' with Numderline'
        target_font.fullname += ' with Numderline'
        fontname, style = FONT_NAME_RE.match(target_font.fontname).groups()
        target_font.fontname = fontname + 'WithNumderline'
        if style is not None:
            target_font.fontname += style
        target_font.appendSFNTName(
            'English (US)', 'Preferred Family', target_font.familyname)
        target_font.appendSFNTName(
            'English (US)', 'Compatible Full', target_font.fullname)

    target_bb = [0, 0, 0, 0]
    target_font_width = 0

    # Find the biggest char width and height in the Latin-1 extended range and
    # the box drawing range This isn't ideal, but it works fairly well - some
    # fonts may need tuning after patching.
    for cp in chain(range(0x00, 0x17f), range(0x2500, 0x2600)):
        try:
            bbox = target_font[cp].boundingBox()
        except TypeError:
            continue
        if not target_font_width:
            target_font_width = target_font[cp].width
        if bbox[0] < target_bb[0]:
            target_bb[0] = bbox[0]
        if bbox[1] < target_bb[1]:
            target_bb[1] = bbox[1]
        if bbox[2] > target_bb[2]:
            target_bb[2] = bbox[2]
        if bbox[3] > target_bb[3]:
            target_bb[3] = bbox[3]

    # Find source and target size difference for scaling
    # x_ratio = (target_bb[2] - target_bb[0]) / (source_bb[2] - source_bb[0])
    # y_ratio = (target_bb[3] - target_bb[1]) / (source_bb[3] - source_bb[1])
    # scale = psMat.scale(x_ratio, y_ratio)

    # Find source and target midpoints for translating
    # x_diff = target_bb[0] - source_bb[0]
    # y_diff = target_bb[1] - source_bb[1]
    # translate = psMat.translate(x_diff, y_diff)
    # transform = psMat.compose(scale, translate)

    # # Create new glyphs from symbol font
    # for source_glyph in source_font.glyphs():
    #     if source_glyph == source_font['block']:
    #         # Skip the symbol font block glyph
    #         continue

    #     # Select and copy symbol from its encoding point
    #     source_font.selection.select(source_glyph.encoding)
    #     source_font.copy()

    #     # Select and paste symbol to its unicode code point
    #     target_font.selection.select(source_glyph.unicode)
    #     target_font.paste()

    #     # Transform the glyph
    #     target_font.transform(transform)

    #     # Reset the font's glyph width so it's still considered monospaced
    #     target_font[source_glyph.unicode].width = target_font_width

    target_font.em = target_font_em_original

    # FIXME: Menlo and Meslo font do have these substitutes, but U+FB01 and
    #        U+FB02 still do not show up for fi and fl.
    # target_font[0xFB01].removePosSub('*')  # fi ligature
    # target_font[0xFB02].removePosSub('*')  # fl ligature

    digit_names = [target_font[code].glyphname for code in range(ord('0'),ord('9')+1)]
    print(digit_names)
    gen_feature(digit_names)
    target_font.mergeFeature('mods.fea')

    # for glyph in target_font:
    #     print(glyph)

    # Generate patched font
    # extension = os.path.splitext(target_font.path)[1]
    # if extension.lower() not in ['.ttf', '.otf']:
    #     # Default to OpenType if input is not TrueType/OpenType
    #     extension = '.otf'
    extension = '.otf'
    target_font.generate('out/{0}{1}'.format(target_font.fullname, extension))


def patch_fonts(target_files, rename_font=True):
    for target_file in target_files:
        target_font = fontforge.open(target_file.name)
        try:
            patch_one_font(target_font, rename_font)
        finally:
            target_font.close()
    return 0


def main(argv):
    args = get_argparser().parse_args(argv)
    return patch_fonts(args.target_fonts, args.rename_font)


raise SystemExit(main(sys.argv[1:]))
