# -*- coding: utf-8 -*-
"""Apply standard Chinese academic Word styling to pandoc-generated .docx.

- A4 page, margins: top/bottom 2.54cm, left/right 3.17cm
- Body: SimSun (宋体) + Times New Roman, 12pt (小四)
- Headings / Title: SimHei (黑体) + Times New Roman, black, bold
- Table / Caption: SimSun, 10.5pt (五号)

Usage: python style_docx_zh.py file1.docx [file2.docx ...]
In-place. Requires python-docx >= 1.0.
"""
import sys
from docx import Document
from docx.shared import Pt, Cm, Mm, RGBColor
from docx.oxml.ns import qn

BODY = "宋体"
HEAD = "黑体"
LATIN = "Times New Roman"


def set_font(style, east, size_pt, bold=None, color_black=False):
    try:
        st = style
    except KeyError:
        return
    st.font.name = LATIN
    st.font.size = Pt(size_pt)
    if bold is not None:
        st.font.bold = bold
    if color_black:
        st.font.color.rgb = RGBColor(0, 0, 0)
    rpr = st.element.get_or_add_rPr()
    rfonts = rpr.get_or_add_rFonts()
    rfonts.set(qn("w:eastAsia"), east)
    rfonts.set(qn("w:ascii"), LATIN)
    rfonts.set(qn("w:hAnsi"), LATIN)


def style_document(path):
    doc = Document(path)
    for sec in doc.sections:
        sec.page_width = Mm(210)
        sec.page_height = Mm(297)
        sec.top_margin = Cm(2.54)
        sec.bottom_margin = Cm(2.54)
        sec.left_margin = Cm(3.17)
        sec.right_margin = Cm(3.17)

    names = {
        "Normal": (BODY, 12.0, None, False),
        "First Paragraph": (BODY, 12.0, None, False),
        "Body Text": (BODY, 12.0, None, False),
        "Compact": (BODY, 12.0, None, False),
        "Title": (HEAD, 16.0, True, True),
        "Subtitle": (HEAD, 14.0, False, True),
        "Heading 1": (HEAD, 15.0, True, True),
        "Heading 2": (HEAD, 13.5, True, True),
        "Heading 3": (HEAD, 12.5, True, True),
        "Heading 4": (HEAD, 12.0, True, True),
        "Heading 5": (HEAD, 12.0, True, True),
        "Heading 6": (HEAD, 12.0, True, True),
        "Table": (BODY, 10.5, None, False),
        "Table Caption": (BODY, 10.5, True, False),
        "Caption": (BODY, 10.5, None, False),
        "Source Code": (BODY, 9.0, None, False),
        "Verbatim Char": (BODY, 9.0, None, False),
        "Block Text": (BODY, 12.0, None, False),
    }
    for name, (east, size, bold, black) in names.items():
        try:
            st = doc.styles[name]
        except KeyError:
            continue
        set_font(st, east, size, bold, black)

    doc.save(path)
    print("styled:", path)


if __name__ == "__main__":
    for p in sys.argv[1:]:
        style_document(p)
