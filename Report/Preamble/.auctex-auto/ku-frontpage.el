(TeX-add-style-hook
 "ku-frontpage"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("textpos" "absolute")))
   (TeX-run-style-hooks
    "babel"
    "eso-pic"
    "graphicx"
    "times"
    "ifthen"
    "textpos"
    "hyperref"
    "lettrine")
   (TeX-add-symbols
    '("kupdfsetup" 3)
    '("frontpageimage" 1)
    '("advisor" 1)
    '("subtitle" 1)
    '("assignment" 1)
    "KUSTYLE"
    "KULANG"
    "KUFACULTY"
    "KUCOLOR"
    "AUTHOR"
    "TITLE"
    "DATE"
    "ASSIGNMENT"
    "SUBTITLE"
    "ADVISOR"
    "FRONTPAGEIMAGE"
    "KUbold"
    "KUsemibold"
    "maketitle"))
 :latex)

