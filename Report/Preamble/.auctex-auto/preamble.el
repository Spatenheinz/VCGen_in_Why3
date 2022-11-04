(TeX-add-style-hook
 "preamble"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("Preamble/ku-frontpage" "english" "science" "titlepage") ("appendix" "toc" "page") ("cleveref" "noabbrev" "capitalise") ("biblatex" "backend=biber" "dateabbrev=false")))
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "SaveVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "VerbatimOut")
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb*")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "inputenc"
    "latexsym"
    "amssymb"
    "amsmath"
    "svg"
    "subfig"
    "Preamble/ku-frontpage"
    "float"
    "caption"
    "appendix"
    "fancyvrb"
    "url"
    "tabularx"
    "booktabs"
    "titlesec"
    "semantic"
    "stmaryrd"
    "hyperref"
    "cleveref"
    "multirow"
    "longtable"
    "biblatex"
    "csquotes"
    "syntax"
    "listings"
    "xcolor")
   (TeX-add-symbols
    '("subst" 3)
    '("hoarePQ" 1)
    '("hoare" 3)
    '("judges" 2)
    '("judgeb" 2)
    '("judgea" 2)
    '("judge" 2)
    '("lra" 1)
    "phantomsection"
    "listofillustrations"
    "summaryname")
   (LaTeX-add-environments
    "changemargin"
    "Abstract")
   (LaTeX-add-bibliographies
    "references")
   (LaTeX-add-listings-lstdefinestyles
    "mystyle")
   (LaTeX-add-xcolor-definecolors
    "codegreen"
    "codegray"
    "codepurple"
    "backcolour"))
 :latex)

