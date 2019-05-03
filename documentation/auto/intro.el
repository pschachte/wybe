(TeX-add-style-hook
 "intro"
 (lambda ()
   (add-to-list 'LaTeX-verbatim-environments-local "VerbatimOut")
   (add-to-list 'LaTeX-verbatim-environments-local "SaveVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "a4wide"
    "xspace"
    "fancyvrb"
    "color"
    "hyperref")
   (TeX-add-symbols
    '("tuple" 1)
    '("possible" 1)
    '("tbi" 1)
    '("nyi" 1)
    "lang"
    "Lang"
    "ie"
    "eg"
    "Ie"
    "Eg"
    "etc")
   (LaTeX-add-labels
    "Compiling"
    "Variables"
    "Calling"
    "Procedures"
    "Control"
    "Conditional"
    "Loops"
    "Modules"
    "Types"
    "Tests"
    "Resources"
    "Foreign"
    "Library"
    "Contributors"))
 :latex)

