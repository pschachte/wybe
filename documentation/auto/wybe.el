(TeX-add-style-hook
 "wybe"
 (lambda ()
   (add-to-list 'LaTeX-verbatim-environments-local "VerbatimOut")
   (add-to-list 'LaTeX-verbatim-environments-local "SaveVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb*")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "a4wide"
    "xspace"
    "fancyvrb")
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
    "sec:Lexical structure"
    "sec:Syntax"
    "sec:Statements and expressions"
    "sec:Dataflow"
    "sec:Mode overloading"
    "sec:Defining functions and procedures"
    "sec:Functions are procedures"
    "sec:Tests"
    "sec:Implied modes"
    "sec:Selection and iteration statements"
    "sec:Modules"
    "sec:Exports"
    "sec:Imports"
    "sec:Submodules"
    "sec:Top level statements"
    "sec:Visibilty"
    "sec:Types"
    "sec:Functions and procedures"
    "sec:Resources"
    "sec:The Expression Problem"
    "sec:Foreign interface"
    "sec:Code Transformation"))
 :latex)

