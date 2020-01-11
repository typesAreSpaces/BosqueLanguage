(TeX-add-style-hook
 "firstdraft"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("llncs" "runningheads")))
   (TeX-run-style-hooks
    "latex2e"
    "llncs"
    "llncs10"
    "graphicx")
   (LaTeX-add-bibliographies
    "bibliography/references"))
 :latex)

