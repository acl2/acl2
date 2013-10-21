(defmacro paco ()
 '(cond ((assoc-equal "PACO" (known-package-alist state))

         (in-package "PACO"))
        (t (er-progn (include-book ;; Newline to defeat dependency checker
                      "paco")
                     (comp t)
                     (value
                      (cw "~%~%Note:  For ptrace and faster output, :q and ~%~
                           (load \"raw.lisp\").~%~%"))
                     (in-package "PACO")))))
