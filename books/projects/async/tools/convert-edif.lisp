; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Warren Hunt for requesting these utilities.  See Lisp comments
; below for documentation.

(in-package "ACL2")

(defun convert-edif (in-file out-file state)

; Takes an edif expression in in-file and prints the corresponding ACL2
; s-expression to out-file.  The read of in-file is case-sensitive for symbols,
; so for example the symbol abc in in-file will appear as |abc| in out-file,
; and the symbol 11u may appear as 11\u.

  (declare (xargs :mode :program ; because of (er soft ...)
                  :stobjs state))
  (let ((ctx 'convert-edif))
    (mv-let (in-channel state)
      (open-input-channel in-file :object state)
      (cond
       ((null in-channel)
        (er soft ctx
            "Unable to open file ~x0 for input."
            in-file))
       (t
        (mv-let (eofp obj state)
          (read-object-with-case in-channel :preserve state)
          (pprogn
           (close-input-channel in-channel state)
           (cond
            (eofp (er soft ctx
                      "Unable to read an expression from file ~x0."
                      in-file))
            (t (mv-let (out-channel state)
                 (open-output-channel out-file :object state)
                 (cond
                  ((null out-channel)
                   (er soft ctx
                       "Unable to open file ~x0 for output."
                       out-file))
                  (t
                   (pprogn
                    (print-object$ obj out-channel state)
                    (close-output-channel out-channel state)
                    (value (list :converted-edif out-file)))))))))))))))

(defun print-edif (sexp-file edif-file state)

; This function is intended to be an inverse to convert-edif (defined above).
; Thus, symbols are printed without escaping them with |..| or \.

  (declare (xargs :mode :program ; because of (er soft ...)
                  :stobjs state))
  (let ((ctx 'print-edif))
    (mv-let (sexp-channel state)
      (open-input-channel sexp-file :object state)
      (cond
       ((null sexp-channel)
        (er soft ctx
            "Unable to open file ~x0 for input."
            sexp-file))
       (t
        (mv-let (eofp obj state)
          (read-object sexp-channel state)
          (pprogn
           (close-input-channel sexp-channel state)
           (cond
            (eofp (er soft ctx
                      "Unable to read an expression from file ~x0."
                      sexp-file))
            (t (mv-let (edif-channel state)
                 (open-output-channel edif-file :object state)
                 (cond
                  ((null edif-channel)
                   (er soft ctx
                       "Unable to open file ~x0 for output."
                       edif-file))
                  (t
                   (pprogn
                    (print-object$-preserving-case obj edif-channel state)
                    (close-output-channel edif-channel state)
                    (value (list :printed-edif edif-file)))))))))))))))
