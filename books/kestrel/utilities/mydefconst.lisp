; A tool to define a constant and treat its printing specially
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Compare to books/kestrel/utilities/untranslate-preprocessing.lisp.

;; TODO: Clean up and perhaps rename this book

;BBOZO we should avoid the evisc-table when the value of form is nil - how do we do that?
(defmacro mydefconst-non-nil (name form)
  `(progn (defconst ,name ,form)
          (table evisc-table ,name
                 ;;note the vertical bars - symbol-name loses them, so we add them back
                 ;;a little gross, because now even normal symbols will print with |
                 (concatenate 'string "#.|" (symbol-name ',name) "|"))))

;ex: (MAKE-EVENT (cons 'DEFCONST (cons '*FOO* (cons (+ 3 4) NIL))))

(defun mydefconst-fn (name form)
  `(MAKE-EVENT (if (equal ,form nil)
                   (cons 'DEFCONST (cons ',name (cons (list 'quote ,form) NIL)))
                 (cons 'myDEFCONST-non-nil (cons ',name (cons (list 'quote ,form) NIL))))))

(defmacro mydefconst (name form ;&optional doc
                            )
  (mydefconst-fn name form ;doc
                  ))
