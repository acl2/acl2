; Utilities dealing with strings
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;Note that concatenate is a macro in ACL2 but a function in Raw Lisp.  If
;called from a guard-verified logic mode function, or from a program mode
;function, this should be fast.

(defmacro n-string-append (&rest strings)
  `(concatenate 'string ,@strings))

;; (DEFMACRO n-string-append
;;   (X Y &REST RST)
;;   (XXXJOIN 'string-append
;;            (CONS X (CONS Y RST))))

;; See also books/centaur/clex/example.lisp
(defun newline-string ()
  (declare (xargs :guard t))
  "\
")
