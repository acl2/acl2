; Recognizer for a unary lambda
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/pseudo-lambdap" :dir :system) ;reduce?

;; Recognize a unary lambda (not a lambda application).  Example: (lambda (x y) (+ x y))
;; todo: check that all vars mentioned in farg2 are in farg1?
;; todo: add pseudo to the name?
(defun unary-lambdap (x)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable PSEUDO-LAMBDAP))))) ;todo
  (and (pseudo-lambdap x)
       (= 1 (len (lambda-formals x))) ;exactly one argument
       ))
