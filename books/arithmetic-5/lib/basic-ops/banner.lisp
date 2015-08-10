; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; banner.lisp
;;;
;;; This file contains a message about how to enable non-linear
;;; arithmetic.  It is displayed upon including this library.  In
;;; order to avoid seeing the message twice, be sure that there is no
;;; compiled file for top.lisp.  The standard "make" procedure ensures
;;; this through top.acl2.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (prog2$
  (observation-cw
   'non-linear-arithmetic
   "To turn on non-linear arithmetic, execute :~|~%~Y02~|~%~
    or :~|~%~Y12~|~%~
    See the README for more about non-linear arithmetic and ~
    general information about using this library."
   '(set-default-hints '((nonlinearp-default-hint
                          stable-under-simplificationp
                          hist pspv)))
   '(set-default-hints '((nonlinearp-default-hint++
                          id stable-under-simplificationp
                          hist nil)))
   nil)
  '(value-triple nil))
 :check-expansion t)

