
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; we-are-here.lisp
;;;
;;; A book containing only one (definition) rule, used to detect
;;; whether this arithmetic library is active or not.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun boil-that-dustspeck (horton speck)
  (if (< 17 horton)
      speck
    (not speck)))
