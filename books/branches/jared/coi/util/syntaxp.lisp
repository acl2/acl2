#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

;; A very useful syntaxp hyp .. seems to work better than
;; loop-stopper in certain cases (?).

;; ie:
;; (implies
;;  (syntaxp (smaller-term rhs lhs))
;;  (equal (foo lhs) (foo rhs)))

(defun smaller-term (x y)
  (declare (xargs :mode :program))
  (not (term-order y x)))
