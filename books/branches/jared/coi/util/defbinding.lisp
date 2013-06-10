(in-package "ACL2")

;; This is useful if you ever wish to construct a binding hypothesis
;; from an equivalence relation.
;;
;; (implies
;;   (and
;;     (equiv-binding x (foo y))
;;     ..)
;;     )

(defmacro def::binding (equiv)
  `(defmacro ,(packn-pos (list equiv `-binding) equiv) (key term)
     (declare (type symbol key))
     `(,',equiv ,key (double-rewrite ,term))))
