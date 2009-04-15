#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "BAG")
(include-book "basic")
(include-book "find-index" :dir :lists)

;bzo where should this go?
(defthm find-index-of-cdr
  (implies (bag::unique key-names)
           (equal (list::find-index key (cdr key-names))
                  (if (list::memberp key (cdr key-names))
                      (+ -1 (list::find-index key key-names))
                    (len (cdr key-names)))))
  :hints (("Goal" :induct t
           :in-theory (enable list::find-index)
           :do-not '(generalize eliminate-destructors))))

(theory-invariant (incompatible (:rewrite FIND-INDEX-OF-CDR) (:definition find-index)))
