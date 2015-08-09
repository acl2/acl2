(in-package "ACL2")

#|

  conjunction.lisp
  ~~~~~~~~~~~~~~~~

In this book, we prove the theorems on conjunctive reductions of LTL
formula. In particular, we prove that if an ltl-formula f is the conjunction of
formuals f1 and f2, then the semantics of f with respect to a model m will be
the conjunction of semantics of f1 and f2 wrt m.

|#


(include-book "ltl")

(local
(defthm ltl-conjunction-reduction-1
  (implies (and (ltl-formulap f)
                (equal (len f) 3)
                (equal (second f) '&)
                (ltl-semantics (first f) m)
                (ltl-semantics (third f) m))
           (ltl-semantics f m))
  :hints (("Goal"
           :in-theory (disable compatible-ppath-p)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :cases ((compatible-ppath-p (ltl-semantics-witness
                                        f m) m)))))

)

(local
(defthm ltl-conjunction-reduction-2
  (implies (and (ltl-formulap f)
                (equal (len f) 3)
                (equal (second f) '&)
                (ltl-semantics f m))
           (ltl-semantics (first f) m))
   :hints (("Goal"
           :in-theory (disable compatible-ppath-p)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :cases ((compatible-ppath-p (ltl-semantics-witness (first f) m) m)))
          ("Subgoal 1"
           :in-theory (disable compatible-ppath-p ltl-semantics-necc
                               ltl-ppath-semantics-can-be-decomposed-over-conjunctions
                               ltl-semantics)
           :expand (ltl-semantics (first f) m)
           :use ((:instance ltl-semantics-necc
                            (ppath (ltl-semantics-witness (first f) m)))
                 (:instance
                  ltl-ppath-semantics-can-be-decomposed-over-conjunctions
                  (p (ltl-semantics-witness (first f) m)))))))
)

(local
(defthm ltl-conjunction-reduction-3
  (implies (and (ltl-formulap f)
                (equal (len f) 3)
                (equal (second f) '&)
                (ltl-semantics f m))
           (ltl-semantics (third f) m))
  :hints (("Goal"
           :in-theory (disable compatible-ppath-p)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :cases ((compatible-ppath-p (ltl-semantics-witness (third f) m) m)))
          ("Subgoal 1"
           :in-theory (disable compatible-ppath-p
                               ltl-semantics-necc
                               ltl-ppath-semantics-can-be-decomposed-over-conjunctions
                               ltl-semantics)
           :expand (ltl-semantics (third f) m)
           :use ((:instance ltl-semantics-necc
                            (ppath (ltl-semantics-witness (third f) m)))
                 (:instance
                  ltl-ppath-semantics-can-be-decomposed-over-conjunctions
                  (p (ltl-semantics-witness (third f) m)))))))
)

(local
(in-theory (disable ltl-semantics ltl-formulap
                    ltl-semantics-necc))
)

(DEFTHM ltl-semantics-is-decomposed-over-conjunction
  (implies (and (ltl-formulap f)
                (equal (len f) 3)
                (equal (second f) '&))
           (equal (ltl-semantics f m)
                  (and (ltl-semantics (first f) m)
                       (ltl-semantics (third f) m))))
  :hints (("Goal"
           :use ((:instance ltl-conjunction-reduction-1)
                 (:instance ltl-conjunction-reduction-2)
                 (:instance ltl-conjunction-reduction-3)))))
