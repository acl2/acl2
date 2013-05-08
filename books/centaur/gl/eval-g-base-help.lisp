
(in-package "GL")

(include-book "eval-g-base")

(include-book "gify-clause-proc")

(include-book "general-object-thms")

(include-book "tools/def-functional-instance" :dir :system)





(acl2::def-functional-instance
 eval-g-base-alt-def
 generic-geval-alt-def
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base))
 :hints ('(:do-not-induct
           t
           :expand ((eval-g-base x env))))
 :rule-classes ((:definition :clique (eval-g-base))))


(acl2::def-functional-instance
 mk-g-boolean-correct-for-eval-g-base
 mk-g-boolean-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))



(acl2::def-functional-instance
 gtests-obj-correct-for-eval-g-base
 gtests-obj-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 gtests-nonnil-correct-for-eval-g-base
 gtests-nonnil-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(local
 (progn

   ;; These should only be necessary to prove the meta rules for g-if.

   (acl2::def-functional-instance
    mk-g-ite-correct-for-eval-g-base
    mk-g-ite-correct
    ((apply-stub eval-g-base-apply)
     (generic-geval-apply eval-g-base-apply)
     (generic-geval eval-g-base)))


   (acl2::def-functional-instance
    gobj-ite-merge-correct-for-eval-g-base
    gobj-ite-merge-correct
    ((apply-stub eval-g-base-apply)
     (generic-geval-apply eval-g-base-apply)
     (generic-geval eval-g-base)))))

(acl2::def-functional-instance
 eval-g-base-g-apply
 generic-geval-g-apply
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 general-consp-car-correct-for-eval-g-base
 general-consp-car-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 general-consp-cdr-correct-for-eval-g-base
 general-consp-cdr-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(in-theory (disable general-consp-car-correct-for-eval-g-base
                    general-consp-cdr-correct-for-eval-g-base))

(acl2::def-functional-instance
 eval-g-base-cons
 generic-geval-cons
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 eval-g-base-non-cons
 generic-geval-non-cons
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(in-theory (disable eval-g-base-non-cons))

;; (acl2::def-functional-instance
;;  eval-g-base-gobj-fix
;;  generic-geval-gobj-fix
;;  ((apply-stub eval-g-base-apply)
;;   (generic-geval-apply eval-g-base-apply)
;;   (generic-geval eval-g-base)))

(acl2::def-functional-instance
 general-concrete-obj-when-consp-for-eval-g-base
 general-concrete-obj-when-consp
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 not-general-numberp-not-acl2-numberp-for-eval-g-base
 not-general-numberp-not-acl2-numberp
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 mk-g-number-correct-for-eval-g-base
 mk-g-number-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 mk-g-concrete-correct-for-eval-g-base
 mk-g-concrete-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 g-concrete-quote-correct-for-eval-g-base
 g-concrete-quote-correct
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))

(acl2::def-functional-instance
 eval-g-base-of-gl-cons
 generic-geval-gl-cons
 ((apply-stub eval-g-base-apply)
  (generic-geval-apply eval-g-base-apply)
  (generic-geval eval-g-base)))





(def-geval-meta eval-g-base evgb-ev evgb-ev-lst)
