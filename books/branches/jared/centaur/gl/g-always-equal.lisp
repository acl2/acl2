

(in-package "GL")

(include-book "g-primitives-help")


(include-book "g-if")
(include-book "symbolic-arithmetic-fns")
(local (include-book "eval-g-base-help"))
(include-book "eval-g-base")
(local (include-book "hyp-fix-logic"))
(include-book "always-equal-prep")
(include-book "g-equal")

(def-g-fn acl2::always-equal
  ;; Once we've ruled out the case where they're both atoms, start by recurring
  ;; down to non-ITEs on both a and b:
  `(bfr-case :bdd (g-always-equal-core x y hyp clk)
             :aig (glr equal x y hyp clk)))



;; (def-gobjectp-thm acl2::always-equal
;;   :hints `(("Goal" :in-theory (e/d (booleanp-gobjectp)
;;                                    ((:definition ,gfn)
;;                                     g-always-equal-core
;;                                     general-boolean-value
;;                                     general-boolean-value-cases
;;                                     gobj-fix-when-not-gobjectp
;;                                     gobj-fix-when-gobjectp
;;                                     (:type-prescription booleanp)
;;                                     (:type-prescription gobj-fix)
;;                                     equal-of-booleans-rewrite))
;;             :expand ((,gfn x y hyp clk)))))

(verify-g-guards
   acl2::always-equal
   :hints `(("Goal" :in-theory (disable ,gfn))))






(def-g-correct-thm acl2::always-equal eval-g-base
  :hints `(("Goal" :in-theory (e/d (,gfn)
                                   (g-always-equal-core)))))

