

(in-package "GL")

; (include-book "g-if")
(include-book "g-primitives-help")
(include-book "eval-g-base")
(local (include-book "gobjectp-thms"))

(def-g-fn hide 'x)

(def-gobjectp-thm hide)

(local (defthm hide-open
         (equal (hide x) x)
         :hints (("Goal" :expand ((:free (x) (hide x)))))))

(verify-g-guards hide)

(local
 (defthm eval-g-base-gobj-fix
   (equal (eval-g-base (gobj-fix x) env)
          (eval-g-base x env))
   :hints(("Goal" :expand ((:with eval-g-base (eval-g-base x env))
                           (:with eval-g-base (eval-g-base (gobj-fix x) env)))))))

(def-g-correct-thm hide eval-g-base
  :hints `(("Goal" :in-theory '(hide-open ,gfn gobj-fix-when-gobjectp)))
  :final-hints `(("Goal" :expand ((:free (x) (hide x)))
                  :use ((:instance gl-thm::|ACL2::HIDE-CORRECT1|
                                   (x (gobj-fix x))
                                   (hyp (bfr-fix hyp))))
                  :in-theory (disable (force) gl-thm::|ACL2::HIDE-CORRECT1|))))
