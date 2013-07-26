

(in-package "GL")

; (include-book "g-if")
(include-book "g-primitives-help")
(include-book "eval-g-base")
(include-book "gtypes")
(local (include-book "gobjectp-thms"))

(def-g-fn hide 'x)

;; (def-gobjectp-thm hide)

(local (defthm hide-open
         (equal (hide x) x)
         :hints (("Goal" :expand ((:free (x) (hide x)))))))

(verify-g-guards hide)

(def-gobj-dependency-thm hide
  :hints `(("goal" 
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm hide eval-g-base
  :hints `(("Goal" :in-theory '(hide-open ,gfn))))
