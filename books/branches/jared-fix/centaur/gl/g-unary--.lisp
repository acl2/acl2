
(in-package "GL")

(set-inhibit-warnings "theory")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))


(def-g-fn unary--
  `(if (atom x)
       (- (fix x))
     (pattern-match x
       ((g-ite test then else)
        (if (zp clk)
            (g-apply 'unary-- (gl-list x))
          (g-if test
                (,gfn then hyp clk)
                (,gfn else hyp clk))))
       ((g-apply & &)
        (g-apply 'unary-- (gl-list x)))
       ((g-concrete obj)
        (- (fix obj)))
       ((g-var &)
        (g-apply 'unary-- (gl-list x)))
       ((g-boolean &) 0)
       ((g-number num)
        (mv-let (rn rd in id)
          (break-g-number num)
          (mk-g-number (bfr-unary-minus-s rn)
                       (rlist-fix rd)
                       (bfr-unary-minus-s in)
                       (rlist-fix id))))
       (& 0))))

;; (def-gobjectp-thm unary--
;;   :hints `(("Goal" :in-theory (e/d () ((:definition ,gfn)))
;;             :induct (,gfn x hyp clk)
;;             :expand ((,gfn x hyp clk)
;;                      (:free (x) (gobjectp (- x)))))))

(verify-g-guards
 unary--
 :hints `(("Goal" :in-theory (disable ,gfn))))


(local (include-book "arithmetic/top-with-meta" :dir :system))


(local
 (defthm minus-of-non-acl2-number
   (implies (not (acl2-numberp x))
            (equal (- x) (- 0)))))

(local
 (defthm minus-of-complex
   (implies (and (rationalp a) (rationalp b))
            (equal (- (complex a b))
                   (complex (- a) (- b))))
   :hints (("goal" :use ((:instance complex-definition
                                    (x a) (y b))
                         (:instance complex-definition
                                    (x (- a)) (y (- b))))
            :in-theory (disable equal-complexes-rw)))))

;; (local (defthm eval-g-base-atom
;;          (implies (and (not (consp x)) (gobjectp x))
;;                   (equal (eval-g-base x env) x))
;;          :hints(("Goal" :in-theory (enable eval-g-base)))))

;; (local (defthm gobjectp-number
;;          (implies (acl2-numberp x)
;;                   (gobjectp x))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (local
;;  (defthm not-integerp-break-g-number
;;    (implies (wf-g-numberp x)
;;             (and (not (integerp (mv-nth 0 (break-g-number x))))
;;                  (not (integerp (mv-nth 1 (break-g-number x))))
;;                  (not (integerp (mv-nth 2 (break-g-number x))))
;;                  (not (integerp (mv-nth 3 (break-g-number x))))))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp-simpler-def
;;                                      break-g-number bfr-listp)))))

(def-g-correct-thm unary-- eval-g-base
  :hints `(("Goal" :in-theory (e/d* (components-to-number-alt-def
                                     general-concrete-obj natp)
                                    ((:definition ,gfn)
                                     general-number-components-ev
                                     general-numberp-eval-to-numberp))
            :induct (,gfn x hyp clk)
            :do-not-induct t
            :expand ((,gfn x hyp clk)
                     (:with eval-g-base (eval-g-base x env))))))
