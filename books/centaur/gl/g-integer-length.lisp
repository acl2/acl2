
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

;; (defthm true-listp-of-bfr-integer-length-s1
;;   (true-listp (mv-nth 1 (bfr-integer-length-s1 offset x)))
;;   :hints(("Goal" :in-theory (enable bfr-integer-length-s1)))
;;   :rule-classes :type-prescription)

;; (defthm true-listp-of-bfr-integer-length-s
;;   (true-listp (bfr-integer-length-s x))
;;   :hints(("Goal" :in-theory (enable bfr-integer-length-s)))
;;   :rule-classes :type-prescription)
 

(def-g-fn integer-length
  `(let ((x i))
     (if (atom x)
         (ec-call (integer-length x))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              (g-apply 'integer-length (gl-list x))
            (g-if test
                  (,gfn then hyp clk)
                  (,gfn else hyp clk))))
         ((g-apply & &)
          (g-apply 'integer-length (gl-list x)))
         ((g-var &)
          (g-apply 'integer-length (gl-list x)))
         ((g-boolean &) 0)
         ((g-concrete obj) (ec-call (integer-length obj)))
         ((g-number num)
          (mv-let (arn ard ain aid)
            (break-g-number num)
            (g-if (mk-g-boolean (hyp-fix (bfr-or (bfr-=-uu aid nil)
                                               (bfr-=-ss ain nil)) hyp))
                  (g-if (equal ard '(t))
                        (let ((res (rlist-fix (bfr-integer-length-s arn))))
                          (mk-g-number res 1 0 1))
                        (g-apply 'integer-length (gl-list x)))
                  0)))
         (& 0)))))

;; (local (defthm gobjectp-integer-length
;;          (gobjectp (integer-length a))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (local (defthm gobjectp-equal
;;          (gobjectp (equal a b))
;;          :hints(("Goal" :in-theory (enable gobjectp-def
;;                                            g-keyword-symbolp-def)))))

;; (def-gobjectp-thm integer-length
;;   :hints `(("Goal" :in-theory (e/d ()
;;                                  ((:definition ,gfn)))
;;           :induct (,gfn i hyp clk)
;;           :expand ((,gfn i hyp clk)))))

(verify-g-guards
 integer-length
 :hints `(("Goal" :in-theory (disable ,gfn))))



(local (defthm non-integerp-integer-length
         (implies (not (integerp x))
                  (equal (integer-length x) 0))
         :rule-classes ((:rewrite :backchain-limit-lst 1))))

(local (defthm eval-g-base-booleanp
         (implies (booleanp x)
                  (equal (eval-g-base x env) x))
         :hints(("Goal" :in-theory (enable eval-g-base booleanp)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm general-concrete-obj-integer
         (implies (integerp x)
                  (equal (general-concrete-obj x) x))
         :hints(("Goal" :in-theory (enable general-concrete-obj)))))

(local (defthm eval-g-base-integer
         (implies (integerp x)
                  (equal (eval-g-base x env) x))
         :hints(("Goal" :in-theory (enable eval-g-base)))))

(def-g-correct-thm integer-length eval-g-base
  :hints `(("Goal" :in-theory (e/d (components-to-number-alt-def)
                                   ((:definition ,gfn)
                                    general-concretep-def
                                    eval-g-base-alt-def
                                    integer-length))
            :induct (,gfn i hyp clk)
            :expand ((,gfn i hyp clk)))
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base (eval-g-base i env)))))))
