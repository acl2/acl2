

(in-package "GL")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))

(defun g-rem-of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (eq (=-uu xrd '(t)) t)
             (eq (=-uu yrd '(t)) t)
             (eq (bfr-or (=-ss xin nil)
                       (=-uu xid nil)) t)
             (eq (bfr-or (=-ss yin nil)
                       (=-uu yid nil)) t))
        (mk-g-number (rlist-fix (rem-ss xrn yrn)))
      (g-apply 'rem (gl-list x y)))))

(in-theory (disable (g-rem-of-numbers)))


(local (include-book "arithmetic/top-with-meta" :dir :system))

;; (local (defthm not-integerp-rem-ss
;;          (implies (and (bfr-listp a) (bfr-listp b))
;;                   (not (integerp (rem-ss a b))))
;;          :hints (("goal" :use ((:instance bfr-listp-rem-ss))
;;                   :in-theory (e/d (bfr-listp) (bfr-listp-rem-ss))))))

(local (defthm rationalp-rem
         (implies (and (integerp x) (integerp y))
                  (rationalp (rem x y)))))

(local (add-bfr-fn-pat =-uu))
(local (add-bfr-fn-pat =-ss))

(local
 (defthm g-rem-of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-rem-of-numbers x y) env)
                   (rem (eval-g-base x env)
                          (eval-g-base y env))))
   :hints (("goal" :in-theory
            (e/d* ((:ruleset general-object-possibilities))
                  (general-numberp
                   general-number-components
                   rem))
            :do-not-induct t)
           (bfr-reasoning))))

(in-theory (disable g-rem-of-numbers))




(def-g-binary-op rem
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (g-rem-of-numbers x-num y-num)))

(verify-g-guards
 rem
 :hints `(("goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(local (defthm rem-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (rem x y) (rem 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (rem x y) (rem x 0))))))

(def-g-correct-thm rem eval-g-base
  :hints
  `(("goal" :in-theory (e/d* (general-concretep-atom
                              (:ruleset general-object-possibilities))
                             ((:definition ,gfn)
                              general-numberp-eval-to-numberp
                              general-boolean-value-correct
                              bool-cond-itep-eval
                              general-consp-car-correct-for-eval-g-base
                              general-consp-cdr-correct-for-eval-g-base
                              boolean-listp
                              components-to-number-alt-def
                              member-equal
                              general-number-components-ev
                              general-concretep-def
                              general-concretep-def
                              rem floor
                              hons-assoc-equal
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)))
     :induct (,gfn x y hyp clk)
     :do-not-induct t
     :expand ((,gfn x y hyp clk)))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))

