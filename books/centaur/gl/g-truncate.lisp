
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

(defun g-truncate-of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (eq (bfr-=-uu xrd '(t)) t)
             (eq (bfr-=-uu yrd '(t)) t)
             (eq (bfr-or (bfr-=-ss xin nil)
                       (bfr-=-uu xid nil)) t)
             (eq (bfr-or (bfr-=-ss yin nil)
                       (bfr-=-uu yid nil)) t))
        (mk-g-number (rlist-fix (bfr-truncate-ss xrn yrn)))
      (g-apply 'truncate (gl-list x y)))))

(in-theory (disable (g-truncate-of-numbers)))

(local (include-book "arithmetic/top-with-meta" :dir :system))


(local (add-bfr-fn-pat bfr-=-uu))
(local (add-bfr-fn-pat bfr-=-ss))

(local
 (defthm g-truncate-of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-truncate-of-numbers x y) env)
                   (truncate (eval-g-base x env)
                          (eval-g-base y env))))
   :hints (("goal" :in-theory
            (e/d* ((:ruleset general-object-possibilities))
                  (general-numberp
                   general-number-components
                   truncate))
            :do-not-induct t)
           (bfr-reasoning))))

(in-theory (disable g-truncate-of-numbers))




(def-g-binary-op truncate
  (b* ((i-num (if (general-numberp i) i 0))
       (j-num (if (general-numberp j) j 0)))
    (g-truncate-of-numbers i-num j-num)))


(verify-g-guards
 truncate
 :hints `(("goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(local (defthm truncate-when-not-numberp
         (and (implies (not (acl2-numberp i))
                       (equal (truncate i j) (truncate 0 j)))
              (implies (not (acl2-numberp j))
                       (equal (truncate i j) (truncate i 0))))))

(def-g-correct-thm truncate eval-g-base
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
                              truncate
                              hons-assoc-equal
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)))
     :induct (,gfn i j hyp clk)
     :do-not-induct t
     :expand ((,gfn i j hyp clk)))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))


