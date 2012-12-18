
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
 

(defun g-logbitp-of-numbers (a b)
  (declare (xargs :guard (and (gobjectp a)
                              (general-numberp a)
                              (gobjectp b)
                              (general-numberp b))))
  (b* (((mv arn ard ain aid)
        (general-number-components a))
       ((mv brn brd bin bid)
        (general-number-components b))
       ((mv aintp aintp-known)
        (if (equal ard '(t))
            (mv (bfr-or (=-ss ain nil) (=-uu aid nil)) t)
          (mv nil nil)))
       ((mv bintp bintp-known)
        (if (equal brd '(t))
            (mv (bfr-or (=-ss bin nil) (=-uu bid nil)) t)
          (mv nil nil))))
    (if (and bintp-known aintp-known)
        (mk-g-boolean
         (logbitp-n2v 1
                      (bfr-ite-bss-fn (bfr-and
                                     aintp (bfr-not (s-sign arn)))
                                    arn nil)
                      (bfr-ite-bss-fn bintp brn nil)))
      (g-apply 'logbitp (list a b)))))

(in-theory (disable (g-logbitp-of-numbers)))

(local
 (defthm gobjectp-g-logbitp-of-numbers
   (implies (and (gobjectp a)
                 (general-numberp a)
                 (gobjectp b)
                 (general-numberp b))
            (gobjectp (g-logbitp-of-numbers a b)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm logbitp-when-not-integers
         (and (implies (not (natp a))
                       (equal (logbitp a b) (logbitp 0 b)))
              (implies (not (integerp b))
                       (equal (logbitp a b) (logbitp a 0))))
         :hints(("Goal" :in-theory (enable logbitp)))))

(local
 (defthm g-logbitp-of-numbers-correct
   (implies (and (gobjectp a)
                 (general-numberp a)
                 (gobjectp b)
                 (general-numberp b))
            (equal (eval-g-base (g-logbitp-of-numbers a b) env)
                   (logbitp (eval-g-base a env)
                            (eval-g-base b env))))
   :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                    (general-numberp
                                     general-number-components))
            :do-not-induct t))))

(in-theory (disable g-logbitp-of-numbers))

(def-g-binary-op logbitp
  (b* ((i-num (if (general-numberp i) i 0))
       (j-num (if (general-numberp j) j 0)))
    (g-logbitp-of-numbers i-num j-num)))

(def-gobjectp-thm logbitp
  :hints `(("Goal" :in-theory
            (e/d* (general-concretep-atom)
                  ((:definition ,gfn) (force)
                   (:rules-of-class :type-prescription :here)
                   (:ruleset gl-wrong-tag-rewrites)
                   general-concretep-def
                   gobj-fix-when-not-gobjectp
                   gobj-fix-when-gobjectp
                   equal-of-booleans-rewrite
                   (:ruleset gl-tag-rewrites)
                   mv-nth-cons-meta
                   bfr-ite-bss-fn))
            :induct (,gfn i j hyp clk)
            :expand ((,gfn i j hyp clk)))))

(verify-g-guards
 logbitp
 :hints `(("Goal" :in-theory
           (disable* ,gfn bfr-p-of-boolean
                     (:rules-of-class :type-prescription :here)
                     (:ruleset gl-wrong-tag-rewrites)))))


(local (defthm logbitp-when-not-numbers
         (and (implies (not (acl2-numberp a))
                       (equal (logbitp a b) (logbitp 0 b)))
              (implies (not (acl2-numberp b))
                       (equal (logbitp a b) (logbitp a 0))))
         :hints(("Goal" :in-theory (enable logbitp)))))

(def-g-correct-thm logbitp eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      tag-when-g-boolean-p
                                      tag-when-g-apply-p
                                      tag-when-g-concrete-p
                                      tag-when-g-var-p
                                      general-numberp-eval-to-numberp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      components-to-number-alt-def
                                      member-equal bfr-p-of-boolean
                                      general-number-components-ev
                                      general-concretep-def
                                      v2n-is-v2i-when-sign-nil
                                      general-concretep-def
                                      rationalp-implies-acl2-numberp
                                      hons-assoc-equal
                                      default-car default-cdr
                                      bfr-eval-list-consts
                                      mv-nth-cons-meta
                                      possibilities-for-x-5
                                      possibilities-for-x-3
                                      general-boolean-value-cases
                                      (:ruleset gl-wrong-tag-rewrites)
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription bfr-eval)))
             :induct (,gfn i j hyp clk)
             :expand ((,gfn i j hyp clk)))))
