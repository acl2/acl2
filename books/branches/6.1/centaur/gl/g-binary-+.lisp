
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

(defun g-binary-+-of-numbers (x y)
  (declare (xargs :guard (and (gobjectp x)
                              (general-numberp x)
                              (gobjectp y)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (equal xrd '(t))
             (equal yrd '(t))
             (equal xid '(t))
             (equal yid '(t)))
        (let* ((rsum (+-ss nil xrn yrn))
               (isum (+-ss nil xin yin)))
          (mk-g-number
           (if (boolean-listp rsum) (v2i rsum) rsum)
           1
           (if (boolean-listp isum) (v2i isum) isum)))
      (g-apply 'binary-+ (list x y)))))

(in-theory (disable (g-binary-+-of-numbers)))

(local
 (progn
   (defthm gobjectp-g-binary-+-of-numbers
     (implies (and (gobjectp x)
                   (general-numberp x)
                   (gobjectp y)
                   (general-numberp y))
              (gobjectp (g-binary-+-of-numbers x y)))
     :hints(("Goal" :in-theory (disable general-numberp
                                        general-number-components))))

   (defthm g-binary-+-of-numbers-correct
     (implies (and (gobjectp x)
                   (general-numberp x)
                   (gobjectp y)
                   (general-numberp y))
              (equal (eval-g-base (g-binary-+-of-numbers x y) env)
                     (+ (eval-g-base x env)
                        (eval-g-base y env))))
     :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                      (general-numberp
                                       general-number-components))
              :do-not-induct t)))))

(in-theory (disable g-binary-+-of-numbers))

(def-g-binary-op binary-+
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (g-binary-+-of-numbers x-num y-num)))



(def-gobjectp-thm binary-+
  :hints `(("goal" :in-theory (e/d* (general-concretep-atom)
                                    ((:definition ,gfn)
                                     (force)
                                     general-concretep-def
                                     hyp-fix
                                     gobj-fix-when-not-gobjectp
                                     gobj-fix-when-gobjectp
                                     (:rules-of-class :type-prescription :here)
                                     (:ruleset gl-wrong-tag-rewrites)))
            :induct (,gfn x y hyp clk)
            :do-not-induct t
            :expand ((,gfn x y hyp clk)
                     (gobjectp (+ (gobj-fix x) (gobj-fix y)))))))




(verify-g-guards
 binary-+
 :hints `(("goal" :in-theory (disable* ,gfn bfr-p-of-boolean
                                       (:rules-of-class :type-prescription
                                                        :here)
                                       (:ruleset gl-wrong-tag-rewrites)))))


(local (defthm +-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (+ x y)
                              (+ 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (+ x y)
                              (+ x 0))))))

(def-g-correct-thm binary-+ eval-g-base
  :hints
  `(("goal" :in-theory (e/d* (general-concretep-atom
                              (:ruleset general-object-possibilities))
                             ((:definition ,gfn)
                              i2v n2v v2i +-ss
                              tag-when-g-boolean-p
                              tag-when-g-apply-p
                              tag-when-g-concrete-p
                              tag-when-g-var-p
                              general-numberp-eval-to-numberp
                              general-boolean-value-correct
                              bool-cond-itep-eval
                              general-consp-car-correct-for-eval-g-base
                              general-consp-cdr-correct-for-eval-g-base
                              boolean-listp
                              components-to-number-alt-def
                              member-equal bfr-p-of-boolean
                              general-number-components-ev
                              general-concretep-def
                              v2n-is-v2i-when-sign-nil
                              general-concretep-def
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)))
     :induct (,gfn x y hyp clk)
     :do-not-induct t
     :expand ((,gfn x y hyp clk)))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))
