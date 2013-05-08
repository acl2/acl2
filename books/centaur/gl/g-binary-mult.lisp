

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

(defun g-binary-*-of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (equal xrd '(t))
             (equal yrd '(t))
             (equal xid '(t))
             (equal yid '(t)))
        (let* ((rprod (+-ss nil (*-ss xrn yrn)
                            (unary-minus-s
                             (*-ss xin yin))))
               (iprod (+-ss nil (*-ss xrn yin)
                            (*-ss xin yrn))))
          (mk-g-number
           (if (boolean-listp rprod) (v2i rprod) rprod)
           1
           (if (boolean-listp iprod) (v2i iprod) iprod)))
      (g-apply 'binary-* (gl-list x y)))))

(in-theory (disable (g-binary-*-of-numbers)))

(local
 (progn
   ;; (defthm gobjectp-g-binary-*-of-numbers
   ;;   (implies (and (gobjectp x)
   ;;                 (general-numberp x)
   ;;                 (gobjectp y)
   ;;                 (general-numberp y))
   ;;            (gobjectp (g-binary-*-of-numbers x y)))
   ;;   :hints(("Goal" :in-theory (disable general-numberp
   ;;                                      general-number-components))))

   (include-book "arithmetic/top-with-meta" :dir :system)

   (defthm *-complex
     (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d))
              (equal (* (complex a b) (complex c d))
                     (complex (- (* a c) (* b d))
                              (+ (* a d) (* b c)))))
     :hints (("goal" :use ((:instance complex-definition (x a) (y b))
                           (:instance complex-definition (x c) (y d))
                           (:instance complex-definition
                                      (x (- (* a c) (* b d)))
                                      (y (+ (* a d) (* b c)))))
              :in-theory (disable equal-complexes-rw))))

   (defthm g-binary-*-of-numbers-correct
     (implies (and (general-numberp x)
                   (general-numberp y))
              (equal (eval-g-base (g-binary-*-of-numbers x y) env)
                     (* (eval-g-base x env)
                        (eval-g-base y env))))
     :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                      (general-numberp
                                       general-number-components))
              :do-not-induct t)))))

(in-theory (disable g-binary-*-of-numbers))

(def-g-binary-op binary-*
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (g-binary-*-of-numbers x-num y-num)))

(local (defthmd general-concretep-atom
         (implies (and (not (consp x)))
                  (general-concretep x))
         :hints(("Goal" :in-theory (enable general-concretep-def
                                           gobjectp-def)))
         :rule-classes ((:rewrite :backchain-limit-lst (0)))))

;; (def-gobjectp-thm binary-*
;;   :hints `(("goal" :in-theory (e/d* (general-concretep-atom)
;;                                     ((:definition ,gfn)
;;                                      (force)
;;                                      general-concretep-def
;;                                      hyp-fix
;;                                      gobj-fix-when-not-gobjectp
;;                                      gobj-fix-when-gobjectp
;;                                      (:rules-of-class :type-prescription :here)
;;                                      (:ruleset gl-wrong-tag-rewrites)))
;;             :induct (,gfn x y hyp clk)
;;             :do-not-induct t
;;             :expand ((,gfn x y hyp clk)
;;                      (gobjectp (+ (gobj-fix x) (gobj-fix y)))))))


(verify-g-guards
 binary-*
 :hints `(("goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))




(local (defthm *-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (* x y)
                              (* 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (* x y)
                              (* x 0))))))



(def-g-correct-thm binary-* eval-g-base
  :hints
  `(("goal" :in-theory (e/d* (general-concretep-atom
                              not-general-numberp-not-acl2-numberp
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
                              v2n-is-v2i-when-sign-nil
                              general-concretep-def
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)))
     :induct (,gfn x y hyp clk)
     :do-not-induct t
     :expand ((,gfn x y hyp clk)))
;;     '(:use ((:instance possibilities-for-x)
;;             (:instance possibilities-for-x (x y))))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))
