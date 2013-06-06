
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

;; (include-book "univ-gl-eval")

(defun g-binary-+-of-numbers (x y)
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
        (let* ((rsum (+-ss nil xrn yrn))
               (isum (+-ss nil xin yin)))
          (mk-g-number
           (if (boolean-listp rsum) (v2i rsum) rsum)
           1
           (if (boolean-listp isum) (v2i isum) isum)))
      (g-apply 'binary-+ (gl-list x y)))))

(in-theory (disable (g-binary-+-of-numbers)))


(local (defthmd bfr-eval-list-when-boolean-listp
         (implies (boolean-listp x)
                  (equal (bfr-eval-list x env)
                         x))))

(local (defthm rewrite-v2i-of-boolean-list
         (implies (and (syntaxp (not (and (consp x)
                                          (eq (car x) 'bfr-eval-list))))
                       (bind-free '((env . (car env))) (env))
                       (boolean-listp x))
                  (equal (v2i x)
                         (v2i (bfr-eval-list x env))))
         :hints(("Goal" :in-theory (enable bfr-eval-list-when-boolean-listp)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm rewrite-v2n-of-boolean-list
         (implies (and (syntaxp (not (and (consp x)
                                          (eq (car x) 'bfr-eval-list))))
                       (bind-free '((env . (car env))) (env))
                       (boolean-listp x))
                  (equal (v2n x)
                         (v2n (bfr-eval-list x env))))
         :hints(("Goal" :in-theory (enable bfr-eval-list-when-boolean-listp)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(defthm bfr-eval-list-of-bfr-ite-bvv-fn-under-v2n
  (equal (v2n (bfr-eval-list (bfr-ite-bvv-fn c a b) env))
         (v2n (if (bfr-eval c env)
                  (bfr-eval-list a env)
                (bfr-eval-list b env))))
  :hints(("Goal" :in-theory (enable bfr-ite-bvv-fn v2n)
          :induct t)
         (bfr-reasoning)))


(local
 (defthm g-binary-+-of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-binary-+-of-numbers x y) env)
                   (+ (eval-g-base x env)
                      (eval-g-base y env))))
   :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                    (general-numberp
                                     general-number-components))
            :do-not-induct t))))

(in-theory (disable g-binary-+-of-numbers))

(def-g-binary-op binary-+
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (g-binary-+-of-numbers x-num y-num)))





(verify-g-guards
 binary-+
 :hints `(("goal" :in-theory (disable* ,gfn 
                                       (:rules-of-class :type-prescription
                                                        :here)))))


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
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)
                              (:type-prescription components-to-number-fn)))
     :induct (,gfn x y hyp clk)
     :do-not-induct t
     :expand ((,gfn x y hyp clk)))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))
