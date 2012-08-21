
(in-package "GL")

(set-inhibit-warnings "theory")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(local (include-book "eval-g-base-help"))
(include-book "eval-g-base")
; (include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "hyp-fix-logic"))

(local (defthm apply-base-of-equal
         (equal (apply-base 'equal (list x y))
                (equal x y))))

(local (defthm equal-of-components-to-number-fn
         (implies (and (integerp arn) (integerp ain)
                       (integerp brn) (integerp bin))
                  (equal (equal (components-to-number-fn
                                 arn 1 ain 1)
                                (components-to-number-fn
                                 brn 1 bin 1))
                         (and (equal arn brn)
                              (equal ain bin))))))


(local (in-theory (disable acl2-count)))

(local
 (encapsulate nil
   (local (include-book "arithmetic/top-with-meta" :dir :system))
   (defthm equal-of-components-to-number-fn2
     (implies (and (integerp arn) (natp ard)
                   (integerp brn) (natp brd)
                   (integerp ain) (integerp aid)
                   (integerp bin) (integerp bid)
                   (not (equal ard 0))
                   (not (equal brd 0))
                   (equal ard brd)
                   (not (equal arn brn)))
              (not (equal (components-to-number-fn
                           arn ard ain aid)
                          (components-to-number-fn
                           brn brd bin bid)))))

   (defthm equal-of-components-to-number-fn3
     (implies (and (integerp arn) (natp aid)
                   (integerp brn) (natp bid)
                   (integerp ain) (integerp ard)
                   (integerp bin) (integerp brd)
                   (not (equal aid 0))
                   (not (equal bid 0))
                   (equal aid bid)
                   (not (equal ain bin)))
              (not (equal (components-to-number-fn
                           arn ard ain aid)
                          (components-to-number-fn
                           brn brd bin bid)))))

   (defthm components-to-number-fn-normalize-zeros1
     (equal (components-to-number-fn rn 0 in id)
            (components-to-number-fn 0 1 in id)))

   (defthm components-to-number-fn-normalize-zeros2
     (equal (components-to-number-fn rn rd in 0)
            (components-to-number-fn rn rd 0 1)))

   (defthm components-to-number-fn-normalize-zeros3
     (implies (syntaxp (not (equal rd ''1)))
              (equal (components-to-number-fn 0 rd in id)
                     (components-to-number-fn 0 1 in id))))

   (defthm components-to-number-fn-normalize-zeros4
     (implies (syntaxp (not (equal id ''1)))
              (equal (components-to-number-fn rn rd 0 id)
                     (components-to-number-fn rn rd 0 1))))))

(defun equal-of-numbers (a b hyp)
  (declare (xargs :guard (and (gobjectp a)
                              (general-numberp a)
                              (gobjectp b)
                              (general-numberp b)
                              (bfr-p hyp))))
  (b* (((mv arn ard ain aid)
        (general-number-components a))
       ((mv brn brd bin bid)
        (general-number-components b)))
    (g-if (mk-g-boolean (bfr-and (=-uu ard brd)
                               (=-uu aid bid)))
          (mk-g-boolean (bfr-and (bfr-or (=-uu nil ard)
                                     (=-ss arn brn))
                               (bfr-or (=-uu nil aid)
                                     (=-ss ain bin))))
          (g-apply 'equal (list a b)))))

(local (defthm equal-of-numbers-gobjectp
         (implies (and (gobjectp a)
                       (general-numberp a)
                       (gobjectp b)
                       (general-numberp b)
                       (bfr-p hyp))
                  (gobjectp (equal-of-numbers a b hyp)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (defthm equal-of-numbers-correct
         (implies (and (gobjectp a)
                       (general-numberp a)
                       (gobjectp b)
                       (general-numberp b)
                       (bfr-p hyp)
                       (bfr-eval hyp (car env)))
                  (equal (eval-g-base (equal-of-numbers a b hyp) env)
                         (equal (eval-g-base a env)
                                (eval-g-base b env))))
         :hints(("Goal" :in-theory
                 (e/d* ((:ruleset general-object-possibilities)
                        boolean-list-bfr-eval-list))))))

(in-theory (Disable equal-of-numbers))

(def-g-fn equal
  ;; Once we've ruled out the case where they're both atoms, start by recurring
  ;; down to non-ITEs on both a and b:
  `(let ((a x) (b y))
     (cond ((and (general-concretep a) (general-concretep b))
            (hqual (general-concrete-obj a) (general-concrete-obj b)))
           ((zp clk)
            (g-apply 'equal (list a b)))
           (t (pattern-match a
                ((g-ite test then else)
                 (g-if test
                       (,gfn then b hyp clk)
                       (,gfn else b hyp clk)))
                (& (pattern-match b
                     ((g-ite test then else)
                      (g-if test
                            (,gfn a then hyp clk)
                            (,gfn a else hyp clk)))
                     ((g-var &)
                      (or (equal a b)
                          (g-apply 'equal (list a b))))
                     ((g-apply fn args)
                      (pattern-match a
                        ((g-apply !fn aargs)
                         (g-if (,gfn args aargs hyp clk)
                               t
                               (g-apply 'equal (list a b))))
                        (& (g-apply 'equal (list a b)))))
                     (& (pattern-match a
                          ((g-var &) (g-apply 'equal (list a b)))
                          ((g-apply & &) (g-apply 'equal (list a b)))
                          (& (cond
                              ((hqual a b) t)
                              ((general-booleanp a)
                               (if (general-booleanp b)
                                   (mk-g-boolean (bfr-iff (general-boolean-value a)
                                                        (general-boolean-value b)))
                                 nil))
                              ((general-numberp a)
                               (if (general-numberp b)
                                   (equal-of-numbers a b hyp)
                                 nil))
                              ((general-consp a)
                               (if (general-consp b)
                                   (g-if (,gfn (general-consp-car a)
                                               (general-consp-car b)
                                               hyp clk)
                                         (,gfn (general-consp-cdr a)
                                               (general-consp-cdr b)
                                               hyp clk)
                                         nil)
                                 nil))
                              (t nil))))))))))))



(def-gobjectp-thm equal
  :hints `(("Goal" :in-theory (e/d* ()
                                    ((:definition ,gfn)
                                     general-boolean-value
                                     general-boolean-value-cases
                                     gobjectp-def
                                     general-concretep-def
                                     gobj-fix-when-not-gobjectp
                                     gobj-fix-when-gobjectp
                                     hyp-fix
                                     booleanp-gobjectp
                                     equal-of-booleans-rewrite
                                     tag-when-g-number-p
                                     tag-when-g-boolean-p
                                     tag-when-g-concrete-p
                                     (:rules-of-class :type-prescription :here)
                                     (:ruleset gl-wrong-tag-rewrites)
                                     (:ruleset gl-tag-forward)))
            :induct (,gfn x y hyp clk)
            :expand ((,gfn x y hyp clk)
                     (,gfn x x hyp clk)))
           (and stable-under-simplificationp
                '(:in-theory (e/d* (booleanp-gobjectp)
                                    ((:definition ,gfn)
                                     general-boolean-value
                                     general-boolean-value-cases
                                     gobjectp-def
                                     general-concretep-def
                                     gobj-fix-when-not-gobjectp
                                     gobj-fix-when-gobjectp
                                     hyp-fix
                                     equal-of-booleans-rewrite
                                     tag-when-g-number-p
                                     tag-when-g-boolean-p
                                     tag-when-g-concrete-p
                                     (:rules-of-class :type-prescription :here)
                                     (:ruleset gl-wrong-tag-rewrites)
                                     (:ruleset gl-tag-forward)))))))

(encapsulate nil
  (local (in-theory (e/d* ()
                          (general-concretep-def
                           gobjectp-def
                           boolean-listp-bfr-listp
                           boolean-listp bfr-p-of-boolean
                           g-var-p-when-wrong-tag
                           g-ite-p-when-wrong-tag
                           g-apply-p-when-wrong-tag
                           tag-when-g-var-p
                           tag-when-g-apply-p
                           tag-when-g-ite-p
                           equal-of-booleans-rewrite
                           iff-implies-equal-not
                           (:type-prescription true-under-hyp)
                           (:type-prescription false-under-hyp)
                           (:type-prescription gobjectp)
                           (:type-prescription general-booleanp)
                           (:type-prescription general-numberp)
                           (:type-prescription g-ite-p)
                           (:type-prescription bfr-p)
                           (:type-prescription general-concretep)
                           (:type-prescription g-var-p)
                           (:type-prescription g-apply-p)
                           (:type-prescription =-uu)
                           hyp-fix-of-hyp-fixedp
                           (:meta mv-nth-cons-meta)
                           zp-open default-<-2 default-<-1
                           (:type-prescription zp)
                           (:type-prescription hyp-fix)
                           default-car default-cdr
                           tag-when-g-number-p
                           tag-when-g-concrete-p
                           tag-when-g-boolean-p
                           not
                           (:ruleset gl-type-forward-consp)
                           (:rules-of-class :type-prescription :here))
                          ((:type-prescription general-number-components)))))
  (verify-g-guards
   equal
   :hints `(("Goal" :in-theory (disable ,gfn)))))








(encapsulate nil

  (local
   (in-theory (e/d** (
                      possibilities-for-x-1
                      gl-thm::|GOBJECTP-COMMON-LISP::EQUAL|
                      
                      possibilities-for-x-2
                      possibilities-for-x-3
                      possibilities-for-x-4
                      possibilities-for-x-5
                      possibilities-for-x-6
                      possibilities-for-x-7
                      possibilities-for-x-8
                      possibilities-for-x-9

                      g-if-geval-meta-correct-eval-g-base
                      g-or-geval-meta-correct-eval-g-base
                      eval-g-base-g-apply
                      eval-g-base-cons
                      mk-g-boolean-correct-for-eval-g-base
                      geval-g-if-marker-eval-g-base
                      geval-g-or-marker-eval-g-base
                      
                      general-concretep-not-general-consp
                      general-concretep-not-general-booleanp
                      general-concretep-not-general-numberp
                      gobjectp-tag-rw-to-types eq
                      general-concrete-obj-when-consp-for-eval-g-base
                      general-concrete-obj-when-numberp
                      general-concrete-obj-when-booleanp
                      
                      (:type-prescription bfr-eval)
                      (:type-prescription components-to-number-fn)
                      (:rules-of-class :executable-counterpart :here)
                      
                      gtests-wfp
                      gtests-g-test-marker
                      gobjectp-g-apply
                      gobjectp-cons
                      general-consp-car-gobjectp
                      general-consp-cdr-gobjectp
                      gobjectp-mk-g-boolean
                      gobjectp-apply-case
                      gobjectp-ite-case
                      
                      hyp-fix-bfr-p 
                      bfr-p-bfr-binary-and
                      bfr-p-bfr-binary-or
                      bfr-p-bfr-not 
                      bfr-eval-bfr-binary-and
                      bfr-eval-bfr-not
                      bfr-eval-bfr-binary-or
                      gtests-nonnil-correct-for-eval-g-base
                      hyp-fix-correct
                      general-number-components-bfr-listps
                      (:type-prescription v2i)
                      bfr-p-general-boolean-value
                      bfr-p-bfr-fix
                      bfr-equiv-is-an-equivalence
                      bfr-equiv-implies-equal-bfr-eval-1
                      bfr-eval-g-hyp-marker
                      bfr-p-g-hyp-marker
                      bfr-fix-when-bfr-p

                      cons-equal
                      apply-base-of-equal
                      bfr-eval-bfr-iff
                      bfr-p-bfr-iff
                      bfr-fix-bfr-equiv
                      equal-of-numbers-correct
                      equal-of-numbers-gobjectp
                      
                      gobj-fix-when-gobjectp
                      gobjectp-gobj-fix
                      eval-g-base-gobj-fix
                      hons-equal
                      gobjectp-of-atomic-constants
                      general-concrete-obj-of-atomic-constants
                      general-concretep-of-atomic-constants)
                     ((gobjectp)
                      (general-concrete-obj)
                      (general-concretep)))))

  (local
   (make-event
    `(in-theory
      (enable (:induction ,(gl-fnsym 'equal))))))

  


  (def-g-correct-thm equal eval-g-base
    :hints `(("Goal" 
             :induct (,gfn x y hyp clk)
             :expand ((,gfn x y hyp clk)
                      (,gfn x x hyp clk)
                      (,gfn x y hyp clk)
                      (,gfn x x hyp clk)
                      (eval-g-base x env)
                      (eval-g-base y env)
                      (eval-g-base nil env)
                      (eval-g-base t env))
             :do-not-induct t)
            (case-match id
              ((('0 '1) (n . &) . &)
               (if (member n '(3 4))
                   `(:in-theory
                     (disable possibilities-for-x-1
                              possibilities-for-x-2
                              possibilities-for-x-3
                              possibilities-for-x-4
                              possibilities-for-x-5
                              possibilities-for-x-7
                              possibilities-for-x-8
                              possibilities-for-x-9)
                     :expand ((,',gfn x y hyp clk)
                              (eval-g-base ,(if (eql n 3) 'x 'y) env)
                              (eval-g-base nil env)
                              (eval-g-base t env)))
                 '(:use ((:instance possibilities-for-x)
                         (:instance possibilities-for-x (x y))))))))))
