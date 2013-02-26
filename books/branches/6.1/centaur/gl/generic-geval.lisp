

(in-package "GL")

(include-book "gobjectp")
(include-book "bvecs")
(include-book "tools/bstar" :dir :system)

(local (include-book "gobjectp-thms"))

(defun acl2::boolfix (x)
  (declare (xargs :guard t))
  (if x t nil))





;; Pulls apart a number into its components.  They are stored in order of how
;; often we expect them to be non-default values:
;; real numerator   (can stop here for naturals. Default: nil (meaning zero))
;; real sign        (can stop here for integers. Default: nil (meaning positive))
;; real denominator (can stop here for rationals. Default: (t) (meaning integer))
;; then complex numerator, sign, denominator.
(defun break-g-number (x)
  (declare (xargs :guard (wf-g-numberp x)))
  (let* ((real-numer (nth 0 x))
         (real-denom (if (<= 2 (len x))
                         (nth 1 x)
                       '(t)))
         (imag-numer (nth 2 x))
         (imag-denom (if (<= 4 (len x))
                         (nth 3 x)
                       '(t))))
    (mv real-numer real-denom imag-numer imag-denom)))

(defthm bfr-lists-break-g-number
  (implies (wf-g-numberp x)
           (mv-let (rn rd in id)
             (break-g-number x)
             (and (bfr-listp rn)
                  (bfr-listp rd)
                  (bfr-listp in)
                  (bfr-listp id))))
  :hints(("Goal" :in-theory (enable wf-g-numberp-simpler-def))))





(defun components-to-number-fn (rnum rden inum iden)
  (declare (xargs :guard (and (rationalp rnum)
                              (rationalp rden)
                              (rationalp inum)
                              (rationalp iden))))
  (complex (* rnum (if (eql rden 0) rden (/ rden)))
           (* inum (if (eql iden 0) iden (/ iden)))))


(defmacro components-to-number (rnum &optional
                                     (rden '1)
                                     (inum '0)
                                     (iden '1))
  (list 'components-to-number-fn rnum rden inum iden))

(add-macro-alias components-to-number components-to-number-fn)


(in-theory (disable components-to-number))



(defun gobj-fix-thm-name (name)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name name) "-GOBJ-FIX")
   name))


(defthm measure-for-geval
  (and (implies (and (consp (gobj-fix x))
                     (eq (tag (gobj-fix x)) :g-ite))
                (and (o< (acl2-count (g-ite->test (gobj-fix x)))
                         (acl2-count x))
                     (o< (acl2-count (g-ite->then (gobj-fix x)))
                         (acl2-count x))
                     (o< (acl2-count (g-ite->else (gobj-fix x)))
                         (acl2-count x))))
       (implies (and (consp (gobj-fix x))
                     (eq (tag (gobj-fix x)) :g-apply))
                (o< (acl2-count (g-apply->args (gobj-fix x)))
                    (acl2-count x)))
       (implies (and (consp (gobj-fix x))
                     (not (eq (tag (gobj-fix x)) :g-concrete))
                     (not (eq (tag (gobj-fix x)) :g-boolean))
                     (not (eq (tag (gobj-fix x)) :g-number))
                     (not (eq (tag (gobj-fix x)) :g-ite))
                     (not (eq (tag (gobj-fix x)) :g-apply))
                     (not (eq (tag (gobj-fix x)) :g-var)))
                (and (o< (acl2-count (car (gobj-fix x)))
                         (acl2-count x))
                     (o< (acl2-count (cdr (gobj-fix x)))
                         (acl2-count x)))))
  :hints(("Goal" :in-theory (enable gobj-fix))))


(defconst *geval-body-template*
  '(defun geval (x env)
     (declare (xargs :guard (and (gobjectp x) (consp env))
                     :measure (acl2-count x)
                     :hints (("goal" :in-theory '(measure-for-geval atom)))
                     :verify-guards nil))
     (let ((x (mbe :logic (gobj-fix x) :exec x)))
       (if (atom x)
           ;; Every atom represents itself.
           x
         (pattern-match x

           ;; A Concrete is like an escape sequence; we take (cdr x) as a concrete
           ;; object even if it looks symbolic.
           ((g-concrete obj) obj)

           ;; Boolean
           ((g-boolean bool) (bfr-eval bool (car env)))

           ;; Number.  This is the hairy case.  Can represent all ACL2-NUMBERPs,
           ;; but naturals are more compact than integers, which are more compact
           ;; than rationals, which are more compact than complexes.  Denominators
           ;; are coerced to 1 if they evaluate to 0 -- ugly.
           ((g-number num)
            (b* (((mv real-num
                      real-denom
                      imag-num
                      imag-denom)
                  (break-g-number num)))
              (flet ((uval (n env)
                           (v2n (bfr-eval-list n (car env))))
                     (sval (n env)
                           (v2i (bfr-eval-list n (car env)))))
                (components-to-number (sval real-num env)
                                      (uval real-denom env)
                                      (sval imag-num env)
                                      (uval imag-denom env)))))

           ;; If-then-else.
           ((g-ite test then else)
            (if (geval test env)
                (geval then env)
              (geval else env)))

           ;; Apply: Unevaluated function call.
           ((g-apply fn args) (apply fn (geval args env)))

           ;; Var: untyped variable.
           ((g-var name)   (cdr (het name (cdr env))))

           ;; Conses where the car is not a recognized flag represent conses.
           (& (cons (geval (car x) env)
                    (geval (cdr x) env))))))))


(defun def-geval-fn (geval apply)
  (sublis `((geval . ,geval) (apply . ,apply))
          *geval-body-template*))

(defmacro def-geval (geval apply)
  (def-geval-fn geval apply))


(defstub apply-stub (f args) t)

(def-geval generic-geval apply-stub)

(table eval-g-table 'generic-geval 'apply-stub)

(defun get-guard-verification-theorem (name state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((wrld (w state))
       (ctx 'get-guard-verification-theorem)
       ((er names) (acl2::chk-acceptable-verify-guards
                    name ctx wrld state))
       (ens (acl2::ens state))
       ((mv clauses & state)
        (acl2::guard-obligation-clauses
         names nil ens wrld state))
       (term (acl2::termify-clause-set clauses)))
    (value term)))

(make-event
 (b* (((er thm) (get-guard-verification-theorem
                 'generic-geval state)))
   (value `(defthm generic-geval-guards-ok
             ,thm
             :hints (("goal"
                      :do-not-induct t
                      :in-theory
                      '((:rewrite car-cons)
                        (:rewrite cdr-cons)
                        (:rewrite g-apply->args-acl2-count-thm)
                        (:rewrite g-apply-p-when-wrong-tag)
                        (:rewrite g-boolean-p-when-wrong-tag)
                        (:rewrite g-concrete-p-when-wrong-tag)
                        (:rewrite g-ite->else-acl2-count-thm)
                        (:rewrite g-ite->test-acl2-count-thm)
                        (:rewrite g-ite->then-acl2-count-thm)
                        (:rewrite g-ite-p-when-wrong-tag)
                        (:rewrite g-number-p-when-wrong-tag)
                        (:rewrite g-var-p-when-wrong-tag)
                        (:rewrite gobj-fix-when-gobjectp)
                        (:rewrite gobj-fix-when-not-gobjectp)
                        (:rewrite gobjectp-apply-case)
                        (:rewrite gobjectp-tag-rw-to-types)
                        (:rewrite gobjectp-cons-case)
                        (:rewrite gobjectp-ite-case)
                        (:rewrite gobjectp-number-case)
                        (:rewrite gobjectp-boolean-case)
                        (:rewrite bfr-lists-break-g-number)
                        (:rewrite tag-of-g-concrete)
                        (:rewrite tag-when-g-apply-p)
                        (:rewrite tag-when-g-ite-p)
                        (:rewrite tag-when-g-number-p)
                        (:rewrite gobjectp-gobj-fix)
                        (:elim car-cdr-elim)
                        (:type-prescription acl2-count)
                        (:definition o-finp)
                        (:definition o<)
                        (:definition atom)
                        (:type-prescription break-g-number)
                        (:definition eq)
                        ;; Jared: changed hons-get-fn-do-hopy to hons-get for new hons
                        (:definition hons-get)
                        (:definition member-equal)
                        (:definition acl2::return-last)
                        (:meta mv-nth-cons-meta)
                        (:definition not)
                        (:definition nth)
                        (:definition acl2-count)
                        (:type-prescription hons-assoc-equal)
                        (:executable-counterpart car)
                        (:executable-counterpart cdr)
                        (:executable-counterpart consp)
                        (:executable-counterpart equal)
                        (:executable-counterpart zp)
                        (:type-prescription v2n)
                        (:type-prescription v2i))))
             :rule-classes nil))))

(prove-congruences (gobj-equiv) generic-geval)

(defmacro def-eval-g (name apply)
  ;; Evaluate a G object into a concrete object using variable bindings B.  ENV
  ;; is a cons of (car) a list of Booleans giving Boolean assignments to the
  ;; BDD variables, and (cdr) a symbol alist giving arbitrary assignments to the
  ;; untyped variables.
  `(progn
     (def-geval ,name ,apply)
     
;;      (defthm ,(gobj-fix-thm-name name)
;;        (equal (,name (gobj-fix x) env)
;;               (,name x env))
;;        :hints(("Goal" :by (:functional-instance
;;                            generic-geval-gobj-fix
;;                            (generic-geval ,name)
;;                            (apply-stub ,apply))
;;                :in-theory nil)
;;               '(:expand (,name x env))))

     (verify-guards
      ,name
      :hints (("goal" :by (:functional-instance
                      generic-geval-guards-ok
                      (generic-geval ,name)
                      (apply-stub ,apply)))))

     (table eval-g-table ',name ',apply)))
