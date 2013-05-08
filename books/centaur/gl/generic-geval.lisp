

(in-package "GL")

(include-book "gobjectp")
(include-book "bvecs")
(include-book "tools/bstar" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "defapply")
(include-book "defapply-proofs")
(include-book "cutil/defmvtypes" :dir :system)

(defun acl2::boolfix (x)
  (declare (xargs :guard t))
  (if x t nil))


;; redundant-list-fix, like in vl/util/defs
(defun rlist-fix (x)
  (declare (xargs :guard t))
  (mbe :logic (acl2::list-fix x)
       :exec (if (true-listp X) x (acl2::list-fix x))))



;; Pulls apart a number into its components.  They are stored in order of how
;; often we expect them to be non-default values:
;; real numerator   (can stop here for naturals. Default: nil (meaning zero))
;; real sign        (can stop here for integers. Default: nil (meaning positive))
;; real denominator (can stop here for rationals. Default: (t) (meaning integer))
;; then complex numerator, sign, denominator.
(defun break-g-number (x)
  (declare (xargs :guard t))
  (b* (((mv real-numer x) (if (consp x)
                              (mv (car x) (cdr x))
                            (mv nil nil)))
       ((mv real-denom x) (if (consp x)
                              (mv (car x) (cdr x))
                            (mv '(t) nil)))
       ((mv imag-numer x) (if (consp x)
                              (mv (car x) (cdr x))
                            (mv nil nil)))
       (imag-denom (if (consp x) (car x) '(t))))
    (mv (rlist-fix real-numer)
        (rlist-fix real-denom)
        (rlist-fix imag-numer)
        (rlist-fix imag-denom))))

(acl2::defmvtypes break-g-number (true-listp true-listp true-listp true-listp))






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



;; (defun gobj-fix-thm-name (name)
;;   (intern-in-package-of-symbol
;;    (concatenate 'string (symbol-name name) "-GOBJ-FIX")
;;    name))


(defthm measure-for-geval
  (and (implies (and (consp x)
                     (eq (tag x) :g-ite))
                (and (o< (acl2-count (g-ite->test x))
                         (acl2-count x))
                     (o< (acl2-count (g-ite->then x))
                         (acl2-count x))
                     (o< (acl2-count (g-ite->else x))
                         (acl2-count x))))
       (implies (and (consp x)
                     (eq (tag x) :g-apply))
                (o< (acl2-count (g-apply->args x))
                    (acl2-count x)))
       (implies (and (consp x)
                     (not (eq (tag x) :g-concrete))
                     (not (eq (tag x) :g-boolean))
                     (not (eq (tag x) :g-number))
                     (not (eq (tag x) :g-ite))
                     (not (eq (tag x) :g-apply))
                     (not (eq (tag x) :g-var)))
                (and (o< (acl2-count (car x))
                         (acl2-count x))
                     (o< (acl2-count (cdr x))
                         (acl2-count x))))))


(defthm eqlablep-compound-recognizer
  (equal (eqlablep x)
         (or (acl2-numberp x)
             (symbolp x)
             (characterp x)))
  :rule-classes :compound-recognizer)

(defthmd consp-assoc-equal-of-cons
  (implies (consp k)
           (or (consp (assoc-equal k x))
               (not (assoc-equal k x))))
  :hints(("Goal" :in-theory (enable assoc-equal)))
  :rule-classes :type-prescription)

(defthmd symbol-alistp-implies-eqlable-alistp
  (implies (symbol-alistp x)
           (eqlable-alistp x)))


(defconst *geval-template*
  '(progn
     (defapply _geval_-apply _apply-fns_)
     (defun _geval_ (x env)
       (declare (xargs :guard (consp env)
                       :measure (acl2-count x)
                       :verify-guards nil
                       :hints (("goal" :in-theory '(measure-for-geval atom)))))
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
            (if (_geval_ test env)
                (_geval_ then env)
              (_geval_ else env)))

           ;; Apply: Unevaluated function call.
           ((g-apply fn args) (_geval_-apply fn (_geval_ args env)))

           ;; Var: untyped variable.
           ((g-var name)   (cdr (het name (cdr env))))

           ;; Conses where the car is not a recognized flag represent conses.
           (& (cons (_geval_ (car x) env)
                    (_geval_ (cdr x) env))))))

     (defun _geval_-appalist (x env appal)
       (declare (xargs :guard (and (consp env) (symbol-alistp appal))
                       :measure (acl2-count x)
                       :guard-hints (("goal" :in-theory
                                      '((:type-prescription v2i)
                                        (:type-prescription v2n)
                                        (:type-prescription hons-assoc-equal)
                                        hons-get
                                        acl2::assoc-eql-exec-is-assoc-equal
                                        eqlablep-compound-recognizer
                                        consp-assoc-equal-of-cons
                                        _geval_-apply-arities
                                        symbol-alistp-implies-eqlable-alistp)))
                       :hints (("goal" :in-theory '(measure-for-geval atom)))))
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
            (if (_geval_-appalist test env appal)
                (_geval_-appalist then env appal)
              (_geval_-appalist else env appal)))

           ;; Apply: Unevaluated function call.
           ((g-apply fn args)
            (let* ((args (_geval_-appalist args env appal))
                   (look (member-equal (cons fn (len args))
                                       (_geval_-apply-arities))))
              (if (and look (true-listp args))
                  (_geval_-apply fn args)
                (cdr (assoc (cons fn args) appal)))))

           ;; Var: untyped variable.
           ((g-var name)   (cdr (het name (cdr env))))

           ;; Conses where the car is not a recognized flag represent conses.
           (& (cons (_geval_-appalist (car x) env appal)
                    (_geval_-appalist (cdr x) env appal))))))
     
     (table eval-g-table '_geval_ '(_geval_-appalist _geval_-apply _geval_-apply-arities))))


(defun def-geval-fn (geval fns)
  (declare (xargs :mode :program))
  (acl2::template-subst
   *geval-template*
   :atom-alist `((_geval_ . ,geval)
                 (_apply-fns_ . ,fns))
   :str-alist `(("_GEVAL_" . ,(symbol-name geval)))
   :pkg-sym geval))

(defmacro def-geval (geval fns)
  (def-geval-fn geval fns))


(def-geval generic-geval nil)

(local (defthm generic-geval-appalist-is-instance-of-generic-geval
         t
         :hints (("goal" :use ((:functional-instance
                                generic-geval
                                (generic-geval
                                 (lambda (x env)
                                   (generic-geval-appalist x env appalist)))
                                (apply-stub
                                 (lambda (f args)
                                   (cdr (assoc (cons f args) appalist))))
                                (generic-geval-apply
                                 (lambda (fn args)
                                   (LET*
                                    ((LOOK (MEMBER-EQUAL (CONS FN (LEN ARGS))
                                                         (GENERIC-GEVAL-APPLY-ARITIES))))
                                    (IF (AND LOOK (TRUE-LISTP ARGS))
                                        (GENERIC-GEVAL-APPLY FN ARGS)
                                        (CDR (ASSOC (CONS FN ARGS)
                                                    APPALIST))))))))
                  :in-theory '(generic-geval-apply
                               generic-geval-apply-arities
                               member-equal
                               generic-geval-appalist)))
         :rule-classes nil))

(defun get-guard-verification-theorem (name state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((er &) (acl2::in-theory-fn nil state nil '(in-theory nil)))
       (wrld (w state))
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
             :hints (("goal" :do-not-induct t))
             :rule-classes nil))))

;; (prove-congruences (gobj-equiv) generic-geval)

(defconst *geval-appalist-func-inst-template*
  '(:computed-hint-replacement
    ((and stable-under-simplificationp
; (not (cw "clause: ~x0~%" clause))
          ;; both clauses should be of the form ((equal a b))
          (if (equal (car (cadr (car clause))) ;; fn symbol of A
                     '_geval_-appalist)
              '(:expand ((_geval_-appalist x env appalist))
                :do-not nil)
            '(:clause-processor (apply-with-stub/alist-cp clause
                                                          nil
                                                          state)))))
    :use ((:functional-instance
           _thmname_
           (_geval_
            (lambda (x env)
              (_geval_-appalist x env appalist)))
           (apply-stub
            (lambda (f args)
              (cdr (assoc (cons f args) appalist))))
           (_geval_-apply
            (lambda (fn args)
              (IF (AND (MEMBER-EQUAL (CONS FN (LEN ARGS))
                                     (_geval_-APPLY-ARITIES))
                       (TRUE-LISTP ARGS))
                  (_geval_-APPLY FN ARGS)
                  (CDR (ASSOC (CONS FN ARGS)
                              APPALIST)))))))
    :in-theory nil
    :do-not '(preprocess simplify)))

(defun geval-appalist-functional-inst-hint (thm geval)
  (declare (xargs :mode :program))
  (acl2::template-subst
   *geval-appalist-func-inst-template*
   :atom-alist `((_geval_ . ,geval)
                 (_thmname_ . ,thm))
   :str-alist `(("_GEVAL_" . ,(symbol-name geval)))
   :pkg-sym geval))


(defconst *def-eval-g-template*
  '(progn
     (def-geval _geval_ _apply-fns_)
     (verify-guards _geval_
       :hints (("goal" :by (:functional-instance
                            generic-geval-guards-ok
                            (generic-geval _geval_)
                            (generic-geval-apply _geval_-apply)
                            (apply-stub _geval_-apply)))))
     (local (defthm _geval_-appalist-is-instance-of-_geval_
              t
              :hints ((geval-appalist-functional-inst-hint '_geval_ '_geval_))
              :rule-classes nil))))

(defmacro def-eval-g (geval fns)
  (acl2::template-subst
   *def-eval-g-template*
   :atom-alist `((_geval_ . ,geval)
                 (_apply-fns_ . ,fns))
   :str-alist `(("_GEVAL_" . ,(symbol-name geval)))
   :pkg-sym geval))

(local
 ;; test
 (def-eval-g implies-geval
   (implies)))

(with-output :off :all :on (error)
  (local
   ;; test
   (def-eval-g little-geval
     (BINARY-*
      BINARY-+
      PKG-WITNESS
;   UNARY-/
      UNARY--
      COMPLEX-RATIONALP
;   BAD-ATOM<=
      ACL2-NUMBERP
      SYMBOL-PACKAGE-NAME
      INTERN-IN-PACKAGE-OF-SYMBOL
      CODE-CHAR
;   DENOMINATOR
      CDR
;   COMPLEX
      CAR
      CONSP
      SYMBOL-NAME
      CHAR-CODE
      IMAGPART
      SYMBOLP
      REALPART
;   NUMERATOR
      EQUAL
      STRINGP
      RATIONALP
      CONS
      INTEGERP
      CHARACTERP
      <
      COERCE
      booleanp
      logbitp
      binary-logand
      binary-logior
      lognot
      ash
      integer-length
      floor
      mod
      truncate
      rem
      acl2::boolfix

      ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
      NOT IMPLIES
      EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
      PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
      ;; FORCE CASE-SPLIT
      ;; DOUBLE-REWRITE
      ))))

(in-theory (enable generic-geval-apply))
