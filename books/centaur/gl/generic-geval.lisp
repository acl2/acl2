; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "gobjectp")
(include-book "bvecs")
(include-book "std/util/bstar" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "std/util/defmvtypes" :dir :system)
(include-book "../misc/defapply")

;; (defun acl2::boolfix (x)
;;   (declare (xargs :guard t))
;;   (if x t nil))


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
    ;; (mv (list-fix real-numer)
    ;;     (list-fix real-denom)
    ;;     (list-fix imag-numer)
    ;;     (list-fix imag-denom))
    (mv real-numer
        real-denom
        imag-numer
        imag-denom)))

;; (acl2::defmvtypes break-g-number (true-listp true-listp true-listp true-listp))






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

(mutual-recursion
 (defun gobj->term (x env)
   (declare (xargs :guard (consp env)
                   :measure (acl2-count x)
                   :hints (("goal" :in-theory '(measure-for-geval atom)))))
   (if (atom x)
       (kwote x)
     (pattern-match x
       ((g-concrete obj) (kwote obj))

       ((g-boolean bool) (kwote (bfr-eval bool (car env))))

       ((g-number num)
        (b* (((mv real-num
                  real-denom
                  imag-num
                  imag-denom)
              (break-g-number num)))
          (flet ((uval (n env)
                       (bfr-list->u n (car env)))
                 (sval (n env)
                       (bfr-list->s n (car env))))
            (kwote
             (components-to-number (sval real-num env)
                                   (uval real-denom env)
                                   (sval imag-num env)
                                   (uval imag-denom env))))))

       ((g-ite test then else)
        (list 'if
              (gobj->term test env)
              (gobj->term then env)
              (gobj->term else env)))

       ((g-var name) (kwote (cdr (hons-get name (cdr env)))))

       ((g-apply fn args)
        (and (not (eq fn 'quote))
             (cons fn (gobj-list->terms args env))))

       (& ;; cons
        (list 'cons
              (gobj->term (car x) env)
              (gobj->term (cdr x) env))))))

 (defun gobj-list->terms (x env)
   (declare (xargs :guard (consp env)
                   :measure (acl2-count x)))
   (if (atom x)
       nil
     (cons (gobj->term (car x) env)
           (gobj-list->terms (cdr x) env)))))

(mutual-recursion
 (defun gobj-ind (x env)
   (declare (xargs :guard (consp env)
                   :measure (acl2-count x)
                   :hints (("goal" :in-theory '(measure-for-geval atom)))))
   (if (atom x)
       (kwote x)
     (pattern-match x
       ((g-concrete obj) (kwote obj))

       ((g-boolean bool) (kwote (bfr-eval bool (car env))))

       ((g-number num)
        (b* (((mv real-num
                  real-denom
                  imag-num
                  imag-denom)
              (break-g-number num)))
          (flet ((uval (n env)
                       (bfr-list->u n (car env)))
                 (sval (n env)
                       (bfr-list->s n (car env))))
            (kwote
             (components-to-number (sval real-num env)
                                   (uval real-denom env)
                                   (sval imag-num env)
                                   (uval imag-denom env))))))

       ((g-ite test then else)
        (list 'if
              (gobj-ind test env)
              (gobj-ind then env)
              (gobj-ind else env)))

       ((g-var name) (kwote (cdr (hons-get name (cdr env)))))

       ((g-apply fn args)
        (cons fn (gobj-list-ind args env)))

       (& ;; cons
        (list 'cons
              (gobj-ind (car x) env)
              (gobj-ind (cdr x) env))))))

 (defun gobj-list-ind (x env)
   (declare (xargs :guard (consp env)
                   :measure (acl2-count x)))
   (if (atom x)
       nil
     (cons (gobj-ind (car x) env)
           (gobj-list-ind (cdr x) env)))))


(flag::make-flag gobj-flag gobj-ind
                 :flag-mapping ((gobj-ind . gobj)
                                (gobj-list-ind . list)))

(in-theory (disable gobj-ind gobj-list-ind))


(defconst *geval-template*
  '(progn
     (acl2::defapply/ev/concrete-ev _geval_ _apply-fns_)
     ;; (defapply _geval_-apply _apply-fns_)
     (mutual-recursion
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
                            (bfr-list->u n (car env)))
                      (sval (n env)
                            (bfr-list->s n (car env))))
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
            ((g-apply fn args)
             (and (not (eq fn 'quote))
                  (let* ((args (_geval_-list args env)))
                    (mbe :logic (_geval_-ev (cons fn (kwote-lst args)) nil)
                         :exec (b* ((args (acl2::list-fix args))
                                    ((mv ok val) (_geval_-apply fn args))
                                    ((when ok) val))
                                 (_geval_-ev (cons fn (kwote-lst args))
                                             nil))))))

            ;; Var: untyped variable.
            ((g-var name)   (cdr (het name (cdr env))))

            ;; Conses where the car is not a recognized flag represent conses.
            (& (cons (_geval_ (car x) env)
                     (_geval_ (cdr x) env))))))

      (defun _geval_-list (x env)
        (declare (xargs :guard (consp env)
                        :measure (acl2-count x)))
        (if (atom x)
            nil
          (cons (_geval_ (car x) env)
                (_geval_-list (cdr x) env)))))

     (in-theory (disable _geval_ _geval_-list))

     (table eval-g-table '_geval_ '(_geval_-list
                                    _geval_-ev
                                    _geval_-ev-lst
                                    _geval_-apply
                                    _geval_-ev-concrete
                                    _geval_-ev-concrete-lst
                                    . _apply-fns_))))


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


(def-geval base-geval nil)



;; (defthm generic-geval-apply-ev-lst-of-kwote-lst
;;   (equal (generic-geval-apply-ev-lst (kwote-lst x) a)
;;          (acl2::list-fix x)))

;; ;; (defthm generic-geval-apply-ev-lst-of-kwote-lst-a
;; ;;   (implies (syntaxp (not (equal a ''nil)))
;; ;;            (equal (generic-geval-apply-ev-lst (kwote-lst x) a)
;; ;;                   (generic-geval-apply-ev-lst (kwote-lst x) nil))))

;; ;; (defthm kwote-lst-of-generic-geval-apply-ev-lst-of-kwote-lst
;; ;;   (equal (kwote-lst (generic-geval-apply-ev-lst (kwote-lst x) a))
;; ;;          (kwote-lst x)))

;; (defthm true-listp-generic-geval-apply-ev-lst
;;   (true-listp (generic-geval-apply-ev-lst x a))
;;   :hints (("Goal" :induct (len x))))

;; (mutual-recursion
;;  (defund generic-geval-apply-ev-substitution (x a appalist)
;;    (cond ((atom x) (and x (cdr (assoc x a))))
;;          ((eq (car x) 'quote) (cadr x))
;;          ((consp (car x))
;;           (generic-geval-apply-ev-substitution
;;            (caddar x)
;;            (pairlis$ (cadar x)
;;                      (generic-geval-apply-ev-substitution-lst
;;                       (cdr x) a appalist))
;;            appalist))
;;          ((assoc (car x) (generic-geval-apply-arities))
;;           (generic-geval-apply-ev (cons (car x)
;;                                         (kwote-lst
;;                                          (generic-geval-apply-ev-substitution-lst
;;                                           (cdr x) a appalist)))
;;                                   nil))
;;          (t (cdr (assoc (cons (car x)
;;                               (generic-geval-apply-ev-substitution-lst
;;                                (cdr x) a appalist))
;;                         appalist)))))

;;  (defund generic-geval-apply-ev-substitution-lst (x a appalist)
;;    (if (atom x)
;;        nil
;;      (cons (generic-geval-apply-ev-substitution (car x) a appalist)
;;            (generic-geval-apply-ev-substitution-lst (cdr x) a appalist)))))


;; (defun list-equiv1 (x y)
;;   (if (and (atom x) (atom y))
;;       t
;;     (and (consp x) (consp y)
;;          (equal (car x) (car y))
;;          (list-equiv1 (cdr x) (cdr y)))))

;; (defthmd list-equiv-is-list-equiv1
;;   (equal (acl2::list-equiv x y)
;;          (list-equiv1 x y)))

;; (defcong acl2::list-equiv equal (generic-geval-apply-ev-lst x a) 1
;;   :hints (("goal" ::in-theory (enable list-equiv-is-list-equiv1))))

;; (defcong acl2::list-equiv equal (generic-geval-apply-ev-substitution-lst x a appalist) 1
;;   :hints (("goal" ::in-theory (enable list-equiv-is-list-equiv1)
;;            :induct (list-equiv1 x acl2::x-equiv)
;;            :expand ((generic-geval-apply-ev-substitution-lst
;;                      x a appalist)
;;                     (generic-geval-apply-ev-substitution-lst
;;                      acl2::x-equiv a appalist)))))

;; (defcong acl2::list-equiv equal (kwote-lst x) 1
;;   :hints (("goal" ::in-theory (enable list-equiv-is-list-equiv1))))

;; (defcong acl2::list-equiv equal (generic-geval-apply f args) 2
;;   :hints(("Goal" :in-theory (enable generic-geval-apply))))

;; (defthm generic-geval-apply-ev-substitution-lst-of-kwote-lst
;;   (equal (generic-geval-apply-ev-substitution-lst (kwote-lst x) a appalist)
;;          (acl2::list-fix x))
;;   :hints (("goal" :induct (kwote-lst x)
;;            :expand ((:free (x y)
;;                      (generic-geval-apply-ev-substitution-lst
;;                       (cons x y) a appalist))
;;                     (generic-geval-apply-ev-substitution-lst
;;                      nil a appalist)
;;                     (generic-geval-apply-ev-substitution
;;                      (list 'quote (car x)) a appalist)))))

;; (defthm sdfasd
;;   t
;;   :hints (("goal" :use
;;            ((:functional-instance
;;              (:theorem (equal (generic-geval-apply-ev-substitution x a appalist)
;;                               (generic-geval-apply-ev-substitution x a appalist)))
;;              (generic-geval-apply-ev-lst
;;               (lambda (x a)
;;                 (generic-geval-apply-ev-substitution-lst x a appalist)))
;;              (generic-geval-apply-ev
;;               (lambda (x a)
;;                 (generic-geval-apply-ev-substitution x a appalist)))))
;;            :expand ((generic-geval-apply-ev-substitution x a appalist))
;;            :in-theory (enable
;;                        generic-geval-apply
;;                        generic-geval-apply-ev-substitution
;;                        generic-geval-apply-ev-substitution-lst)
;;            :do-not-induct t))
;;   :rule-classes nil
;;   :otf-flg t)



;; (local (defthm generic-geval-appalist-is-instance-of-generic-geval
;;          t
;;          :hints (("goal" :use ((:functional-instance
;;                                 generic-geval
;;                                 (generic-geval
;;                                  (lambda (x env)
;;                                    (generic-geval-appalist x env appalist)))
;;                                 (generic-geval-ev
;;                                  (lambda (x a)
;;                                    (generic-geval-ev-concrete x a appalist)))
;;                                 (generic-geval-ev-lst
;;                                  (lambda (x a)
;;                                    (generic-geval-ev-concrete-lst
;;                                     x a appalist)))))
;;                   ;; '(generic-geval-apply-ev-lst-of-atom
;;                              ;;   generic-geval-apply-ev-substitution)
;;                   ;; :in-theory '(generic-geval-apply
;;                   ;;              generic-geval-apply-arities
;;                   ;;              member-equal
;;                   ;;              generic-geval-appalist)
;;                   :do-not-induct t)
;;                  ;; (and stable-under-simplificationp
;;                  ;;      '(:in-theory (enable
;;                  ;;                    generic-geval-apply-ev-of-fncall-args)
;;                  ;;        :expand ((:free (a)
;;                  ;;                  (generic-geval-apply-ev-substitution
;;                  ;;                   x a appalist))
;;                  ;;                 (:free (x y a)
;;                  ;;                  (generic-geval-apply-ev-substitution
;;                  ;;                   (cons x y) a appalist)))))
;;                  ;; (and stable-under-simplificationp
;;                  ;;      '(:in-theory (enable
;;                  ;;                    generic-geval-apply-ev-substitution
;;                  ;;                    generic-geval-apply-ev-of-fncall-args)))
;;                  ;; (and stable-under-simplificationp
;;                  ;;      '(:expand ((generic-geval-ev-concrete-lst
;;                  ;;                  acl2::x-lst a appalist)
;;                  ;;                 (generic-geval-apply-ev-substitution
;;                  ;;                  x a appalist))))
;;                  )
;;          :rule-classes nil
;;          :otf-flg t))

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
                 'base-geval state)))
   (value `(defthm base-geval-guards-ok
             ,thm
             :hints (("goal" :do-not-induct t))
             :rule-classes nil))))

;; (prove-congruences (gobj-equiv) generic-geval)

;; (defconst *geval-appalist-func-inst-template*
;;   '(:computed-hint-replacement
;;     ((and stable-under-simplificationp
;;           '(:expand ((:free (f ar)
;;                       (_geval_-apply f ar))
;;                      (:free (x) (hide x))))))
;;     :use
;;     ((:functional-instance
;;       _theorem_
;;       (_geval_ (lambda (x env)
;;                        (_geval_-appalist x env appalist)))
;;       (_geval_-ev (lambda (x a)
;;                           (_geval_-ev-concrete x a appalist)))
;;       (_geval_-ev-lst
;;        (lambda (x a)
;;                (_geval_-ev-concrete-lst x a appalist)))))
;;     :in-theory '(nth-of-_geval_-ev-concrete-lst
;;                  acl2::car-to-nth-meta-correct
;;                  acl2::nth-of-cdr
;;                  _geval_-ev-concrete-lst-of-kwote-lst
;;                  acl2::list-fix-when-true-listp
;;                  acl2::kwote-list-list-fix
;;                  (:t _geval_-ev-concrete-lst)
;;                  (:t acl2::list-fix)
;;                  car-cons cdr-cons nth-0-cons (nfix))
;;     :expand ((_geval_-ev-concrete x a appalist)
;;              (:free (f ar)
;;               (_geval_-ev-concrete (cons f ar) nil appalist))
;;              (:free (x) (hide x))
;;              (_geval_-ev-concrete-lst acl2::x-lst a appalist)
;;              (_geval_-appalist x env appalist))
;;     :do-not-induct t))


;; (:use ((:functional-instance
;;            _geval_
;;            (_geval_
;;             (lambda (x env)
;;               (_geval_-appalist x env appalist)))
;;            (_geval_-ev
;;             (lambda (x a)
;;               (_geval_-ev-concrete x a appalist)))
;;            (_geval_-ev-lst
;;             (lambda (x a)
;;               (_geval_-ev-concrete-lst
;;                x a appalist)))))
;;     ;; '(generic-geval-apply-ev-lst-of-atom
;;     ;;   generic-geval-apply-ev-substitution)
;;     ;; :in-theory '(generic-geval-apply
;;     ;;              generic-geval-apply-arities
;;     ;;              member-equal
;;     ;;              generic-geval-appalist)
;;     :do-not-induct t))
;;   '(:computed-hint-replacement
;;     ((and stable-under-simplificationp
;; ; (not (cw "clause: ~x0~%" clause))
;;           ;; both clauses should be of the form ((equal a b))
;;           (if (equal (car (cadr (car clause))) ;; fn symbol of A
;;                      '_geval_-appalist)
;;               '(:expand ((_geval_-appalist x env appalist))
;;                 :do-not nil)
;;             '(:clause-processor (apply-with-stub/alist-cp clause
;;                                                           nil
;;                                                           state)))))
;;     :use ((:functional-instance
;;            _thmname_
;;            (_geval_
;;             (lambda (x env)
;;               (_geval_-appalist x env appalist)))
;;            (apply-stub
;;             (lambda (f args)
;;               (cdr (assoc (cons f args) appalist))))
;;            (_geval_-apply
;;             (lambda (fn args)
;;               (IF (AND (MEMBER-EQUAL (CONS FN (LEN ARGS))
;;                                      (_geval_-APPLY-ARITIES))
;;                        (TRUE-LISTP ARGS))
;;                   (_geval_-APPLY FN ARGS)
;;                   (CDR (ASSOC (CONS FN ARGS)
;;                               APPALIST)))))))
;;     :in-theory nil
;;     :do-not '(preprocess simplify)))

;; (defun geval-appalist-functional-inst-hint (thm geval)
;;   (declare (xargs :mode :program))
;;   (acl2::template-subst
;;    *geval-appalist-func-inst-template*
;;    :atom-alist `((_geval_ . ,geval)
;;                  (_theorem_ . ,thm))
;;    :str-alist `(("_GEVAL_" . ,(symbol-name geval)))
;;    :pkg-sym geval))


(defconst *def-eval-g-template*
  '(progn
     (local (in-theory #!acl2 (enable car-cdr-elim
                                      car-cons
                                      cdr-cons
                                      acl2-count
                                      (:t acl2-count)
                                      o< o-finp
                                      acl2::true-listp-of-list-fix
                                      pseudo-term-listp
                                      pseudo-termp
                                      eqlablep
                                      consp-assoc-equal
                                      assoc-eql-exec-is-assoc-equal
                                      alistp-pairlis$
                                      atom not eq
                                      symbol-listp-forward-to-true-listp)))
     (def-geval _geval_ _apply-fns_)
     (verify-guards _geval_
       :hints (("goal" :use ((:functional-instance
                              base-geval-guards-ok
                              (base-geval _geval_)
                              (base-geval-list _geval_-list)
                              (base-geval-ev _geval_-ev)
                              (base-geval-ev-lst _geval_-ev-lst)))
                :in-theory (e/d* (_geval_-ev-of-fncall-args
                                  _geval_-apply-agrees-with-_geval_-ev
                                  eq atom
                                  _geval_
                                  _geval_-list
                                  base-geval-apply)
                                 (_geval_-apply))))
       :otf-flg t)
     ;; (local (defthm _geval_-appalist-is-instance-of-_geval_
     ;;          t
     ;;          :hints ((geval-appalist-functional-inst-hint '_geval_ '_geval_))
     ;;          :rule-classes nil))
     ))

(defmacro def-eval-g (geval fns)
  (acl2::template-subst
   *def-eval-g-template*
   :atom-alist `((_geval_ . ,geval)
                 (_apply-fns_ . ,fns))
   :str-alist `(("_GEVAL_" . ,(symbol-name geval)))
   :pkg-sym geval))

(def-eval-g generic-geval (cons if))

(defthm-gobj-flag
  (defthm generic-geval-is-generic-geval-ev-of-gobj->term
    (equal (generic-geval-ev (gobj->term x env) a)
           (generic-geval x env))
    :hints('(:in-theory (enable generic-geval-ev-of-fncall-args
                                generic-geval gobj->term)
             :expand ((gobj->term x env)))
           (and stable-under-simplificationp
                '(:cases ((eq (g-apply->fn x) 'quote))
                  :expand ((gobj-list->terms (g-apply->args x) env)))))
    :flag gobj)
  (defthm generic-geval-list-is-generic-geval-ev-lst-of-gobj-list->terms
    (equal (generic-geval-ev-lst (gobj-list->terms x env) a)
           (generic-geval-list x env))
    :hints ('(:expand ((generic-geval-list x env)
                       (gobj-list->terms x env))))
    :flag list))





(local
 ;; test
 (def-eval-g implies-geval
   (implies)))



;; (DEFTHM LITTLE-GEVAL-APPALIST-IS-INSTANCE-OF-LITTLE-GEVAL
;;   T
;;   :HINTS ('(:computed-hint-replacement
;;             ((and stable-under-simplificationp
;;                   '(:expand ((:free (f ar)
;;                               (little-geval-apply f ar))))))
;;             :USE
;;             ((:FUNCTIONAL-INSTANCE
;;               LITTLE-GEVAL
;;               (LITTLE-GEVAL (LAMBDA (X ENV)
;;                                     (LITTLE-GEVAL-APPALIST X ENV APPALIST)))
;;               (LITTLE-GEVAL-EV (LAMBDA (X A)
;;                                        (LITTLE-GEVAL-EV-CONCRETE X A APPALIST)))
;;               (LITTLE-GEVAL-EV-LST
;;                (LAMBDA (X A)
;;                        (LITTLE-GEVAL-EV-CONCRETE-LST X A APPALIST)))))
;;             :in-theory '(nth-of-little-geval-ev-concrete-lst
;;                          acl2::car-to-nth-meta-correct
;;                          acl2::nth-of-cdr
;;                          little-geval-ev-concrete-lst-of-kwote-lst
;;                          acl2::list-fix-when-true-listp
;;                          acl2::kwote-list-list-fix
;;                          (:t little-geval-ev-concrete-lst)
;;                          (:t acl2::list-fix)
;;                          car-cons cdr-cons nth-0-cons (nfix))
;;             :expand ((little-geval-ev-concrete x a appalist)
;;                      (:free (f ar)
;;                       (little-geval-ev-concrete (cons f ar) nil appalist))
;;                      (little-geval-ev-concrete-lst acl2::x-lst a appalist)
;;                      (little-geval-appalist x env appalist))
;;             :DO-NOT-INDUCT T))
;;   :RULE-CLASSES NIL)

(with-output :off :all :on (error)
  (local
   ;; test
   (def-eval-g little-geval
     (BINARY-* if cons
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
;      acl2::boolfix

      ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
      NOT IMPLIES
      EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
      PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
      ;; FORCE CASE-SPLIT
      ;; DOUBLE-REWRITE
      ))))

(in-theory (enable generic-geval-apply))
