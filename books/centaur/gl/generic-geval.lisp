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
(include-book "gobject-types")
(include-book "bvecs")
(include-book "std/util/bstar" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "std/util/defmvtypes" :dir :system)
(include-book "../misc/defapply")

;; (defun acl2::boolfix (x)
;;   (declare (xargs :guard t))
;;   (if x t nil))



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
                     (not (eq (tag x) :g-integer))
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

       ((g-integer bits)
        (kwote (ec-call (bfr-list->s bits (car env)))))

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
                   :verify-guards nil
                   :hints (("goal" :in-theory '(measure-for-geval atom)))))
   (if (atom x)
       (kwote x)
     (pattern-match x
       ((g-concrete obj) (kwote obj))

       ((g-boolean bool) (kwote (bfr-eval bool (car env))))

       ((g-integer bits)
        (kwote (bfr-list->s bits (car env))))

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
                 :flag-mapping ((gobj-ind gobj)
                                (gobj-list-ind list)))

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

            ;; Integer
            ((g-integer bits) (ec-call (bfr-list->s bits (car env))))

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



(defun get-guard-verification-theorem (name guard-debug state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((er &) (acl2::in-theory-fn nil state '(in-theory nil)))
       (wrld (w state))
       (ctx 'get-guard-verification-theorem)
       ((er names) (acl2::chk-acceptable-verify-guards
                    name t ctx wrld state))
       (ens (acl2::ens state))
       ((mv clauses &)
        (acl2::guard-obligation-clauses
         names guard-debug ens wrld state))
       (term (acl2::termify-clause-set clauses)))
    (value term)))

(make-event
 (b* (((er thm) (get-guard-verification-theorem
                 'base-geval nil state)))
   (value `(defthm base-geval-guards-ok
             ,thm
             :hints (("goal" :do-not-induct t))
             :rule-classes nil))))



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
                                  _geval_-ev-of-nonsymbol-atom
                                  _geval_-ev-of-bad-fncall
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
