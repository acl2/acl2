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
(include-book "symbolic-arithmetic")
(local (include-book "std/alists/alistp" :dir :system))
; cert_param: (non-acl2r)



;; An shape spec is an object that is similar to a g object, but a) where there
;; would be BDDs in a g object, there are natural numbers in an shape spec, and
;; b) no G-APPLY constructs are allowed in an shape spec.

(defund number-specp (nspec)
  (declare (xargs :guard t))
  (and (true-listp nspec)
       (<= (len nspec) 4)
       (nat-listp (car nspec))
       (nat-listp (cadr nspec))
       (nat-listp (caddr nspec))
       (nat-listp (cadddr nspec))
       (or (not (cdr nspec))
           (consp (cadr nspec)))
       (or (not (cdddr nspec))
           (consp (cadddr nspec)))))

(defagg g-integer (sign bits var))
(defagg g-integer? (sign bits var intp))
(defagg g-call (fn args inverse))

(defund ss-unary-functionp (x)
  (declare (xargs :guard t))
  (and (not (eq x 'quote))
       (or (symbolp x)
           (and (consp x)
                (eq (car x) 'lambda)
                (consp (cdr x))
                (symbol-listp (cadr x))
                (eql (len (cadr x)) 1)
                (consp (cddr x))
                (pseudo-termp (caddr x))
                (not (cdddr x))))))

(define variablep (x)
  (and (symbolp x)
       (not (booleanp x))
       (not (keywordp x)))
  ///
  (defthm variablep-compound-recognizer
    (implies (variablep x)
             (and (symbolp x) (not (booleanp x))))
    :rule-classes :compound-recognizer))

(defines shape-specp
  (define shape-specp (x)
    :measure (acl2-count x)
    (if (atom x)
        (and (not (g-keyword-symbolp x))
             (not (member x '(:g-integer :g-integer? :g-call))))
      (case (tag x)
        (:g-number (number-specp (g-number->num x)))
        (:g-integer (and (natp (g-integer->sign x))
                         (nat-listp (g-integer->bits x))
                         (variablep (g-integer->var x))))
        (:g-integer? (and (natp (g-integer?->sign x))
                          (nat-listp (g-integer?->bits x))
                          (natp (g-integer?->intp x))
                          (variablep (g-integer?->var x))))
        (:g-boolean (natp (g-boolean->bool x)))
        (:g-concrete t)
        (:g-var (variablep (g-var->name x)))
        (:g-ite
         (and (shape-specp (g-ite->test x))
              (shape-specp (g-ite->then x))
              (shape-specp (g-ite->else x))))
        (:g-apply nil)
        (:g-call (and (symbolp (g-call->fn x))
                      (not (eq (g-call->fn x) 'quote))
                      (shape-spec-listp (g-call->args x))
                      (ss-unary-functionp (g-call->inverse x))))
        (otherwise (and (shape-specp (car x))
                        (shape-specp (cdr x))))))
    ///
    (defthm shape-specp-when-atom
      (implies (atom x)
               (equal (shape-specp x)
                      (and (not (g-keyword-symbolp x))
                           (not (member x '(:g-integer :g-integer? :g-call))))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-number
      (implies (equal (tag x) :g-number)
               (equal (shape-specp x)
                      (number-specp (g-number->num x))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-integer
      (implies (equal (tag x) :g-integer)
               (equal (shape-specp x)
                       (and (natp (g-integer->sign x))
                            (nat-listp (g-integer->bits x))
                            (variablep (g-integer->var x)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-integer?
      (implies (equal (tag x) :g-integer?)
               (equal (shape-specp x)
                      (and (natp (g-integer?->sign x))
                           (nat-listp (g-integer?->bits x))
                           (natp (g-integer?->intp x))
                           (variablep (g-integer?->var x)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-boolean
      (implies (equal (tag x) :g-boolean)
               (equal (shape-specp x)
                      (natp (g-boolean->bool x))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-concrete
      (implies (equal (tag x) :g-concrete)
               (equal (shape-specp x) t))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-var
      (implies (equal (tag x) :g-var)
               (equal (shape-specp x)
                      (variablep (g-var->name x))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-ite
      (implies (equal (tag x) :g-ite)
               (equal (shape-specp x)
                      (and (shape-specp (g-ite->test x))
                           (shape-specp (g-ite->then x))
                           (shape-specp (g-ite->else x)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-call
      (implies (equal (tag x) :g-call)
               (equal (shape-specp x)
                      (and (symbolp (g-call->fn x))
                           (not (eq (g-call->fn x) 'quote))
                           (shape-spec-listp (g-call->args x))
                           (ss-unary-functionp (g-call->inverse x)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-cons
      (implies (and (consp x)
                    (not (equal (tag x) :g-number))
                    (not (equal (tag x) :g-boolean))
                    (not (equal (tag x) :g-integer))
                    (not (equal (tag x) :g-integer?))
                    (not (equal (tag x) :g-concrete))
                    (not (equal (tag x) :g-var))
                    (not (equal (tag x) :g-ite))
                    (not (equal (tag x) :g-call)))
               (equal (shape-specp x)
                      (and (not (equal (tag x) :g-apply))
                           (shape-specp (car x))
                           (shape-specp (cdr x)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm shape-specp-when-g-apply
      (implies (equal (tag x) :g-apply)
               (not (shape-specp x)))
      :rule-classes ((:rewrite :backchain-limit-lst 0))))
                    
  (define shape-spec-listp (x)
    :measure (acl2-count x)
    (if (atom x)
        (eq x nil)
      (and (shape-specp (car x))
           (shape-spec-listp (cdr x))))
    ///
    (defthm shape-spec-listp-when-atom
      (implies (atom x)
               (equal (shape-spec-listp x)
                      (equal x nil)))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))
    (defthm shape-spec-listp-when-cons
      (implies (consp x)
               (equal (shape-spec-listp x)
                      (and (shape-specp (car x))
                           (shape-spec-listp (cdr x)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))))



(mutual-recursion
 (defun shape-spec-ind (x)
   (if (atom x)
       x
     (case (tag x)
       ((:g-number :g-integer :g-integer? :g-boolean :g-concrete :g-var) x)
       (:g-ite (list (shape-spec-ind (g-ite->test x))
                     (shape-spec-ind (g-ite->then x))
                     (shape-spec-ind (g-ite->else x))))
       (:g-call (shape-spec-list-ind (g-call->args x)))
       (otherwise (list (shape-spec-ind (car x))
                        (shape-spec-ind (cdr x)))))))
 (defun shape-spec-list-ind (x)
   (if (atom x)
       nil
     (cons (shape-spec-ind (car x))
           (shape-spec-list-ind (cdr x))))))


(flag::make-flag shape-spec-flag shape-spec-ind
                 :flag-mapping ((shape-spec-ind . ss)
                                (shape-spec-list-ind . list)))




(define shape-spec-obj-in-range-iff ((x shape-specp) obj)
  ;; only works on call-free objects
  :guard-hints(("Goal" :in-theory (enable shape-specp)))
  :returns (in-range booleanp :rule-classes :type-prescription)
  (if (atom x)
      (iff x obj)
    (pattern-match x
      ((g-number &)
       (bool-fix obj))
      ((g-integer & & &) (bool-fix obj))
      ((g-integer? & & & &) t)
      ((g-boolean &) t)
      ((g-var &) t)
      ((g-ite if then else)
       (or (and (shape-spec-obj-in-range-iff if t)
                (shape-spec-obj-in-range-iff then obj))
           (and (shape-spec-obj-in-range-iff if nil)
                (shape-spec-obj-in-range-iff else obj))))
      ((g-call & & &) nil)
      ((g-concrete y) (iff y obj))
      (& (bool-fix obj))))
  ///
  (fty::deffixcong iff equal (shape-spec-obj-in-range-iff x obj) obj))

(defund integer-in-range (vlist obj)
  (declare (xargs :guard t))
  (and (integerp obj)
       (if (atom vlist)
           (eql obj 0)
         (and (<= (- (ash 1 (len (cdr vlist)))) obj)
              (< obj (ash 1 (len (cdr vlist))))))))

(defund natural-in-range (vlist obj)
  (declare (xargs :guard t))
  (and (natp obj)
       (and (<= 0 obj)
            (< obj (ash 1 (len vlist))))))

(defund number-spec-in-range (nspec obj)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints(("Goal" :in-theory (enable number-specp)))))
  (and (acl2-numberp obj)
       (integer-in-range (car nspec) (numerator (realpart obj)))
       (if (consp (cdr nspec))
           (natural-in-range (cadr nspec) (denominator (realpart obj)))
         (integerp obj))
       (integer-in-range (caddr nspec) (numerator (imagpart obj)))
       (if (consp (cdddr nspec))
           (natural-in-range
            (cadddr nspec) (denominator (imagpart obj)))
         (integerp (imagpart obj)))))

(defund shape-spec-obj-in-range (x obj)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints(("Goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      (equal x obj)
    (pattern-match x
      ((g-number n) (number-spec-in-range n obj))
      ((g-integer & & &) (integerp obj))
      ((g-integer? & & & &) t)
      ((g-boolean &) (booleanp obj))
      ((g-var &) t)
      ((g-concrete y) (equal y obj))
      ((g-ite if then else)
       (or (and (shape-spec-obj-in-range-iff if t)
                (shape-spec-obj-in-range then obj))
           (and (shape-spec-obj-in-range-iff if nil)
                (shape-spec-obj-in-range else obj))))
      ((g-call & & &) nil)
      (& (and (consp obj)
              (shape-spec-obj-in-range (car x) (car obj))
              (shape-spec-obj-in-range (cdr x) (cdr obj)))))))


(defun-nx shape-spec-slice-to-env (obj)
  (mv-let (bsl vsl) obj
    (cons bsl vsl)))

(defun-nx ss-append-envs (x y)
  (cons (append (car x) (car y))
        (append (cdr x) (cdr y))))





(define integer-env-slice ((vlist nat-listp)
                           (obj integerp))
  :guard-hints (("goal" :in-theory (enable nat-listp)))
  :returns (alist alistp)
  (if (atom vlist)
      nil
    (cons (cons (car vlist) (logbitp 0 obj))
          (integer-env-slice (cdr vlist) (ash obj -1))))
  ///
  (std::defret true-listp-integer-env-slice
    (true-listp alist)
    :rule-classes :type-prescription))



(define number-spec-env-slice ((nspec number-specp)
                               obj)
  :guard-hints (("goal" :in-theory (enable number-specp)))
  :returns (alist alistp)
  (b* ((obj (fix obj))
       (rn-bspec
        (integer-env-slice (car nspec) (numerator (realpart obj))))
       (rd-bspec
        (integer-env-slice (cadr nspec) (denominator (realpart obj))))
       (in-bspec
        (integer-env-slice (caddr nspec) (numerator (imagpart obj))))
       (id-bspec
        (integer-env-slice (cadddr nspec) (denominator (imagpart obj)))))
    (append rn-bspec rd-bspec in-bspec id-bspec))
  ///
  (std::defret true-listp-number-spec-env-slice
    (true-listp alist)
    :rule-classes :type-prescription))

(define g-integer-env-slice ((sign natp)
                             (bits nat-listp)
                             var obj)
  :returns (mv (bvar-alist alistp)
               (gvar-alist alistp))
  (b* ((obj (ifix obj))
       (slice (integer-env-slice bits (loghead (len bits) obj)))
       (rest (logtail (len bits) obj))
       (signval (< rest 0)))
    (mv (cons (cons sign signval)
              slice)
        (list (cons var rest))))
  ///
  (std::defret true-listp-of-g-integer-env-slice-bvar-alist
    (true-listp bvar-alist)
    :rule-classes :type-prescription)
  (std::defret true-listp-of-g-integer-env-slice-gvar-alist
    (true-listp gvar-alist)
    :rule-classes :type-prescription))

(defines shape-spec-arbitrary-slice
  :verify-guards nil
  (define shape-spec-arbitrary-slice ((x shape-specp))
    :returns (mv (bvar-alist alistp)
                 (gvar-alist alistp))
    (if (atom x)
        (mv nil nil)
      (pattern-match x
        ((g-number nspec)
         (mv (number-spec-env-slice nspec 0) nil))
        ((g-integer sign bits var)
         (g-integer-env-slice sign bits var 0))
        ((g-integer? sign bits var intp)
         (mv-let (bsl vsl)
           (g-integer-env-slice sign bits var 0)
           (mv (cons (cons intp t) bsl) vsl)))
        ((g-boolean n) (mv (list (cons n nil)) nil))
        ((g-var v) (mv nil (list (cons v nil))))
        ((g-ite if then else)
         (b* (((mv if-bsl if-vsl)
               (shape-spec-arbitrary-slice if))
              ((mv then-bsl then-vsl)
               (shape-spec-arbitrary-slice then))
              ((mv else-bsl else-vsl)
               (shape-spec-arbitrary-slice else)))
           (mv (append if-bsl then-bsl else-bsl)
               (append if-vsl then-vsl else-vsl))))
        ((g-concrete &) (mv nil nil))
        ((g-call & args &) (shape-spec-list-arbitrary-slice args))
        (& (b* (((mv car-bsl car-vsl)
                 (shape-spec-arbitrary-slice (car x)))
                ((mv cdr-bsl cdr-vsl)
                 (shape-spec-arbitrary-slice (cdr x))))
             (mv (append car-bsl cdr-bsl)
                 (append car-vsl cdr-vsl)))))))

  (define shape-spec-list-arbitrary-slice ((x shape-spec-listp))
    :returns (mv (bvar-alist alistp)
                 (gvar-alist alistp))
    (if (atom x)
        (mv nil nil)
      (b* (((mv bsl1 vsl1) (shape-spec-arbitrary-slice (car x)))
           ((mv bsl2 vsl2) (shape-spec-list-arbitrary-slice (cdr x))))
        (mv (append bsl1 bsl2)
            (append vsl1 vsl2)))))
  ///

  (defthm-shape-spec-flag
    (defthm true-listp-shape-spec-arbitrary-slice-1
      (true-listp (mv-nth 1 (shape-spec-arbitrary-slice x)))
      :hints ('(:expand ((shape-spec-arbitrary-slice x))))
      :flag ss
      :rule-classes :type-prescription)
    (defthm true-listp-shape-spec-list-arbitrary-slice-1
      (true-listp (mv-nth 1 (shape-spec-list-arbitrary-slice x)))
      :flag list
      :rule-classes :type-prescription))

  (defthm-shape-spec-flag
    (defthm true-listp-shape-spec-arbitrary-slice-0
      (true-listp (mv-nth 0 (shape-spec-arbitrary-slice x)))
      :hints ('(:expand ((shape-spec-arbitrary-slice x))))
      :flag ss
      :rule-classes :type-prescription)
    (defthm true-listp-shape-spec-list-arbitrary-slice-0
      (true-listp (mv-nth 0 (shape-spec-list-arbitrary-slice x)))
      :flag list
      :rule-classes :type-prescription))


  (verify-guards shape-spec-arbitrary-slice
    :hints(("Goal" :in-theory (enable shape-specp
                                      shape-spec-listp)))))

(define shape-spec-iff-env-slice ((x shape-specp) obj)
  :returns (mv (bvar-alist alistp)
               (gvar-alist alistp))
  :verify-guards nil
  (if (atom x)
      (mv nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv (number-spec-env-slice nspec 0) nil))
      ((g-integer sign bits var)
       (g-integer-env-slice sign bits var 0))
      ((g-integer? sign bits var intp)
       (mv-let (bsl vsl)
         (g-integer-env-slice sign bits var 0)
         (if obj
             (mv (cons (cons intp t) bsl) vsl)
           (mv (cons (cons intp nil) bsl)
               (list (cons var nil))))))
      ((g-boolean n) (mv (list (cons n (bool-fix obj))) nil))
      ((g-var v) (mv nil (list (cons v (bool-fix obj)))))
      ((g-ite if then else)
       (b* (((mv then-bslice then-vslice)
             (shape-spec-iff-env-slice then obj))
            ((mv else-bslice else-vslice)
             (shape-spec-iff-env-slice else obj))
            (then-ok (shape-spec-obj-in-range-iff then obj))
            ((mv if-bslice if-vslice)
             (shape-spec-iff-env-slice if then-ok)))
         (mv (append if-bslice then-bslice else-bslice)
             (append if-vslice then-vslice else-vslice))))
      ((g-concrete &) (mv nil nil))
      ((g-call & args &)
       (shape-spec-list-arbitrary-slice args))
      (& (b* (((mv car-bsl car-vsl)
               (shape-spec-arbitrary-slice (car x)))
              ((mv cdr-bsl cdr-vsl)
               (shape-spec-arbitrary-slice (cdr x))))
           (mv (append car-bsl cdr-bsl)
               (append car-vsl cdr-vsl))))))
  ///
  (std::defret true-listp-of-shape-spec-iff-env-slice-bvar-alist
    (true-listp bvar-alist)
    :rule-classes :type-prescription)

  (std::defret true-listp-of-shape-spec-iff-env-slice-gvar-alist
    (true-listp gvar-alist)
    :rule-classes :type-prescription)

  (verify-guards shape-spec-iff-env-slice
    :hints(("Goal" :in-theory (enable shape-specp))))

  (fty::deffixcong iff equal (shape-spec-iff-env-slice x obj) obj))

(define shape-spec-env-slice ((x shape-specp) obj)
  :returns (mv (bvar-alist alistp)
               (gvar-alist alistp))
  :verify-guards nil
  (if (atom x)
      (mv nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv (number-spec-env-slice nspec obj) nil))
      ((g-integer sign bits var)
       (g-integer-env-slice sign bits var obj))
      ((g-integer? sign bits var intp)
       (mv-let (bsl vsl)
         (g-integer-env-slice sign bits var obj)
         (if (integerp obj)
             (mv (cons (cons intp t) bsl) vsl)
           (mv (cons (cons intp nil) bsl)
               (list (cons var obj))))))
      ((g-boolean n)
       (mv (list (cons n obj))
           nil))
      ((g-var v) (mv nil (list (cons v obj))))
      ((g-ite if then else)
       (b* (((mv then-bslice then-vslice)
             (shape-spec-env-slice then obj))
            ((mv else-bslice else-vslice)
             (shape-spec-env-slice else obj))
            (then-ok (shape-spec-obj-in-range then obj))
            ((mv if-bslice if-vslice)
             (shape-spec-iff-env-slice if then-ok)))
         (mv (append if-bslice then-bslice else-bslice)
             (append if-vslice then-vslice else-vslice))))
      ((g-concrete &) (mv nil nil))
      ((g-call & args &)
       (shape-spec-list-arbitrary-slice args))
      (& (b* (((mv car-bslice car-vslice)
               (shape-spec-env-slice (car x) (ec-call (car obj))))
              ((mv cdr-bslice cdr-vslice)
               (shape-spec-env-slice (cdr x) (ec-call (cdr obj)))))
           (mv (append car-bslice cdr-bslice)
               (append car-vslice cdr-vslice))))))
  ///
  (std::defret true-listp-shape-spec-env-slice-1
    (true-listp bvar-alist)
    :rule-classes :type-prescription)

  (std::defret true-listp-shape-spec-env-slice-2
    (true-listp gvar-alist)
    :rule-classes :type-prescription)

  (verify-guards shape-spec-env-slice
    :hints(("Goal" :in-theory (enable shape-specp)))))






(define shape-spec-bindingsp (x)
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (variablep (caar x))
         (consp (cdar x))
         (shape-specp (cadar x))
         (shape-spec-bindingsp (cdr x)))))


(local
 (defthm nat-listp-true-listp
   (implies (nat-listp x)
            (true-listp x))
   :hints(("Goal" :in-theory (enable nat-listp)))
   :rule-classes (:rewrite :forward-chaining)))


(defund number-spec-indices (nspec)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints (("goal" :in-theory (enable number-specp)))))
  (append (car nspec)
          (cadr nspec)
          (caddr nspec)
          (cadddr nspec)))


(mutual-recursion
 (defun shape-spec-indices (x)
   (declare (xargs :guard (shape-specp x)
                   :verify-guards nil))
   (if (atom x)
       nil
     (pattern-match x
       ((g-number nspec)
        (number-spec-indices nspec))
       ((g-integer sign bits &)
        (cons sign bits))
       ((g-integer? sign bits & intp)
        (list* intp sign bits))
       ((g-boolean n) (list n))
       ((g-var &) nil)
       ((g-ite if then else)
        (append (shape-spec-indices if)
                (shape-spec-indices then)
                (shape-spec-indices else)))
       ((g-concrete &) nil)
       ((g-call & args &) (shape-spec-list-indices args))
       (& (append (shape-spec-indices (car x))
                  (shape-spec-indices (cdr x)))))))
 (defun shape-spec-list-indices (x)
   (declare (xargs :guard (shape-spec-listp x)))
   (if (atom x)
       nil
     (append (shape-spec-indices (car x))
             (shape-spec-list-indices (cdr x))))))


(defund numlist-to-vars (lst)
  (declare (xargs :guard (nat-listp lst)
                  :guard-hints (("goal" :in-theory (enable nat-listp)))))
  (if (atom lst)
      nil
    (cons (bfr-var (lnfix (car lst)))
          (numlist-to-vars (cdr lst)))))

(defund num-spec-to-num-gobj (nspec)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints (("goal" :in-theory (enable number-specp)))))
  (cons (numlist-to-vars (car nspec))
        (and (consp (cdr nspec))
             (cons (numlist-to-vars (cadr nspec))
                   (and (consp (cddr nspec))
                        (cons (numlist-to-vars (caddr nspec))
                              (and (consp (cdddr nspec))
                                   (list (numlist-to-vars
                                          (cadddr nspec))))))))))

(mutual-recursion
 (defun shape-spec-to-gobj (x)
   (declare (xargs :guard (shape-specp x)
                   :guard-hints (("goal" :in-theory (enable shape-specp
                                                            shape-spec-listp)))))
   (if (atom x)
       x
     (pattern-match x
       ((g-number nspec)
        (g-number (num-spec-to-num-gobj nspec)))
       ((g-integer sign bits var)
        (g-apply 'logapp
                 (list (len bits)
                       (g-number (list (bfr-logapp-nus
                                        (len bits) (numlist-to-vars bits) nil)))
                       (g-apply 'int-set-sign
                                (list (g-boolean (bfr-var (lnfix sign)))
                                      (g-var var))))))
       ((g-integer? sign bits var intp)
        (g-apply 'maybe-integer
                 (list
                  (g-apply 'logapp
                           (list (len bits)
                                 (g-number (list (bfr-logapp-nus
                                                  (len bits) (numlist-to-vars bits) nil)))
                                 (g-apply 'int-set-sign
                                          (list (g-boolean (bfr-var (lnfix sign)))
                                                (g-var var)))))
                  (g-var var)
                  (g-boolean (bfr-var (lnfix intp))))))
       ((g-boolean n) (g-boolean (bfr-var (lnfix n))))
       ((g-var &) x)
       ((g-ite if then else)
        (g-ite (shape-spec-to-gobj if)
               (shape-spec-to-gobj then)
               (shape-spec-to-gobj else)))
       ((g-concrete &) x)
       ((g-call fn args &) (g-apply fn (shape-spec-to-gobj-list args)))
       (& (gl-cons (shape-spec-to-gobj (car x))
                   (shape-spec-to-gobj (cdr x)))))))
 (defun shape-spec-to-gobj-list (x)
   (declare (xargs :guard (shape-spec-listp x)))
   (if (atom x)
       nil
     (cons (shape-spec-to-gobj (car x))
           (shape-spec-to-gobj-list (cdr x))))))
