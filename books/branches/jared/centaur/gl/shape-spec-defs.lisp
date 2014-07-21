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

; cert_param: (non-acl2r)

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defund nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))


;; An shape spec is an object that is similar to a g object, but a) where there
;; would be BDDs in a g object, there are natural numbers in an shape spec, and
;; b) no G-APPLY constructs are allowed in an shape spec.

(defund number-specp (nspec)
  (declare (xargs :guard t))
  (and (consp nspec)
       (nat-listp (car nspec))
       (if (atom (cdr nspec))
           (not (cdr nspec))
         (and (nat-listp (cadr nspec))
              (if (atom (cddr nspec))
                  (not (cddr nspec))
                (and (nat-listp (caddr nspec))
                     (if (atom (cdddr nspec))
                         (not (cdddr nspec))
                         (and (nat-listp (cadddr nspec))
                              (not (cddddr nspec))))))))))


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



(mutual-recursion
 (defun shape-specp (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (if (atom x)
       (and (not (g-keyword-symbolp x))
            (not (member x '(:g-integer :g-integer? :g-call))))
     (case (tag x)
       (:g-number (number-specp (g-number->num x)))
       (:g-integer (and (natp (g-integer->sign x))
                        (nat-listp (g-integer->bits x))))
       (:g-integer? (and (natp (g-integer?->sign x))
                         (nat-listp (g-integer?->bits x))
                         (natp (g-integer?->intp x))))
       (:g-boolean (natp (g-boolean->bool x)))
       (:g-concrete t)
       (:g-var t)
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
                       (shape-specp (cdr x)))))))
 (defun shape-spec-listp (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (if (atom x)
       (eq x nil)
     (and (shape-specp (car x))
          (shape-spec-listp (cdr x))))))

(in-theory (disable shape-specp shape-spec-listp))



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




(defund shape-spec-obj-in-range-iff (x obj)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints(("Goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      (iff x obj)
    (pattern-match x
      ((g-number &)
       obj)
      ((g-integer & & &) obj)
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
      (& obj))))

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
           (and (natural-in-range (cadr nspec) (denominator (realpart obj)))
                (if (consp (cddr nspec))
                    (and (integer-in-range
                          (caddr nspec) (numerator (imagpart obj)))
                         (if (consp (cdddr nspec))
                             (natural-in-range
                              (cadddr nspec) (denominator (imagpart obj)))
                           (eql (denominator (imagpart obj)) 1)))
                  (rationalp obj)))
         (integerp obj))))

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
  (mv-let (ok bsl vsl) obj
    (declare (ignore ok))
    (cons bsl vsl)))

(defun-nx ss-append-envs (x y)
  (cons (append (car x) (car y))
        (append (cdr x) (cdr y))))





(defund integer-env-slice (vlist obj)
  (declare (xargs :guard (and (nat-listp vlist)
                              (integerp obj))
                  :guard-hints(("Goal" :in-theory (enable nat-listp)))))
  (if (atom vlist)
      (mv (eql obj 0) nil)
    (if (atom (cdr vlist))
        (if (eql obj 0)
            (mv t (list (cons (car vlist) nil)))
          (mv (eql obj -1) (list (cons (car vlist) t))))
      (mv-let (rest-ok rest-bslice)
        (integer-env-slice (cdr vlist) (ash obj -1))
        (mv rest-ok (cons (cons (car vlist) (logbitp 0 obj)) rest-bslice))))))

(local
 (defthm true-listp-integer-env-slice
   (true-listp (mv-nth 1 (integer-env-slice vlist obj)))
   :hints(("Goal" :in-theory (enable integer-env-slice)))))

(defund natural-env-slice (vlist obj)
  (declare (xargs :guard (and (nat-listp vlist)
                              (integerp obj))
                  :guard-hints(("Goal" :in-theory (enable nat-listp)))))
  (if (atom vlist)
      (mv (eql obj 0) nil)
    (mv-let (rest-ok rest-bslice)
      (natural-env-slice (cdr vlist) (ash obj -1))
      (mv rest-ok (cons (cons (car vlist) (logbitp 0 obj)) rest-bslice)))))

(local
 (defthm true-listp-natural-env-slice
   (true-listp (mv-nth 1 (natural-env-slice vlist obj)))
   :hints(("Goal" :in-theory (enable natural-env-slice)))))

(defund number-spec-env-slice (nspec obj)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints(("Goal" :in-theory (enable number-specp)))))
  (mv-let (rn-ok rn-bspec)
    (integer-env-slice (car nspec) (numerator (realpart (fix obj))))
    (if (consp (cdr nspec))
        (mv-let (rd-ok rd-bspec)
          (natural-env-slice (cadr nspec) (denominator (realpart (fix obj))))
          (if (consp (cddr nspec))
              (mv-let (in-ok in-bspec)
                (integer-env-slice
                 (caddr nspec) (numerator (imagpart (fix obj))))
                (if (consp (cdddr nspec))
                    (mv-let (id-ok id-bspec)
                      (natural-env-slice
                       (cadddr nspec)
                       (denominator (imagpart (fix obj))))
                      (mv (and (acl2-numberp obj)
                               rn-ok rd-ok in-ok id-ok)
                          (append rn-bspec rd-bspec
                                  in-bspec id-bspec)))
                  (mv (and (acl2-numberp obj)
                           (eql (denominator (imagpart obj)) 1)
                           rn-ok rd-ok in-ok)
                      (append rn-bspec rd-bspec
                              in-bspec))))
            (mv (and (acl2-numberp obj)
                     (eql (imagpart obj) 0)
                     rn-ok rd-ok)
                (append rn-bspec rd-bspec))))
      (mv (and (acl2-numberp obj)
               (eql (denominator (realpart obj)) 1)
               (eql (imagpart obj) 0) rn-ok)
          rn-bspec))))

(local
 (defthm true-listp-number-spec-env-slice-1
   (true-listp (mv-nth 1 (number-spec-env-slice nspec obj)))
   :hints(("Goal" :in-theory (enable number-spec-env-slice)))))

(defun g-integer-env-slice (sign bits var obj)
  (declare (xargs :guard (and (natp sign) (nat-listp bits))))
  (b* ((obj (ifix obj))
       ((mv & slice) (natural-env-slice bits (loghead (len bits) obj)))
       (rest (logtail (len bits) obj))
       (signval (< rest 0)))
    (mv (cons (cons sign signval)
              slice)
        (list (cons var rest)))))

(mutual-recursion
 (defun shape-spec-arbitrary-slice (x)
   (declare (xargs :guard (shape-specp x)
                   :verify-guards nil))
   (if (atom x)
       (mv nil nil)
     (pattern-match x
       ((g-number nspec)
        (mv-let (ok bsl)
          (number-spec-env-slice nspec 0)
          (declare (ignore ok))
          (mv bsl nil)))
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

 (defun shape-spec-list-arbitrary-slice (x)
   (declare (xargs :guard (shape-spec-listp x)))
   (if (atom x)
       (mv nil nil)
     (b* (((mv bsl1 vsl1) (shape-spec-arbitrary-slice (car x)))
          ((mv bsl2 vsl2) (shape-spec-list-arbitrary-slice (cdr x))))
       (mv (append bsl1 bsl2)
           (append vsl1 vsl2))))))

(local
 (defthm-shape-spec-flag
   (defthm true-listp-shape-spec-arbitrary-slice-1
     (true-listp (mv-nth 1 (shape-spec-arbitrary-slice x)))
     :hints ('(:expand ((shape-spec-arbitrary-slice x))))
     :flag ss)
   (defthm true-listp-shape-spec-list-arbitrary-slice-1
     (true-listp (mv-nth 1 (shape-spec-list-arbitrary-slice x)))
     :flag list)))

(local
 (defthm-shape-spec-flag
   (defthm true-listp-shape-spec-arbitrary-slice-0
     (true-listp (mv-nth 0 (shape-spec-arbitrary-slice x)))
     :hints ('(:expand ((shape-spec-arbitrary-slice x))))
     :flag ss)
   (defthm true-listp-shape-spec-list-arbitrary-slice-0
     (true-listp (mv-nth 0 (shape-spec-list-arbitrary-slice x)))
     :flag list)))


(verify-guards shape-spec-arbitrary-slice
               :hints(("Goal" :in-theory (enable shape-specp
                                                 shape-spec-listp))))

(in-theory (disable shape-spec-arbitrary-slice shape-spec-list-arbitrary-slice))

(defund shape-spec-iff-env-slice (x obj)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      (mv (iff x obj) nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv-let (ok bsl)
         (number-spec-env-slice nspec 0)
         (declare (ignore ok))
         (mv obj bsl nil)))
      ((g-integer sign bits var)
       (mv-let (bsl vsl)
         (g-integer-env-slice sign bits var 0)
         (mv obj bsl vsl)))
      ((g-integer? sign bits var intp)
       (mv-let (bsl vsl)
         (g-integer-env-slice sign bits var 0)
         (if obj
             (mv t (cons (cons intp t) bsl) vsl)
           (mv t (cons (cons intp nil) bsl)
               (list (cons var nil))))))
      ((g-boolean n) (mv t (list (cons n obj)) nil))
      ((g-var v) (mv t nil (list (cons v obj))))
      ((g-ite if then else)
       (b* (((mv then-ok then-bslice then-vslice)
             (shape-spec-iff-env-slice then obj))
            ((mv else-ok else-bslice else-vslice)
             (shape-spec-iff-env-slice else obj))
            ((mv if-t-ok if-t-bslice if-t-vslice)
             (shape-spec-iff-env-slice if t))
            ((mv if-nil-ok if-nil-bslice if-nil-vslice)
             (shape-spec-iff-env-slice if nil)))
         (if (and then-ok if-t-ok)
             (mv t (append if-t-bslice then-bslice else-bslice)
                 (append if-t-vslice then-vslice else-vslice))
           (mv (and else-ok if-nil-ok)
               (append if-nil-bslice then-bslice else-bslice)
               (append if-nil-vslice then-vslice else-vslice)))))
      ((g-concrete y) (mv (iff y obj) nil nil))
      ((g-call & args &)
       (mv-let (bsl vsl)
         (shape-spec-list-arbitrary-slice args)
         (mv nil bsl vsl)))
      (& (b* (((mv car-bsl car-vsl)
               (shape-spec-arbitrary-slice (car x)))
              ((mv cdr-bsl cdr-vsl)
               (shape-spec-arbitrary-slice (cdr x))))
           (mv obj
               (append car-bsl cdr-bsl)
               (append car-vsl cdr-vsl)))))))

(local
 (defthm true-listp-shape-spec-iff-env-slice-1
   (true-listp (mv-nth 1 (shape-spec-iff-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice)))))

(local
 (defthm true-listp-shape-spec-iff-env-slice-2
   (true-listp (mv-nth 2 (shape-spec-iff-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice)))))

(verify-guards shape-spec-iff-env-slice
               :hints(("Goal" :in-theory (enable shape-specp))))

(defund shape-spec-env-slice (x obj)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      (mv (equal x obj) nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv-let (ok bspec)
         (number-spec-env-slice nspec obj)
         (mv ok bspec nil)))
      ((g-integer sign bits var)
       (mv-let (bsl vsl)
         (g-integer-env-slice sign bits var obj)
         (mv (integerp obj) bsl vsl)))
      ((g-integer? sign bits var intp)
       (mv-let (bsl vsl)
         (g-integer-env-slice sign bits var obj)
         (if (integerp obj)
             (mv t (cons (cons intp t) bsl) vsl)
           (mv t (cons (cons intp nil) bsl)
               (list (cons var obj))))))
      ((g-boolean n)
       (mv (booleanp obj)
           (list (cons n obj))
           nil))
      ((g-var v) (mv t nil (list (cons v obj))))
      ((g-ite if then else)
       (b* (((mv then-ok then-bslice then-vslice)
             (shape-spec-env-slice then obj))
            ((mv else-ok else-bslice else-vslice)
             (shape-spec-env-slice else obj))
            ((mv if-t-ok if-t-bslice if-t-vslice)
             (shape-spec-iff-env-slice if t))
            ((mv if-nil-ok if-nil-bslice if-nil-vslice)
             (shape-spec-iff-env-slice if nil)))
         (if (and then-ok if-t-ok)
             (mv t (append if-t-bslice then-bslice else-bslice)
                 (append if-t-vslice then-vslice else-vslice))
           (mv (and else-ok if-nil-ok)
               (append if-nil-bslice then-bslice else-bslice)
               (append if-nil-vslice then-vslice else-vslice)))))
      ((g-concrete y)
       (mv (equal obj y) nil nil))
      ((g-call & args &)
       (mv-let (bsl vsl)
         (shape-spec-list-arbitrary-slice args)
         (mv nil bsl vsl)))
      (& (b* (((mv car-ok car-bslice car-vslice)
               (shape-spec-env-slice (car x) (ec-call (car obj))))
              ((mv cdr-ok cdr-bslice cdr-vslice)
               (shape-spec-env-slice (cdr x) (ec-call (cdr obj)))))
           (mv (and (consp obj) car-ok cdr-ok)
               (append car-bslice cdr-bslice)
               (append car-vslice cdr-vslice)))))))

(local
 (defthm true-listp-shape-spec-env-slice-1
   (true-listp (mv-nth 1 (shape-spec-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice)))))

(local
 (defthm true-listp-shape-spec-env-slice-2
   (true-listp (mv-nth 2 (shape-spec-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice)))))

(verify-guards shape-spec-env-slice
               :hints(("Goal" :in-theory (enable shape-specp))))




(defun shape-spec-bindingsp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (not (keywordp (caar x)))
         (caar x)
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
          (and (consp (cdr nspec))
               (append (cadr nspec)
                       (and (consp (cddr nspec))
                            (append (caddr nspec)
                                    (and (consp (cdddr nspec))
                                         (cadddr nspec))))))))


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
    (cons (bfr-var (car lst))
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
                                (list (g-boolean (bfr-var sign))
                                      (g-var var))))))
       ((g-integer? sign bits var intp)
        (g-apply 'maybe-integer
                 (list
                  (g-apply 'logapp
                           (list (len bits)
                                 (g-number (list (bfr-logapp-nus
                                                  (len bits) (numlist-to-vars bits) nil)))
                                 (g-apply 'int-set-sign
                                          (list (g-boolean (bfr-var sign))
                                                (g-var var)))))
                  (g-var var)
                  (g-boolean (bfr-var intp)))))
       ((g-boolean n) (g-boolean (bfr-var n)))
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
