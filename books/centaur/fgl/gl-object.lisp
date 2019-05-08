; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "arith-base")
(local (std::add-default-post-define-hook :fix))

(defprod g-map-tag
  ((index acl2::maybe-natp :rule-classes :type-prescription))
  :layout :tree
  :tag :g-map
  ///
  (defthm car-of-g-map-tag-fix
    (equal (car (g-map-tag-fix x)) :g-map)
    :hints(("Goal" :in-theory (enable g-map-tag-fix)))))


(defmacro gl-object-keys ()
  ''(:g-concrete
     :g-boolean
     :g-integer
     :g-ite
     :g-apply
     :g-var
     :g-map))

(fty::deftypes gl-object
  (fty::defflexsum gl-object
    (:g-concrete
     :cond (or (atom x)
               (eq (car x) :g-concrete))
     :shape (and (not (member x (gl-object-keys)))
                 (or (atom x)
                     (consp (cdr x))
                     (member (cdr x) (gl-object-keys))))
     :fields ((val :acc-body
                   (if (consp x) (cdr x) x)))
     :ctor-body (if (and (atom val)
                         (not (and (symbolp val) ;; optimization
                                   (member-eq val (gl-object-keys)))))
                    val
                  (cons :g-concrete val))
     :type-name g-concrete)
    (:g-boolean
     :cond (eq (car x) :g-boolean)
     :fields ((bool :acc-body (cdr x)))
     :ctor-body (cons :g-boolean bool)
     :type-name g-boolean)
    (:g-integer
     :cond (eq (car x) :g-integer)
     :fields ((bits :acc-body (cdr x) :type true-listp))
     :ctor-body (cons :g-integer bits)
     :type-name g-integer)
    (:g-ite
     :cond (eq (car x) :g-ite)
     :shape (and (consp (cdr x))
                 (consp (cddr x)))
     :fields ((test :type gl-object :acc-body (cadr x))
              (then :type gl-object :acc-body (caddr x))
              (else :type gl-object :acc-body (cdddr x)))
     :ctor-body (cons :g-ite (cons test (cons then else)))
     :type-name g-ite)
    (:g-apply
     :cond (eq (car x) :g-apply)
     :shape (consp (cdr x))
     :fields ((fn :type pseudo-fnsym :acc-body (cadr x))
              (args :type gl-objectlist :acc-body (cddr x)))
     :ctor-body (cons :g-apply (cons fn args))
     :type-name g-apply)
    (:g-var
     :cond (eq (car x) :g-var)
     :fields ((name :type pseudo-var :acc-body (cdr x)))
     :ctor-body (cons :g-var name)
     :type-name g-var)
    (:g-map
     :cond (and (consp (car x))
                (eq (caar x) :g-map))
     :fields ((tag :type g-map-tag :acc-body (car x))
              (alist :type gl-object-alist :acc-body (cdr x)))
     :ctor-body (cons tag alist)
     :type-name g-map)

    (:g-cons
     :fields ((car :type gl-object :acc-body (car x))
              (cdr :type gl-object :acc-body (cdr x)))
     :ctor-body (cons car cdr)
     :type-name g-cons)

    :post-pred-events
    ((local (defthm gl-object-p-of-cons
              (implies (and (gl-object-p x)
                            (gl-object-p y))
                       (gl-object-p (cons x y)))
              :hints (("goal" :expand ((gl-object-p x)
                                       (gl-object-p (cons x y)))))))
     (local (defthm car-not-g-map-when-gl-object-p
              (implies (gl-object-p x)
                       (not (equal (car x) :g-map)))
              :hints (("goal" :expand ((gl-object-p x)
                                       (gl-object-p (car x)))))))))
  (fty::deflist gl-objectlist :elt-type gl-object :true-listp t :elementp-of-nil t)
  (fty::defmap gl-object-alist :val-type gl-object :true-listp nil))
     

(defsection g-int
  :parents (shape-specs)
  :short "Create a g-binding for an integer."
  :long "<p>This is a low-level way to create a custom shape specifier for a
signed integer.  You might generally prefer higher-level tools like @(see
auto-bindings).</p>"

  (defun g-int (start by n)
    (declare (xargs :guard (and (acl2-numberp start)
                                (acl2-numberp by)
                                (natp n))))
    (g-integer (numlist start by n))))


(fty::defmap gl-object-bindings :key-type pseudo-var-p :val-type gl-object :true-listp t
  ///
  (defthm gl-object-bindings-p-of-append
    (implies (and (gl-object-bindings-p x)
                  (gl-object-bindings-p y))
             (gl-object-bindings-p (append x y)))))


(define mk-g-boolean (x)
  :returns (bool gl-object-p)
  (if (booleanp x)
      (g-concrete x)
    (g-boolean x)))

(define mk-g-integer ((x true-listp))
  :returns (int gl-object-p :hints(("Goal" :in-theory (enable gl-object-p))))
  (if (boolean-listp (mbe :logic (true-list-fix x) :exec x))
      (g-concrete (bools->int x))
    (g-integer x)))

(define mk-g-cons ((x gl-object-p)
                   (y gl-object-p))
  :returns (cons gl-object-p :hints(("Goal" :in-theory (enable gl-object-p))))
  (if (and (gl-object-case x :g-concrete)
           (gl-object-case y :g-concrete))
      (g-concrete (cons (g-concrete->val x)
                        (g-concrete->val y)))
    (g-cons x y)))

;; (defines gl-object-symbolic-boolean-free
;;   (define gl-object-symbolic-boolean-free ((x gl-object-p))
;;     :measure (gl-object-count x)
;;     (gl-object-case x
;;       :g-integer (not x.bits)
;;       :g-boolean nil
;;       :g-concrete t
;;       :g-ite (and (gl-object-symbolic-boolean-free x.test)
;;                   (gl-object-symbolic-boolean-free x.then)
;;                   (gl-object-symbolic-boolean-free x.else))
;;       :g-var t
;;       :g-cons (and (gl-object-symbolic-boolean-free x.car)
;;                    (gl-object-symbolic-boolean-free x.cdr))
;;       :g-apply (gl-objectlist-symbolic-boolean-free x.args)))
;;   (define gl-objectlist-symbolic-boolean-free ((x gl-objectlist-p))
;;     :measure (gl-objectlist-count x)
;;     (if (atom x)
;;         t
;;       (and (gl-object-symbolic-boolean-free (car x))
;;            (gl-objectlist-symbolic-boolean-free (cdr x)))))
;;   ///
;;   (fty::deffixequiv-mutual gl-object-symbolic-boolean-free
;;     :hints (("goal" :expand ((gl-objectlist-fix x))))))


(define gobj-syntactic-booleanp ((x gl-object-p))
  (gl-object-case x
    :g-concrete (booleanp x.val)
    :g-boolean t
    :otherwise nil))

(define gobj-syntactic-boolean-fix ((x gl-object-p))
  :returns (mv okp (new-x gl-object-p))
  (gl-object-case x
    :g-concrete (mv t (and x.val t))
    :g-boolean (mv t (gl-object-fix x))
    :g-integer (mv t t)
    :g-cons (mv t t)
    :otherwise (mv nil nil))
  ///
  (defret gobj-syntactic-booleanp-of-<fn>
    (gobj-syntactic-booleanp new-x)
    :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp)))))


(define gobj-syntactic-boolean->bool ((x gl-object-p))
  :guard (gobj-syntactic-booleanp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-booleanp)))
  :returns (bfr)
  (gl-object-case x
    :g-concrete x.val
    :otherwise (and (mbt (gl-object-case x :g-boolean))
                    (g-boolean->bool x))))

(define gobj-syntactic-integerp ((x gl-object-p))
  (gl-object-case x
    :g-concrete (integerp x.val)
    :g-integer t
    :otherwise nil))

(defthmd gl-object-p-when-integerp
  (implies (integerp x)
           (gl-object-p x))
  :hints(("Goal" :in-theory (enable gl-object-p))))

(defthmd gl-object-kind-when-integerp
  (implies (integerp x)
           (equal (gl-object-kind x) :g-concrete))
  :hints(("Goal" :in-theory (enable gl-object-kind))))

(defthmd g-concrete->val-when-integerp
  (implies (integerp x)
           (equal (g-concrete->val x) x))
  :hints(("Goal" :in-theory (enable g-concrete->val))))

(define gobj-syntactic-integer-fix ((x gl-object-p))
  :returns (mv okp
               (new-x gl-object-p))
  :prepwork ((local (in-theory (enable gl-object-p-when-integerp
                                       gl-object-kind-when-integerp
                                       g-concrete->val-when-integerp))))
  (gl-object-case x
    :g-concrete (mv t (ifix x.val))
    :g-boolean (mv t 0)
    :g-integer (mv t (gl-object-fix x))
    :g-cons (mv t 0)
    :otherwise (mv nil 0))
  ///
  (defret gobj-syntactic-integerp-of-<fn>
    (gobj-syntactic-integerp new-x)
    :hints(("Goal" :in-theory (enable gobj-syntactic-integerp)))))

(define gobj-syntactic-integer->bits ((x gl-object-p))
  :guard (gobj-syntactic-integerp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-integerp)))
  :returns (bfrlist true-listp :rule-classes :type-prescription)
  (gl-object-case x
    :g-concrete (int->bools x.val)
    :otherwise (and (mbt (gl-object-case x :g-integer))
                    (g-integer->bits x))))



(define gobj-syntactic-consp ((x gl-object-p))
  (gl-object-case x
    :g-concrete (consp x.val)
    :g-cons t
    :otherwise nil))

(define gobj-syntactic-listp ((x gl-object-p))
  (gl-object-case x
    :g-concrete (or (consp x.val) (not x.val))
    :g-cons t
    :otherwise nil))

(define gobj-syntactic-list-fix ((x gl-object-p))
  :returns (mv okp (new-x gl-object-p))
  (gl-object-case x
    :g-concrete (mv t (if (consp x.val) (gl-object-fix x) nil))
    :g-cons (mv t (gl-object-fix x))
    :g-integer (mv t nil)
    :g-boolean (mv t nil)
    :otherwise (mv nil nil))
  ///
  (defret gobj-syntactic-listp-of-<fn>
    (gobj-syntactic-listp new-x)
    :hints(("Goal" :in-theory (enable gobj-syntactic-listp)))))

(define gobj-syntactic-list->car ((x gl-object-p))
  :guard (gobj-syntactic-listp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-listp)))
  :returns (car gl-object-p)
  (gl-object-case x
    :g-concrete (g-concrete (car x.val))
    :otherwise (and (mbt (gl-object-case x :g-cons))
                    (g-cons->car x))))

(define gobj-syntactic-list->cdr ((x gl-object-p))
  :guard (gobj-syntactic-listp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-listp)))
  :returns (cdr gl-object-p)
  (gl-object-case x
    :g-concrete (g-concrete (cdr x.val))
    :otherwise (and (mbt (gl-object-case x :g-cons))
                    (g-cons->cdr x))))



