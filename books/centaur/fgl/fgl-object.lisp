; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "std/basic/two-nats-measure" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defprod g-map-tag
  ((index acl2::maybe-natp :rule-classes :type-prescription))
  :layout :tree
  :tag :g-map
  ///
  (defthm car-of-g-map-tag-fix
    (equal (car (g-map-tag-fix x)) :g-map)
    :hints(("Goal" :in-theory (enable g-map-tag-fix)))))


(defmacro fgl-object-keys ()
  ''(:g-concrete
     :g-boolean
     :g-integer
     :g-ite
     :g-apply
     :g-var
     :g-map))

(fty::deftypes fgl-object
  (fty::defflexsum fgl-object
    :parents (fgl)
    :short "FGL symbolic object type"
    :long "<p>An FGL symbolic object is the representation for symbolic data
inside the FGL interpreter.  There are several kinds of objects, including
concrete objects that simply represent a particular explicit value, bit-level
objects that represent some function resulting in a Boolean or
bitvector (integer), and termlike objects that represent free variables and
calls of arbitrary functions on symbolic objects.</p>

<p>Symbolic objects are evaluated using @(see fgl-object-eval).  This takes an
environment object of type @(see fgl-env) consisting of an alist mapping free
variables to their values, for evaluating @(see g-var) objects, and a Boolean
function environment for evaluating @(see g-boolean) and @(see g-integer)
objects.</p>

<p>The FGL object type is an <see topic='@(url fty::fty)'>FTY</see>-style
sum-of-products type.  That means any of the sum members listed above may be
used to construct an object of this type.  Functions that access FGL objects
must check which kind of object they have been passed.  The kind of a FGL object
may be accessed using the @('fgl-object-kind') function, but usually it is
easier to use the @('fgl-object-case') macro, which we illustrate using the
following examples:</p>
@({
;; If x is a g-concrete representing an integer, return its integer-length plus
;; one, else if it's a g-integer return the length of its bitlist, else NIL:
 (fgl-object-case x
    :g-concrete (and (integerp x.val) (+ 1 (integer-length x.val)))
    :g-integer (len x.bits)
    :otherwise nil)

;; Check whether x can be syntactically determined to be always non-NIL.
 (defun gobj-syntactically-nonnil (x)
   (fgl-object-case x
      :g-concrete (and x.val t)
      :g-integer  t
      :g-boolean  (eq x.bool t)
      :g-ite      (if (gobj-syntactically-nonnil x.test)
                      (gobj-syntactically-nonnil x.then)
                    (and (gobj-syntactically-nonnil x.then)
                         (gobj-syntactically-nonnil x.else)))
      :g-apply    nil
      :g-var      nil
      :g-cons     t
      :g-map      (and x.alist t)))

;; Check whether x is a g-concrete object.
  (fgl-object-case x :g-concrete)

;; Check whether x is either a g-concrete or g-boolean object.
  (fgl-object-case x '(:g-concrete :g-boolean))

 })

<p>The first two examples above show @('fgl-object-case') both
case-splitting between different kinds and also binding fields of @('x') using
dotted notation, e.g. @('x.bits') above is bound to @('(g-integer->bits x)').
The latter two show a special syntax that is a shortcut for checking the kind
of @('x').  Note that it is likely preferable to use @('(fgl-object-case
x :g-concrete)') rather than @('(eq (fgl-object-kind x) :g-concrete)'), even
though they have the same meaning, because the former will produce an error in
case you misspell @(':g-concrete').</p>
"
    (:g-concrete
     :short "FGL-object constructor for constant (quoted) objects."
     :long "<p>An object constructed as @('(g-concrete val)') evaluates to @('val').
            Atoms other than the FGL object keywords (listed below) are represented as themselves.
            Other objects are represented as @('(:g-concrete . obj)').</p>
            <p>The FGL object keywords are members of the list @('(fgl-object-keys)'), namely:</p>
            @(`(:code (fgl-object-keys))`)
            <p>All atoms other than these are FGL objects representing themselves.</p>"
     :cond (or (atom x)
               (eq (car x) :g-concrete))
     :shape (and (not (member x (fgl-object-keys)))
                 (or (atom x)
                     (consp (cdr x))
                     (member (cdr x) (fgl-object-keys))))
     :fields ((val :acc-body
                   (if (consp x) (cdr x) x)))
     :ctor-body (if (and (atom val)
                         (not (and (symbolp val) ;; optimization
                                   (member-eq val (fgl-object-keys)))))
                    val
                  (cons :g-concrete val))
     :type-name g-concrete)
    (:g-boolean
     :short "FGL object constructor for symbolic Boolean objects."
     :long "<p>An object constructed as @('(g-boolean bool)') evaluates to the
            value of the Boolean function @('bool') under the current
            Boolean function environment, evaluated by @(see bfr-eval).</p>"
     :cond (eq (car x) :g-boolean)
     :fields ((bool :acc-body (cdr x)))
     :ctor-body (cons :g-boolean bool)
     :type-name g-boolean)
    (:g-integer
     :short "FGL object constructor for symbolic integers, with Boolean functions representing the bits."
     :long "<p>An object constructed as @('(g-integer bits)') evaluates to the
            two's-complement integer formed by evaluating each Boolean function
            in the list @('bits') using @(see bfr-eval), and then converting
            that Boolean list to an integer using @(see bools->int).</p>"
     :cond (eq (car x) :g-integer)
     :fields ((bits :acc-body (cdr x) :type true-listp))
     :ctor-body (cons :g-integer bits)
     :type-name g-integer)
    (:g-ite
     :short "FGL object constructor for if-then-else objects."
     :long "<p>An object constructed as @('(g-ite test then else)') represents
            the if-then-else of the evaluations of sub-objects test, then, and
            else.</p>
            <p>This could simply be replaced by @('(g-apply 'if test then else)').</p>"
     :cond (eq (car x) :g-ite)
     :shape (and (consp (cdr x))
                 (consp (cddr x)))
     :fields ((test :type fgl-object :acc-body (cadr x))
              (then :type fgl-object :acc-body (caddr x))
              (else :type fgl-object :acc-body (cdddr x)))
     :ctor-body (cons :g-ite (cons test (cons then else)))
     :type-name g-ite)
    (:g-apply
     :short "FGL object constructor for function calls."
     :long "<p>An object constructed as @('(g-apply fn args)') represents the
            application of function symbol @('fn') to the evaluation of
            @('args'), which must be a list of FGL objects.</p>"
     :cond (eq (car x) :g-apply)
     :shape (consp (cdr x))
     :fields ((fn :type pseudo-fnsym :acc-body (cadr x))
              (args :type fgl-objectlist :acc-body (cddr x)))
     :ctor-body (cons :g-apply (cons fn args))
     :type-name g-apply)
    (:g-var
     :short "FGL object constructor for free variables."
     :long "<p>An object constructed as @('(g-var name)') simply evaluates to
            the binding of variable symbol @('name') in the free variable alist
            of the environment.</p>"
     :cond (eq (car x) :g-var)
     :fields ((name :type pseudo-var :acc-body (cdr x)))
     :ctor-body (cons :g-var name)
     :type-name g-var)
    (:g-map
     :short "FGL object constructor for fast alists and arrays."
     :long "<p>An object constructed as @('(g-map tag alist)') evaluates to the
            evaluation of @('alist') as a FGL object alist -- that is, a list of
            pairs where the keys are concrete objects which are not evaluated
            and the values are FGL objects.  The @('g-map') kind is used in
            fast-alist and @(see fgarray) primitives to offer constant-time
            lookups in fast alists and arrays.</p>"
     :cond (and (consp (car x))
                (eq (caar x) :g-map))
     :fields ((tag :type g-map-tag :acc-body (car x))
              (alist :type fgl-object-alist :acc-body (cdr x)))
     :ctor-body (cons tag alist)
     :type-name g-map)

    (:g-cons
     :short "FGL object constructor for conses."
     :long "<p>An object constructed as @('(g-cons car cdr)') evaluates to the
            cons of the evaluations of FGL objects @('car') and @('cdr').  This
            could be represented instead as @('(g-apply 'cons car cdr)'), but
            the @('g-cons') constructor saves memory by using only one cons in
            its representation, rather than four as would be used in the
            @('g-apply') version.</p>"
     :fields ((car :type fgl-object :acc-body (car x))
              (cdr :type fgl-object :acc-body (cdr x)))
     :ctor-body (cons car cdr)
     :type-name g-cons)

    :post-pred-events
    ((local (defthm fgl-object-p-of-cons
              (implies (and (fgl-object-p x)
                            (fgl-object-p y))
                       (fgl-object-p (cons x y)))
              :hints (("goal" :expand ((fgl-object-p x)
                                       (fgl-object-p (cons x y)))))))
     (local (defthm car-not-g-map-when-fgl-object-p
              (implies (fgl-object-p x)
                       (not (equal (car x) :g-map)))
              :hints (("goal" :expand ((fgl-object-p x)
                                       (fgl-object-p (car x)))))))))
  (fty::deflist fgl-objectlist :elt-type fgl-object :true-listp t :elementp-of-nil t
    :parents (fgl-object))
  (fty::defmap fgl-object-alist :val-type fgl-object :true-listp nil
    :parents (fgl-object)))

(fty::defmap fgl-object-bindings :key-type pseudo-var-p :val-type fgl-object :true-listp t
  ///
  (defthm fgl-object-bindings-p-of-append
    (implies (and (fgl-object-bindings-p x)
                  (fgl-object-bindings-p y))
             (fgl-object-bindings-p (append x y)))))


(define mk-g-boolean (x)
  :returns (bool fgl-object-p)
  (if (booleanp x)
      (g-concrete x)
    (g-boolean x)))

(define mk-g-integer ((x true-listp))
  :returns (int fgl-object-p :hints(("Goal" :in-theory (enable fgl-object-p))))
  (if (boolean-listp (mbe :logic (true-list-fix x) :exec x))
      (g-concrete (bools->int x))
    (g-integer x)))

(define mk-g-cons ((x fgl-object-p)
                   (y fgl-object-p))
  :returns (cons fgl-object-p :hints(("Goal" :in-theory (enable fgl-object-p))))
  (if (and (fgl-object-case x :g-concrete)
           (fgl-object-case y :g-concrete))
      (g-concrete (cons (g-concrete->val x)
                        (g-concrete->val y)))
    (g-cons x y)))




;; (defines fgl-object-symbolic-boolean-free
;;   (define fgl-object-symbolic-boolean-free ((x fgl-object-p))
;;     :measure (fgl-object-count x)
;;     (fgl-object-case x
;;       :g-integer (not x.bits)
;;       :g-boolean nil
;;       :g-concrete t
;;       :g-ite (and (fgl-object-symbolic-boolean-free x.test)
;;                   (fgl-object-symbolic-boolean-free x.then)
;;                   (fgl-object-symbolic-boolean-free x.else))
;;       :g-var t
;;       :g-cons (and (fgl-object-symbolic-boolean-free x.car)
;;                    (fgl-object-symbolic-boolean-free x.cdr))
;;       :g-apply (fgl-objectlist-symbolic-boolean-free x.args)))
;;   (define fgl-objectlist-symbolic-boolean-free ((x fgl-objectlist-p))
;;     :measure (fgl-objectlist-count x)
;;     (if (atom x)
;;         t
;;       (and (fgl-object-symbolic-boolean-free (car x))
;;            (fgl-objectlist-symbolic-boolean-free (cdr x)))))
;;   ///
;;   (fty::deffixequiv-mutual fgl-object-symbolic-boolean-free
;;     :hints (("goal" :expand ((fgl-objectlist-fix x))))))


(define gobj-syntactic-booleanp ((x fgl-object-p))
  (fgl-object-case x
    :g-concrete (booleanp x.val)
    :g-boolean t
    :otherwise nil))

(define gobj-syntactic-boolean-fix ((x fgl-object-p))
  :returns (mv okp (new-x fgl-object-p))
  (fgl-object-case x
    :g-concrete (mv t (and x.val t))
    :g-boolean (mv t (fgl-object-fix x))
    :g-integer (mv t t)
    :g-cons (mv t t)
    :otherwise (mv nil nil))
  ///
  (defret gobj-syntactic-booleanp-of-<fn>
    (gobj-syntactic-booleanp new-x)
    :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp)))))


(define gobj-syntactic-boolean->bool ((x fgl-object-p))
  :guard (gobj-syntactic-booleanp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-booleanp)))
  :returns (bfr)
  (fgl-object-case x
    :g-concrete x.val
    :otherwise (and (mbt (fgl-object-case x :g-boolean))
                    (g-boolean->bool x))))

(define gobj-syntactic-integerp ((x fgl-object-p))
  (fgl-object-case x
    :g-concrete (integerp x.val)
    :g-integer t
    :otherwise nil))

(defthmd fgl-object-p-when-integerp
  (implies (integerp x)
           (fgl-object-p x))
  :hints(("Goal" :in-theory (enable fgl-object-p))))

(defthmd fgl-object-kind-when-integerp
  (implies (integerp x)
           (equal (fgl-object-kind x) :g-concrete))
  :hints(("Goal" :in-theory (enable fgl-object-kind))))

(defthmd g-concrete->val-when-integerp
  (implies (integerp x)
           (equal (g-concrete->val x) x))
  :hints(("Goal" :in-theory (enable g-concrete->val))))

(define gobj-syntactic-integer-fix ((x fgl-object-p))
  :returns (mv okp
               (new-x fgl-object-p))
  :prepwork ((local (in-theory (enable fgl-object-p-when-integerp
                                       fgl-object-kind-when-integerp
                                       g-concrete->val-when-integerp))))
  (fgl-object-case x
    :g-concrete (mv t (ifix x.val))
    :g-boolean (mv t 0)
    :g-integer (mv t (fgl-object-fix x))
    :g-cons (mv t 0)
    :otherwise (mv nil 0))
  ///
  (defret gobj-syntactic-integerp-of-<fn>
    (gobj-syntactic-integerp new-x)
    :hints(("Goal" :in-theory (enable gobj-syntactic-integerp)))))

(define gobj-syntactic-integer->bits ((x fgl-object-p))
  :guard (gobj-syntactic-integerp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-integerp)))
  :returns (bfrlist true-listp :rule-classes :type-prescription)
  (fgl-object-case x
    :g-concrete (int->bools x.val)
    :otherwise (and (mbt (fgl-object-case x :g-integer))
                    (g-integer->bits x))))



(define gobj-syntactic-consp ((x fgl-object-p))
  (fgl-object-case x
    :g-concrete (consp x.val)
    :g-cons t
    :otherwise nil))

(define gobj-syntactic-listp ((x fgl-object-p))
  (fgl-object-case x
    :g-concrete (or (consp x.val) (not x.val))
    :g-cons t
    :otherwise nil))

(define gobj-syntactic-list-fix ((x fgl-object-p))
  :returns (mv okp (new-x fgl-object-p))
  (fgl-object-case x
    :g-concrete (mv t (if (consp x.val) (fgl-object-fix x) nil))
    :g-cons (mv t (fgl-object-fix x))
    :g-integer (mv t nil)
    :g-boolean (mv t nil)
    :otherwise (mv nil nil))
  ///
  (defret gobj-syntactic-listp-of-<fn>
    (gobj-syntactic-listp new-x)
    :hints(("Goal" :in-theory (enable gobj-syntactic-listp)))))

(define gobj-syntactic-list->car ((x fgl-object-p))
  :guard (gobj-syntactic-listp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-listp)))
  :returns (car fgl-object-p)
  (fgl-object-case x
    :g-concrete (g-concrete (car x.val))
    :otherwise (and (mbt (fgl-object-case x :g-cons))
                    (g-cons->car x))))

(define gobj-syntactic-list->cdr ((x fgl-object-p))
  :guard (gobj-syntactic-listp x)
  :guard-hints (("goal" :in-theory (enable gobj-syntactic-listp)))
  :returns (cdr fgl-object-p)
  (fgl-object-case x
    :g-concrete (g-concrete (cdr x.val))
    :otherwise (and (mbt (fgl-object-case x :g-cons))
                    (g-cons->cdr x))))



(defines fgl-object-variable-free-p
  (define fgl-object-variable-free-p ((x fgl-object-p))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    (fgl-object-case x
      :g-var nil
      :g-apply (fgl-objectlist-variable-free-p x.args)
      :g-cons (and (fgl-object-variable-free-p x.car)
                   (fgl-object-variable-free-p x.cdr))
      :g-map (fgl-object-alist-variable-free-p x.alist)
      :g-ite (and (fgl-object-variable-free-p x.test)
                  (fgl-object-variable-free-p x.then)
                  (fgl-object-variable-free-p x.else))
      :otherwise t))

  (define fgl-objectlist-variable-free-p ((x fgl-objectlist-p))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    (if (atom x)
        t
      (and (fgl-object-variable-free-p (car x))
           (fgl-objectlist-variable-free-p (cdr x)))))

  (define fgl-object-alist-variable-free-p ((x fgl-object-alist-p))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    (if (atom x)
        t
      (and (or (not (mbt (consp (car x))))
               (fgl-object-variable-free-p (cdar x)))
           (fgl-object-alist-variable-free-p (cdr x)))))
  ///
  (memoize 'fgl-object-variable-free-p))
