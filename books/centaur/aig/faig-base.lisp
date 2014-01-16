; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>
;
; July 2011, Jared added lots of documentation.
; August 2013, Jared split base.lisp into aig-base.lisp and faig-base.lisp

(in-package "ACL2")
(include-book "aig-base")
(include-book "centaur/misc/universal-equiv" :dir :system)

(defxdoc faig
  :parents (boolean-reasoning)
  :short "A @(see hons)-based representation of four-valued functions as
pairs of @(see aig)s."

  :long "<p>A <b>FAIG</b> (Four-valued AIG) combines two @(see aig)s together
to represent a function with four possible values.  Such functions can be
useful in hardware verification.</p>

<p>We represent an FAIG as the cons of two AIGs, which are called the
<i>onset</i> and <i>offset</i> of the FAIG.  Our FAIG evaluation function,
@(see faig-eval), just evaluates these two AIGs, separately, using ordinary
@(see aig-eval), and conses together the resulting Boolean values.  So, the
four possible values of an FAIG are:</p>

<ul>
<li>@('(nil . nil)'), which we call Z,</li>
<li>@('(t . nil)'), which we call True,</li>
<li>@('(nil . t)'), which we call False, and</li>
<li>@('(t . t)'), which we call X.</li>
</ul>

<p>We generally think of the onset as being a Boolean functions that should
evaluate to @('T') when the wire is being driven to 1.  The offset is similar,
but indicates whether the wire is being driven to 0.  So, the Z value
represents a situation where the wire is completely undriven, and the X value
represents a bad case where the wire is simultaneously driven to both True and
False.</p>

<p>Hons convention.  We ordinarly construct all AIGs with @(see hons), but we
don't bother to hons the FAIG conses that put these AIGs together.</p>")


(defsection faig-constants
  :parents (faig)
  :short "The four @(see FAIG) values, representing true, false, X, and Z."

  (defmacro faig-x () ''(t   . t))
  (defmacro faig-z () ''(nil . nil))
  (defmacro faig-t () ''(t   . nil))
  (defmacro faig-f () ''(nil . t)))



; [Jared] BOZO consider a warning as in aig-eval for when faig-eval,
; faig-restrict, etc., are used on non-consp arguments.

(define faig-eval (x env)
  :parents (faig)
  :short "@(call faig-eval) evaluates @('x'), a @(see faig), under the
environment @('env'), producing a pair of Boolean values."
  :long "<p>See @(see aig-eval); the @('env') should be a fast alist and you
will want to clear the memoize table for @('aig-eval') when you are done using
the @('env').</p>"
  :enabled t
  (if (atom x)
      '(t . t)
    (cons (aig-eval (car x) env)
          (aig-eval (cdr x) env)))
  ///
  (defthm faig-eval-of-constants
    (and (equal (faig-eval (faig-t) env) (faig-t))
         (equal (faig-eval (faig-f) env) (faig-f))
         (equal (faig-eval (faig-z) env) (faig-z))
         (equal (faig-eval (faig-x) env) (faig-x))
         (equal (faig-eval nil env)  (faig-x)))
    :hints(("Goal" :in-theory (enable faig-eval)))))


(define faig-fix (x)
  :parents (faig)
  :short "@(call faig-fix) is the identity for FAIGs, but coerces atoms to
@('(t . t)'), i.e., X."
  :long "<p>This is sometimes when reasoning about FAIG operations, and, e.g.,
allows for permissive guards on @(see faig-constructors), etc.</p>"
  :enabled t
  ;; inline this one since it's used in the faig b* binder, and hence just
  ;; about everywhere that faigs are being constructed or dealt with
  :inline t
  (if (consp x)
      x
    (faig-x)))

(defsection faig-fix-equiv
  (def-universal-equiv faig-fix-equiv
    :equiv-terms ((equal (faig-fix x)))
    :short "Syntactic equivalence of faigs under @(see faig-fix)."
    :long "Two objects are faig-fix-equiv if their @(see faig-fix)es are equal.")

  (verify-guards faig-fix-equiv)

  (local (in-theory (enable faig-fix-equiv)))

  (defthm faig-fix-equiv-of-faig-fix
    (faig-fix-equiv (faig-fix x) x))

  (defcong faig-fix-equiv equal (faig-fix x) 1)

  (defcong faig-fix-equiv equal (faig-eval x env) 1))


(define faig-fix-list (x)
  :parents (faig-fix)
  :short "@(call faig-fix-list) fixes every element of a list with @(see
faig-fix)."
  :enabled t
  (if (atom x)
      nil
    (cons (faig-fix (car x))
          (faig-fix-list (cdr x)))))

(define faig-fix-alist (x)
  :parents (faig-fix)
  :short "@(call faig-fix-alist) fixes every value in an alist with @(see
faig-fix)."
  :enabled t
  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; Bad-alist convention
         (faig-fix-alist (cdr x)))
        (t
         (cons (cons (caar x) (faig-fix (cdar x)))
               (faig-fix-alist (cdr x))))))

(def-b*-binder faig
  ":doc-section B*-BINDERS
Binds two variables to the onset and offset, respectively, of the
faig-fix of the given expression.~/~/~/"
  (declare (xargs :guard (and (true-listp args)
                              (equal (len args) 2)
                              (true-listp forms)
                              (equal (len forms) 1))))
  `(b* (((mv ,(first args) ,(second args))
         (let ((x (faig-fix ,(car forms))))
           (mv (car x) (cdr x)))))
     ,rest-expr))


(define faig-const-p (x)
  :parents (4v-sexpr-to-faig)
  :short "Recognizer for constant @(see faig)s."

  :long "<p>@(call faig-const-p) recognizes conses whose car/cdr are Booleans,
i.e., the four possible constant FAIGs.</p>

<p>This is the FAIG equivalent of @(see 4vp)</p>"
  (and (consp x)
       (booleanp (car x))
       (booleanp (cdr x)))
  ///
  
  (defthm faig-const-p-of-faig-eval
    (faig-const-p (faig-eval x env))
    :hints(("Goal" :in-theory (enable faig-eval)))))


(define faig-const-fix (x)
  :parents (4v-sexpr-to-faig)
  :short "Identity for FAIG constants, or constant X otherwise."
  :long "<p>Note that an older version of this function independently coerced
the car/cdr of @('t') to a Booleans when they were conses, but it seems simpler
to just say anything malformed gets fixed to @('X').</p>"
  (if (faig-const-p x)
      x
    (faig-x))
  ///

  (defthm faig-const-fix-of-faig-eval
    (equal (faig-const-fix (faig-eval x env))
           (faig-eval x env))
    :hints(("Goal" :in-theory (enable faig-eval faig-const-p))))

  (defthm faig-const-p-of-faig-const-fix
    (faig-const-p (faig-const-fix x))
    :hints(("Goal" :in-theory (enable faig-const-p))))

  (defthm faig-const-fix-of-faig-const
    (implies (faig-const-p x)
             (equal (faig-const-fix x) x))
    :hints(("Goal" :in-theory (enable faig-const-p)))))

(defsection faig-const-equiv
  (def-universal-equiv faig-const-equiv
    :equiv-terms ((equal (faig-const-fix x)))
    :short "Equivalence of faig constants (@(see faig-const-p))."
    :long "Two objects are faig-const-equiv if their @(see faig-const-fix)es are equal.")

  (verify-guards faig-const-equiv)

  (local (in-theory (enable faig-const-equiv)))

  (defthm faig-const-equiv-of-faig-const-fix
    (faig-const-equiv (faig-const-fix x) x))

  (defcong faig-const-equiv equal (faig-const-fix x) 1))


(define faig-const-<= (x y)
  :parents (4v-sexpr-to-faig)
  :short "Lattice ordering for FAIG constants."
  :long "<p>This is just the FAIG equivalent of @(see 4v-<=).</p>"
  (let ((x (faig-const-fix x))
        (y (faig-const-fix y)))
    (or (equal x y)
        (equal x (faig-x))))
  ///
  (defcong faig-const-equiv equal (faig-const-<= x y) 1
    :hints(("Goal" :in-theory (enable faig-const-<=))))
  (defcong faig-const-equiv equal (faig-const-<= x y) 2
    :hints(("Goal" :in-theory (enable faig-const-<=)))))




(define faig-eval-list (x env)
  :parents (faig-eval)
  :short "@(call faig-eval-list) evaluates a list of FAIGs."
  :enabled t
  (if (atom x)
      nil
    (cons (faig-eval (car x) env)
          (faig-eval-list (cdr x) env)))
  ///
  (defthm nth-of-faig-eval-list
    (faig-const-equiv (nth n (faig-eval-list x env))
                      (faig-eval (nth n x) env))))

(define faig-eval-alist (x env)
  :parents (faig-eval)
  :short "@(call faig-eval-list) evaluates an FAIG alist (an alist binding
keys to FAIGs)."
  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"
  :enabled t
  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; Bad alist convention
         (faig-eval-alist (cdr x) env))
        (t
         (cons (cons (caar x)
                     (faig-eval (cdar x) env))
               (faig-eval-alist (cdr x) env)))))

(define faig-restrict (x sigma)
  :parents (faig)
  :short "@(call faig-restrict) performs variable substitution throughout the
FAIG @('x'), replacing any variables bound in @('sigma') with their
corresponding values."
  :long "<p>See @(see aig-restrict); the @('env') should be a fast alist and
you will want to clear the memoize table for @('aig-restrict') when you are
done using the @('env').</p>"
  :enabled t
  (if (atom x)
      '(t . t)
    (cons (aig-restrict (car x) sigma)
          (aig-restrict (cdr x) sigma))))

(define faig-restrict-alist (x sigma)
  :parents (faig-restrict)
  :short "@(call faig-restrict-alist) substitutes into an FAIG alist (an alist
binding keys to FAIGs)."
  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"
  :enabled t
  (b* (((when (atom x))
        nil)
       (rest (faig-restrict-alist (cdr x) sigma))
       ((when (atom (car x)))
        ;; Bad alist convention
        rest))
    (cons (cons (caar x) (faig-restrict (cdar x) sigma))
          rest)))

(define faig-restrict-alists (x sigma)
  :parents (faig-restrict)
  :short "@(call faig-restrict-alists) substitutes into a list of FAIG alists."
  :enabled t
  (if (atom x)
      nil
    (cons (faig-restrict-alist (car x) sigma)
          (faig-restrict-alists (cdr x) sigma))))

(define faig-compose (x sigma)
  :parents (faig)
  :short "@(call faig-compose) performs variable substitution throughout the
FAIG @('x'), <b>unconditionally</b> replacing every variable in @('x') with its
binding in @('sigma')."
  :long "<p>See @(see aig-compose); the @('sigma') should be a fast alist and
you will want to clear the memoize table for @('aig-compose') when you are done
using the @('env').</p>"
  :enabled t
  (if (atom x)
      '(t . t)
    (cons (aig-compose (car x) sigma)
          (aig-compose (cdr x) sigma))))

(define faig-compose-alist (x sigma)
  :parents (faig)
  :short "@(call faig-compose-alist) composes into an FAIG Alist (an alist
binding keys to FAIGs)."
  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"
  :enabled t
  (b* (((when (atom x))
        nil)
       (rest (faig-compose-alist (cdr x) sigma))
       ((when (atom (car x)))
        ;; Bad alist convention
        rest))
    (cons (cons (caar x) (faig-compose (cdar x) sigma))
          rest)))

(define faig-partial-eval (x env)
  :parents (faig)
  :short "@(call faig-partial-eval) evaluates @('x'), an FAIG, under the
partial environment @('env'), producing a new FAIG as a result."
  :long "<p>See @(see aig-partial-eval); the @('env') should be a fast alist
and you will want to clear the memoize table for @('aig-partial-eval') when you
are done using the @('env').</p>"
  :enabled t
  (if (atom x)
      '(t . t)
    (cons (aig-partial-eval (car x) env)
          (aig-partial-eval (cdr x) env))))

(define faig-partial-eval-alist (x env)
  :parents (faig-partial-eval)
  :short "@(call faig-partial-eval-alist) partially evaluates an FAIG alist (an
alist binding keys to FAIGs)."
  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"
  :enabled t
  (b* (((when (atom x))
        nil)
       (rest (faig-partial-eval-alist (cdr x) env))
       ((when (atom (car x)))
        ;; Bad alist convention
        rest))
    (cons (cons (caar x) (faig-partial-eval (cdar x) env))
          rest)))

(define faig-partial-eval-alists (x env)
  :parents (faig-partial-eval)
  :short "@(call faig-partial-eval-alists) partially evaluates a list of FAIG
alists."
  :enabled t
  (if (atom x)
      nil
    (cons (faig-partial-eval-alist (car x) env)
          (faig-partial-eval-alists (cdr x) env))))




