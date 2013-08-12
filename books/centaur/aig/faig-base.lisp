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

(defsection faig-eval
  :parents (faig)
  :short "@(call faig-eval) evaluates @('x'), a @(see faig), under the
environment @('env'), producing a pair of Boolean values."

  :long "<p>See @(see aig-eval); the @('env') should be a fast alist and you
will want to clear the memoize table for @('aig-eval') when you are done using
the @('env').</p>"

  (defun faig-eval (x env)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-eval (car x) env)
            (aig-eval (cdr x) env)))))


(defsection faig-eval-list
  :parents (faig-eval)
  :short "@(call faig-eval-list) evaluates a list of FAIGs."

  (defun faig-eval-list (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-eval (car x) env)
            (faig-eval-list (cdr x) env)))))


(defsection faig-eval-alist
  :parents (faig-eval)
  :short "@(call faig-eval-list) evaluates an FAIG alist (an alist binding
keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-eval-alist (x env)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad alist convention
           (faig-eval-alist (cdr x) env))
          (t
           (cons (cons (caar x)
                       (faig-eval (cdar x) env))
                 (faig-eval-alist (cdr x) env))))))




(defsection faig-restrict
  :parents (faig)
  :short "@(call faig-restrict) performs variable substitution throughout the
FAIG @('x'), replacing any variables bound in @('sigma') with their
corresponding values."

  :long "<p>See @(see aig-restrict); the @('env') should be a fast alist and
you will want to clear the memoize table for @('aig-restrict') when you are
done using the @('env').</p>"

  (defun faig-restrict (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-restrict (car x) sigma)
            (aig-restrict (cdr x) sigma)))))


(defsection faig-restrict-alist
  :parents (faig-restrict)
  :short "@(call faig-restrict-alist) substitutes into an FAIG alist (an alist
binding keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-restrict-alist (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((rest (faig-restrict-alist (cdr x) sigma)))
        (if (atom (car x))
            ;; Bad alist convention
            rest
          (cons (cons (caar x) (faig-restrict (cdar x) sigma))
                rest))))))


(defsection faig-restrict-alists
  :parents (faig-restrict)
  :short "@(call faig-restrict-alists) substitutes into a list of FAIG alists."

  (defun faig-restrict-alists (x sigma)
    (if (atom x)
        nil
      (cons (faig-restrict-alist (car x) sigma)
            (faig-restrict-alists (cdr x) sigma)))))




(defsection faig-compose
  :parents (faig)
  :short "@(call faig-compose) performs variable substitution throughout the
FAIG @('x'), <b>unconditionally</b> replacing every variable in @('x') with its
binding in @('sigma')."

  :long "<p>See @(see aig-compose); the @('sigma') should be a fast alist and
you will want to clear the memoize table for @('aig-compose') when you are done
using the @('env').</p>"

  (defun faig-compose (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-compose (car x) sigma)
            (aig-compose (cdr x) sigma)))))


(defsection faig-compose-alist
  :parents (faig)
  :short "@(call faig-compose-alist) composes into an FAIG Alist (an alist
binding keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-compose-alist (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((rest (faig-compose-alist (cdr x) sigma)))
        (if (atom (car x))
            ;; Bad alist convention
            rest
          (cons (cons (caar x) (faig-compose (cdar x) sigma))
                rest))))))




(defsection faig-partial-eval
  :parents (faig)
  :short "@(call faig-partial-eval) evaluates @('x'), an FAIG, under the
partial environment @('env'), producing a new FAIG as a result."

  :long "<p>See @(see aig-partial-eval); the @('env') should be a fast alist
and you will want to clear the memoize table for @('aig-partial-eval') when you
are done using the @('env').</p>"

  (defun faig-partial-eval (x env)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-partial-eval (car x) env)
            (aig-partial-eval (cdr x) env)))))


(defsection faig-partial-eval-alist
  :parents (faig-partial-eval)
  :short "@(call faig-partial-eval-alist) partially evaluates an FAIG alist (an
alist binding keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-partial-eval-alist (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((rest (faig-partial-eval-alist (cdr x) env)))
        (if (atom (car x))
            ;; Bad alist convention
            rest
          (cons (cons (caar x) (faig-partial-eval (cdar x) env))
                rest))))))


(defsection faig-partial-eval-alists
  :parents (faig-partial-eval)
  :short "@(call faig-partial-eval-alists) partially evaluates a list of FAIG
alists."

  (defund faig-partial-eval-alists (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-partial-eval-alist (car x) env)
            (faig-partial-eval-alists (cdr x) env)))))




(defsection faig-fix
  :parents (faig)
  :short "@(call faig-fix) is the identity for FAIGs, but coerces atoms to
@('(t . t)'), i.e., X."

  :long "<p>This is sometimes when reasoning about FAIG operations.</p>"

  (defun faig-fix (x)
    (declare (xargs :guard t))
    (if (consp x) x '(t . t))))


(defsection faig-fix-list
  :parents (faig-fix)
  :short "@(call faig-fix-list) fixes every element of a list with @(see
faig-fix)."

  (defun faig-fix-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-fix (car x))
            (faig-fix-list (cdr x))))))


(defsection faig-fix-alist
  :parents (faig-fix)
  :short "@(call faig-fix-alist) fixes every value in an alist with @(see
faig-fix)."

  (defun faig-fix-alist (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad-alist convention
           (faig-fix-alist (cdr x)))
          (t
           (cons (cons (caar x) (faig-fix (cdar x)))
                 (faig-fix-alist (cdr x)))))))

