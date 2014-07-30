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
(include-book "xdoc/top" :dir :system)
(include-book "gl-util")


;; This is turning into a dumping ground for logically-simple functions that
;; have a special meaning under symbolic execution.  Maybe we should rename
;; this file.

(defsection acl2::always-equal
  :parents (reference)
  :short "Alias for @(see equal) that has a special meaning in @(see gl-bdd-mode)."

  :long "<p>Logically this is just @(see equal), but @(see GL) treats
@('always-equal') in a special way.</p>

<p>Suppose GL is asked to prove @('(equal spec impl)') when this does not
actually hold.  Sometimes, the symbolic objects for spec and impl can be
created, but the BDD representing their equality is too large to fit in memory.
This stops you from seeing any counterexamples, even though GL knows that the
two objects aren't equal.</p>

<p>To work around this, you may restate your theorem using @('always-equal')
instead of @('equal') as the final comparison.  @('always-equal') has a custom
symbolic counterpart that returns @('t') when its arguments are equivalent, or
else produces a symbolic object that captures just one counterexample and is
indeterminate in all other cases.</p>

<p>Note that there is not really any reason to use @('always-equal') if you are
using an AIG-based GL mode, such as @(see gl-satlink-mode).</p>"

  (defun acl2::always-equal (x y)
    (declare (Xargs :guard t))
    (equal x y)))

(defsection gl-assert
  :parents (reference)
  :short "During GL symbolic execution, check that a condition holds and produce an error if not."
  :long "<p>@('(GL-ASSERT X)'), logically speaking, just returns @('(IF X T
NIL)').  In concrete execution, it causes an error if @('X') is false, and in
symbolic execution, it forces a check that @('X') is true and produces a
counterexample if not.</p>"


  (defun-inline gl-assert-fn (x msg gmsg)
    (declare (xargs :guard t)
             (ignore gmsg))
    (mbe :logic (and x t)
         :exec (if x
                   t
                 (er hard? 'gl-assert "~@0" msg))))

  (defmacro gl-assert (x &key
                         (msg 'nil msgp)
                         (gmsg 'nil gmsgp))
    (let* ((msg (if msgp
                    msg
                  (list 'quote (acl2::msg "GL-ASSERT failure: ~x0" x))))
           (gmsg (cond (gmsgp gmsg)
                       (msgp msg)
                       (t (list 'quote (acl2::msg "GL-ASSERT failure: ~x0" x))))))
      `(gl-assert-fn ,x ,msg ,gmsg))))


(defsection gl-concretize
  :parents (reference)
  :short "During GL symbolic execution, try to reduce a symbolic object to a concrete one."
  :long "<p>@('(GL-CONCRETIZE X)'), logically speaking, just returns @('X').
However, during symbolic simulation (in AIG mode), it tries to reduce @('X') to
a concrete object by finding one object it could represent and trying to prove
that it is always equal to that object.</p>"


  (defun-inline gl-concretize (x)
    (declare (xargs :guard t))
    x))


(defsection gl-mbe
  :parents (reference)
  :short "Assert that a particular symbolic object is equivalent to a second
form, and use the second in place of the first."

  :long "<p>@(call gl-mbe) is defined to simply check whether its two arguments
SPEC and IMPL are equal, throwing an error if not, and return SPEC.</p>

<p>However, when GL-MBE is symbolically executed, the equality of the two
arguments is checked symbolically.  If it can be proved that they are always
equal, then IMPL is returned instead of SPEC, otherwise an error is produced.</p>

<p>This is most useful when symbolically executing in AIG mode.  For example,
suppose that through a series of shifting operations, the symbolic
representation of some numeric operand X is expanded to thousands of bits.
However, the user knows that only the bottom 25 bits may be non-zero.  Then the
following form may speed up the rest of the computation involving X by cutting
off all the upper bits, which are known to be zero:</p>

@({
 (let ((x (gl-mbe x (logand (1- (ash 1 25)) x))))
    ...)
})

<p>Here GL-MBE tries to prove that X and the LOGAND expression are equivalent,
that is, their symbolic representations evaluate to the same concrete values
under all environments.  If this can be proved, X is bound to the LOGAND
result, which cuts off the upper bits of X, improving symbolic execution
performance.  However, because logically GL-MBE just returns X, the meaning of
the specification is unaffected.</p>"

  (defun gl-mbe-fn (spec impl spec-form impl-form)
    (declare (xargs :guard t))
    (mbe :logic spec
         :exec (prog2$
                (or (equal spec impl)
                    (er hard?
                        "GL-MBE failure: ~x0 and ~x1 unequal.~%Values: ~x2 versus ~x3."
                        spec-form impl-form spec impl))
                spec)))

  (defthm gl-mbe-gl-def
    (equal (gl-mbe-fn spec impl spec-form impl-form)
           (if (gl-assert (acl2::always-equal spec impl)
                          :msg (msg "GL-MBE failure: ~x0 and ~x1 unequal." spec-form impl-form))
               impl
             spec))
    :rule-classes ((:definition :install-body nil)))

  (set-preferred-def gl-mbe-fn gl-mbe-gl-def)

  (defmacro gl-mbe (spec impl &optional other-info)
    (declare (ignorable other-info))
    (prog2$ (and other-info
                 (cw "NOTE: The third argument of gl-mbe is deprecated.  Sorry for the confusion.~%"))
            `(gl-mbe-fn ,spec ,impl ',spec ',impl))))


(defun gl-force-check-fn (x strong direction)
  (declare (xargs :guard t)
           (ignore strong direction))
  x)

(defmacro gl-force-check (x &key strong (direction ':both))
  `(gl-force-check-fn ,x ,strong ,direction))

(defmacro gl-force-check-strong (x)
  `(gl-force-check-fn ,x t :both))


(defmacro gl-force-true (x &key strong)
  `(gl-force-check-fn ,x ,strong t))

(defmacro gl-force-true-strong (x)
  `(gl-force-check-fn ,x t t))

(defmacro gl-force-false (x &key strong)
  `(gl-force-check-fn ,x ,strong nil))

(defmacro gl-force-false-strong (x)
  `(gl-force-check-fn ,x t nil))

(table gl-uninterpreted-functions 'gl-force-check-fn t)






(defun gl-aside (x)
  (declare (xargs :guard t)
           (ignore x))
  nil)

(defun gl-ignore (x)
  (declare (xargs :guard t)
           (ignore x))
  nil)

(defund gl-error (x)
  (declare (xargs :guard t)
           (ignore x))
  (prog2$ (er hard? 'gl-error "GL-ERROR call encountered; quitting~%")
          nil))

(defthm gl-error-is-nil
  (equal (gl-error x) nil)
  :hints(("Goal" :in-theory (enable gl-error))))



(defun gl-hide (x)
  (declare (xargs :guard t))
  x)
