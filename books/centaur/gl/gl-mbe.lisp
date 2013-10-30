; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "xdoc/top" :dir :system)
(include-book "gl-util")

(defun acl2::always-equal (x y)
  (declare (Xargs :guard t))
  (equal x y))

(defsection gl-assert
  :parents (reference)
  :short "During GL symbolic execution, check that a condition holds and produce an error if not."
  :long "<p>@('GL-ASSERT'), logically speaking, just returns its argument.  In
concrete execution, it causes an error if that argument is false, and in
symbolic execution, it forces a check that its argument is true and produces a
counterexample if not.</p>"


  (defun-inline gl-assert-fn (x msg gmsg)
    (declare (xargs :guard t)
             (ignore gmsg))
    (mbe :logic x
         :exec (or x
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



