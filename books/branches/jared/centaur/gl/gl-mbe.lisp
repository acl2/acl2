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

  (defun gl-mbe (spec impl other-info)
    (declare (xargs :guard t)
             (ignore other-info))
    (prog2$ (or (equal spec impl)
                (er hard? 'gl-mbe "GL-MBE assertion failed: ~x0 not equal to ~x1~%"
                    spec impl))
            spec)))

(defun gl-force-check-fn (x strong)
  (declare (xargs :guard t)
           (ignore strong))
  x)

(defmacro gl-force-check (x &key strong)
  `(gl-force-check-fn ,x ,strong))

(defmacro gl-force-check-strong (x)
  `(gl-force-check-fn ,x t))

(defun gl-force-true-fn (x strong)
  (declare (xargs :guard t)
           (ignore strong))
  x)

(defmacro gl-force-true (x &key strong)
  `(gl-force-true-fn ,x ,strong))

(defmacro gl-force-true-strong (x)
  `(gl-force-true-fn ,x t))


(defun gl-force-false-fn (x strong)
  (declare (xargs :guard t)
           (ignore strong))
  x)

(defmacro gl-force-false (x &key strong)
  `(gl-force-false-fn ,x ,strong))

(defmacro gl-force-false-strong (x)
  `(gl-force-false-fn ,x t))

(table gl-uninterpreted-functions 'gl-force-check-fn t)
(table gl-uninterpreted-functions 'gl-force-true-fn t)
(table gl-uninterpreted-functions 'gl-force-false-fn t)
