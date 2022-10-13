; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; We repeat a couple of tests from simplify-defun-tests.lisp but with cgen
; loaded this time.

; Thanks to Eric Smith for pointing out a previous failure, where cgen's
; :backtrack hints were causing rewrite$ to fail.  Now we erase those hints
; during make-event expansion; see with-simplify-setup-fn.

(in-package "ACL2")

(include-book "simplify")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "acl2s/cgen/top" :dir :system) ; include counterexample stuff

(acl2s-defaults :set testing-enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We avoid deftest when default defun-mode is :programk, because deftest
; creates local events, which are skipped when the default defun-mode is
; :program.

(defun program-mode-test (x)
  (declare (xargs :guard (integerp x)))
  (+ 2 3 x))
(program)
(simplify program-mode-test)
(logic)
(must-be-redundant
 (DEFUN PROGRAM-MODE-TEST$1 (X)
   (DECLARE (XARGS :GUARD (INTEGERP X)
                   :mode :logic ; added manually
                   :VERIFY-GUARDS T))
   (+ 5 X)))

; And here's a simple test not involving :program mode with cgen testing.

(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (simplify-defun foo)
  (must-be-redundant
    (DEFUN FOO$1 (X) (+ 2 X))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))
