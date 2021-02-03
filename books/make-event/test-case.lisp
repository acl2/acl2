; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Sandip Ray suggested that we might want to be able to evaluate arbitrary
; forms, but in this file, test-case should be applied to forms that return a
; single non-stobj value.

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defmacro test-case (form &key (expected 'nil expected-p))
  (let ((form (if expected-p
                  `(equal ,form ,expected)
                form)))
    (list 'assert! form)))

#| ; A more direct definition, not using the assert!.
(defmacro test-case (form &key (expected 'nil expected-p))
  `(make-event
    (let ((ans ,form)
          (expected ,expected))
      (if (or (null ,expected-p)
              (equal ans expected))
          (value `(value-triple ,ans))
        (er soft 'test-case
            "TEST-CASE expected ~y0, got ~y1."
            expected ans)))))
|# ; |

(test-case (+ 3 4))

(test-case (+ 3 4) :expected 7)

(must-fail
 (test-case (+ 3 4) :expected 8))

(test-case (equal (+ 3 4) 7))

(must-fail
 (test-case (equal (+ 3 4) 8)))
