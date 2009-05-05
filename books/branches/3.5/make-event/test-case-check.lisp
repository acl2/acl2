; This is like test-case.lisp, except it uses assert!! (which uses
; :check-expansion t) rather than assert!.

(in-package "ACL2")

(include-book "assert-check")

(defmacro test-case (form &key (expected 'nil expected-p))
  (let ((form (if expected-p
                  `(equal ,form ,expected)
                form)))
    (list 'assert!! form)))

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
