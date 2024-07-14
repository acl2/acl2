; Tests of subst-var-alt
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "subst-var-alt")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)

;; Compare to the tests in sublis-var-simple-tests.lisp.

;; Perhaps surprising.  Adds another binding to the let.
;; We might prefer the result to be (the translation of) (let ((z 3)) (+ y z))
;; but then we have to think about capture
(assert-equal
 ;; the regular sublis-var gives the same thing on this
 (subst-var-alt 'x 'y
                ;; :trans (let ((z 3)) (+ x z))
                '((lambda (z x) (binary-+ x z)) '3 x)
                )
 ;; :trans (let ((z 3)) (+ y z))
 '((lambda (z y) (binary-+ y z)) '3 y))

;; Here, it's less clear that there is a nicer alternate result, due to
;; capture:
;; Replaces x with (cons z z) in (let ((z 3)) (+ x z)).
(assert-equal
 (subst-var-alt 'x '(cons z z)
                ;; :trans (let ((z 3)) (+ x z))
                '((lambda (z x) (binary-+ x z)) '3 x)
                )
 ;; :trans (let ((x (cons z z))) (let ((z 3)) (+ x z)))
 '((lambda (x)
     ((lambda (z x) (binary-+ x z)) '3 x))
   (cons z z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun test-subst-var-alt-fn (var replacement term expected-result wrld)
  (declare (xargs :guard (symbolp var) :mode :program))
  (let* ((replacement (translate-term replacement 'test-subst-var-alt-fn wrld))
         (term (translate-term term 'test-subst-var-alt-fn wrld))
         (result (subst-var-alt var replacement term))
         (result (untranslate result 'nil wrld)))
    (if (equal result expected-result)
        '(value-triple :passed)
      (er hard? 'test-subst-var-alt-fn "Test failed:~%Result: ~x0.~%Expected result: ~x1." result expected-result))))

(defmacro test-subst-var-alt (var replacement term expected-result)
  `(make-event (test-subst-var-alt-fn ',var ',replacement ',term ',expected-result (w state))))

(test-subst-var-alt x (len foo) x (len foo))

;; note that the change is applied to the lambda body
(test-subst-var-alt x (len foo)
                    (let ((y 5)) (< x y))
                    (let ((y 5)) (< (len foo) y)))

;; nothing to do, as x is not free in the term
(test-subst-var-alt x (len foo)
                    (let ((y 5) (x 6)) (< x y))
                    (let ((y 5) (x 6)) (< x y)))

;; here we can't substitute in the lambda body because the binding of foo to z
;; changes the meaning of foo, which appears in the replacement term for x,
;; (len foo)
(test-subst-var-alt x (len foo)
                    (let ((y 5) (foo z)) (acons x y foo))
                    ;; todo: better result?  add binding of x to existing lambda?
                    (let ((x (len foo))) (let ((y 5) (foo z)) (acons x y foo))))
