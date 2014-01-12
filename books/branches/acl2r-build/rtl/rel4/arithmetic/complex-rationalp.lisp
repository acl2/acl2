(in-package "ACL2")
; cert_param: (non-acl2r)
(local (include-book "predicate"))

(defthm complex-rationalp-+-when-second-term-is-rational
  (implies (rationalp y)
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp x))))

(defthm complex-rationalp-+-when-second-term-is-not-complex
  (implies (not (complex-rationalp y))
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp x))))

(defthm complex-rationalp-+-when-first-term-is-rational
  (implies (rationalp x)
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp y))))

(defthm complex-rationalp-+-when-first-term-is-not-complex
  (implies (not (complex-rationalp x))
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp y))))

;add more cases
(defthm complex-rationalp-*-drop-first-term-if-rational
  (implies (and (case-split (not (equal y 0)))
                (rationalp y))
           (equal (complex-rationalp (* y x))
                  (complex-rationalp x))))


#|
(defthm complex-rationalp-*-drop-first-term-if-not-complex
  (implies (and (case-split (not (equal y 0)))
                (not (complex-rationalp y))
                )
           (equal (complex-rationalp (* y x))
                  (complex-rationalp x))))
|#

