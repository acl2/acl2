(in-package "ACL2")

(include-book "def-simplified")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (def-simplified *three* '(+ 1 2))
  (must-be-redundant
   (defconst *three* ''3)))

(deftest
  (def-simplified *car-cons* '(car (cons x y)))
  (must-be-redundant
   (defconst *car-cons* '((0 . x)))))

;; A test that uses an assumption
(deftest
  (def-simplified *test* '(numerator x)
                        :assumptions '((integerp x))
                        :rules '(numerator-when-integerp))
  (must-be-redundant
   (defconst *test* '((0 . x)))))

;; A test that uses an assumption, plus rewriting a RHS
(deftest
  (defun my-integerp (x) (integerp x))
  (defthm my-numerator-when-integerp
    (implies (my-integerp x)
             (equal (numerator x)
                    x)))

  (def-simplified *test* '(numerator x)
                        :assumptions '((integerp x))
                        :rules '(my-numerator-when-integerp my-integerp))
  (must-be-redundant
   (defconst *test* '((0 . x)))))
