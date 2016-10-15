(in-package "ACL2")

(include-book "coi/nary/nary-mod" :dir :system)

;; (nary::monitor-on)

;; (include-book "arithmetic-5/top" :dir :system)

(encapsulate
    (
     ((p) => *)
     )

  (local
   (defun p () 0))

  (defthm integerp-p
    (integerp (p))
    :rule-classes (:type-prescription
                   :rewrite (:forward-chaining :trigger-terms ((p)))))
  
  )

(encapsulate
    (
     ((inv *) => *)
     )

  (local
   (defun inv (x) (ifix x)))

  (defthm integerp-p-inv
    (integerp (inv x))
    :rule-classes (:type-prescription
                   :rewrite (:forward-chaining :trigger-terms ((inv x)))))
  
  )

(defstub pred (x) nil)

(in-theory (disable mod expt))

(defthmd mod-expt-rewrite-5
  (implies (and (integerp k) (integerp l) (integerp m) (integerp n) (natp k))
           (equal (mod (* k l m (expt (mod n (p)) k)) (p))
                  (mod (* k l m (expt n k)) (p))))
  :hints (("Goal" :in-theory (enable nary::mod-rules))))

(defthm simplifies-without-mod-expt-rewrite-5
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp z))
   (equal (pred
           (MOD (* 3
                   (EXPT x 2)
                   (EXPT y 4)
                   (EXPT (MOD (EXPT (INV z) 2) (P)) 2))
                (P)))
          (PRED (MOD (* 3 (EXPT X 2)
                        (EXPT y 4)
                        (EXPT (expt (INV Z) 2) 2))
                     (P)))))
  :hints (("Goal" :in-theory (enable nary::mod-rules))))

(defthm mod-zero
  (equal (mod 0 n) 0)
  :hints (("Goal" :in-theory (enable mod))))

(defthm substitution-test
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp z)
    (integerp n)
    ;; The congruence rules will cause these values to be substituted
    ;; into our conclusion.
    (equal (mod y n) (- z))
    (equal (mod x n) 0))
   (equal (mod (+ x y z) n)
          0))
  :hints (("Goal" :in-theory (enable nary::mod-rules))))

;; Getting rid of "P"

(defthm really?
  (equal (* 0 x) 0))

(defthm rid-p
  (implies
   (integerp x)
   (equal (mod (+ (* (p) x) (+ -8 (p))) (p))
          (mod -8 (p))))
  :hints (("Goal" :in-theory (enable nary::mod-rules))))

;; Applying a rewrite rule

(def::und foo (x)
  (declare (xargs :signature ((integerp) integerp)))
  x)

(def::und goo (x)
  (declare (xargs :signature ((integerp) integerp)))
  x)

(defthm foo-to-goo
  (equal (mod (foo x) p)
         (mod (goo x) p))
  :hints (("Goal" :in-theory (enable foo goo))))

(defthm foo-to-goo-test
  (implies
   (and
    (integerp p)
    (integerp x)
    (integerp y)
    (integerp z))
   (equal (mod (+ x (foo y) z) p)
          (mod (+ x (goo y) z) p)))
  :hints (("Goal" :in-theory (enable nary::mod-rules))))
