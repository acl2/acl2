(in-package "ACL2")

(include-book "nary-mod")
(include-book "arithmetic-5/top" :dir :system)

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
                        (EXPT Y 4)
                        (EXPT (INV Z) 4))
                     (P)))))
  :hints (("Goal" :in-theory (enable nary::mod-rules))))

          
