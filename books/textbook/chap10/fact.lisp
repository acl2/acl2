; Section 10.1 Factorial

(in-package "ACL2")

(defun fact (x)
  (if (zp x)
      1
    (* x (fact (- x 1)))))

(defun tfact (x p)
  (if (zp x)
      p
    (tfact (- x 1) (* x p))))

(defthm complete-*
  (equal (* y (* x z))
         (* x (* y z)))
  :hints (("Goal"
           :use ((:instance associativity-of-* (y x) (x y))
                 (:instance associativity-of-*))
           :in-theory (disable associativity-of-*))))

(defthm fact=tfact-lemma-for-acl2-numberp
  (implies (acl2-numberp p)
           (equal (tfact x p)
                  (* p (fact x)))))

(defthm fact=tfact
  (equal (tfact x 1) (fact x)))

