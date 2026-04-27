(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/factorial" :dir :system)
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "nonstd/nsa/ln-product" :dir :system)

(defun iter-factorial (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      (if (zp n)
          1
          n)
      (* i (iter-factorial (1+ i) n))))

(local
 (defthmd iter-factorial-as-factorial-lemma
     (implies (and (posp i)
                   (natp n)
                   (< i n))
              (equal (iter-factorial i n)
                     (* n (iter-factorial i (1- n)))))
   ))

(defthmd iter-factorial-as-factorial
    (implies (natp n)
             (equal (iter-factorial 1 n)
                    (factorial n)))
  :hints (("Goal"
           :in-theory (enable factorial)
           :induct (factorial n))
          ("Subgoal *1/2"
           :use ((:instance iter-factorial-as-factorial-lemma (i 1))))))

(defun sum-ln (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      (if (< n i)
          0
          (acl2-ln n))
      (+ (acl2-ln i)
         (sum-ln (1+ i) n))))

(defthm real-iter-factorial
    (implies (and (realp i)
                  (realp n))
             (realp (iter-factorial i n)))
  :rule-classes (:rewrite :type-prescription))

(defthm posp-iter-factorial
    (implies (and (posp i)
                  (natp n))
             (posp (iter-factorial i n)))
  :rule-classes (:rewrite :type-prescription))

(defthmd ln-iter-factorial
    (implies (and (posp i)
                  (posp n)
                  (<= i n))
             (equal (acl2-ln (iter-factorial i n))
                    (sum-ln i n)))
  )

(defthmd ln-factorial
    (implies (posp n)
             (equal (acl2-ln (factorial n))
                    (sum-ln 1 n)))
  :hints (("Goal"
           :use ((:instance ln-iter-factorial (i 1))
                 (:instance iter-factorial-as-factorial))))
  )
