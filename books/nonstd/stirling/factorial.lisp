(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/factorial" :dir :system)

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
