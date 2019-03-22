(in-package "RTL")

(include-book "projects/quadratic-reciprocity/pratt" :dir :system)
(local (include-book "projects/quadratic-reciprocity/support/pratt" :dir :system))
(include-book "rtl/rel11/support/util" :dir :system) ;for local-defthmd
(local (include-book "rtl/rel11/support/basic" :dir :system))
(include-book "projects/quadratic-reciprocity/euler" :dir :system) ;for residue

(include-book "arithmetic-5/top" :dir :system)

(in-theory (disable ACL2::|(mod (+ x y) z) where (<= 0 z)| ACL2::|(mod (+ x (- (mod a b))) y)|
                    ACL2::|(mod (mod x y) z)| ACL2::|(mod (+ x (mod a b)) y)| ACL2::cancel-mod-+
                    ACL2::mod-cancel-*-const ACL2::simplify-products-gather-exponents-equal
                    ACL2::simplify-products-gather-exponents-< ACL2::|(mod (+ 1 x) y)|
                    ACL2::cancel-mod-+ ACL2::reduce-additive-constant-< ACL2::|(floor x 2)|
                    ACL2::|(equal x (if a b c))| ACL2::|(equal (if a b c) x)| acl2::|(mod (- x) y)|))

(defund p () (- (expt 2 255) 19))

(defthm primep-p
  (primep (p))
  :hints (("Goal" :use (primep-25519)
           :in-theory (disable (:e primep)))))

(defthm p-nat
  (natp (p))
  :rule-classes (:type-prescription :rewrite))

(in-theory (disable (p)))

(defthm p-is-big
  (> (p) 100000)
  :hints (("Goal" :in-theory (enable p)))
  :rule-classes (:linear))

(defun fp (n) (and (natp n) (< n (p))))

(defun f+ (m n)
  (mod (+ m n) (p)))

(defun f- (m n)
  (mod (- m n) (p)))

(defun f* (m n)
  (mod (* m n) (p)))

(defun fexpt (n e)
  (mod-expt n e (p)))

(defund frcp (n)
  (fexpt n (- (p) 2)))

(defthm natp-frcp
  (implies (integerp n)
           (natp (frcp n)))
  :hints (("Goal" :in-theory (enable p frcp)))
  :rule-classes (:type-prescription :rewrite))

(defun f/ (m n)
  (mod (* m (frcp n)) (p)))

(defthm mod*0
  (implies (and (integerp n) (integerp m)
                (not (= (mod n (p)) 0))
                (not (= (mod m (p)) 0)))
           (not (= (mod (* n m) (p)) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance euclid (p (p)) (a n) (b m))
                        (:instance divides-mod-0 (n (p)) (a n))
                        (:instance divides-mod-0 (n (p)) (a m))
                        (:instance divides-mod-0 (n (p)) (a (* n m)))))))

(defthm mod+rewrite-1
  (implies (and (integerp a) (integerp b))
           (equal (mod (+ (mod a (p)) b) (p))
                  (mod (+ a b) (p))))
  :hints (("Goal" :in-theory (enable mod-sum))))

(defthm mod+rewrite-2
  (implies (and (integerp a) (integerp b))
           (equal (mod (+ a (mod b (p))) (p))
                  (mod (+ a b) (p))))
  :hints (("Goal" :in-theory (enable mod-sum))))

(defthm mod+rewrite-3
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (mod (+ a (mod b (p)) c) (p))
                  (mod (+ a b c) (p)))))

(defthm mod+rewrite-4
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (mod (+ a b (mod c (p))) (p))
                  (mod (+ a b c) (p)))))

(defthm mod*rewrite-1
  (implies (and (integerp a) (integerp b))
           (equal (mod (* (mod a (p)) b) (p))
                  (mod (* a b) (p))))
  :hints (("Goal" :use ((:instance mod-mod-times (n (p)))))))

(defthm mod*rewrite-2
  (implies (and (integerp a) (integerp b))
           (equal (mod (* a (mod b (p))) (p))
                  (mod (* a b) (p))))
  :hints (("Goal" :use ((:instance mod-mod-times (n (p)) (a b) (b a))))))

(defthm mod*rewrite-3
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (mod (* a b (mod c (p))) (p))
                  (mod (* a b c) (p))))
  :hints (("Goal" :use ((:instance mod*rewrite-2 (a (* a b)) (b c))))))

(defthm mod*rewrite-4
  (implies (and (integerp a) (integerp b) (integerp c) (integerp d))
           (equal (mod (* a b c (mod d (p))) (p))
                  (mod (* a b c d) (p))))
  :hints (("Goal" :use ((:instance mod*rewrite-2 (a (* a b c)) (b d))))))

(defthm mod*rewrite-5
  (implies (and (integerp a) (integerp b) (integerp c))
           (equal (mod (+ a (* b (mod c (p)))) (p))
                  (mod (+ a (* b c)) (p))))
  :hints (("Goal" :use ((:instance mod+rewrite-2 (b (* b (mod c (p)))))))))

(defthm mod*rewrite-6
  (implies (and (integerp a) (integerp b) (integerp c) (integerp d) (integerp e))
           (equal (mod (+ a (* b c d (mod e (p)))) (p))
                  (mod (+ a (* b c d e)) (p))))
  :hints (("Goal" :use ((:instance mod*rewrite-5 (b (* b c d)) (c e))))))

(defthm mod*rewrite-7
  (implies (and (integerp a) (integerp b) (integerp c) (integerp d) (integerp e))
           (equal (mod (* a b c d (mod e (p))) (p))
                  (mod (* a b c d e) (p))))
  :hints (("Goal" :use ((:instance mod*rewrite-2 (a (* a b c d)) (b e))))))

(defthm mod-rewrite-1
  (implies (and (integerp a) (integerp b))
           (equal (mod (- (mod a (p)) b) (p))
                  (mod (- a b) (p))))
  :hints (("Goal" :use ((:instance mod-sum (a (- b)) (b a) (n (p)))))))

(defthm mod-rewrite-2
  (implies (and (integerp a) (integerp b))
           (equal (mod (- a (mod b (p))) (p))
                  (mod (- a b) (p))))
  :hints (("Goal" :in-theory (enable mod-diff))))

(defthm mod-expt-rewrite-1
  (implies (and (integerp n)
                (not (zp k)))
           (equal (mod (expt (mod n (p)) k) (p))
                  (mod (* n (expt (mod n (p)) (1- k))) (p))))
  :hints (("Goal" :expand ((EXPT (MOD N (P)) K)))))

(defthm mod-expt-rewrite-2
  (implies (and (integerp n)
                (not (zp k))
                (equal (mod (expt (mod n (p)) (1- k)) (p))
                       (mod (expt n (1- k)) (p))))
           (equal (mod (expt (mod n (p)) k) (p))
                  (mod (expt n k) (p))))
  :hints (("Goal" :use ((:instance mod*rewrite-2 (a n) (b (expt (mod n (p)) (1- k))))))))

(defthm mod-expt-rewrite
  (implies (and (integerp n) (natp k))
           (equal (mod (expt (mod n (p)) k) (p))
                  (mod (expt n k) (p))))
  :hints (("Goal" :induct (fact k))))

(defthm mod-expt-rewrite-3
  (implies (and (integerp m) (integerp n) (natp k))
           (equal (mod (* m (expt (mod n (p)) k)) (p))
                  (mod (* m (expt n k)) (p)))))

(defthm mod-expt-rewrite-4
  (implies (and (integerp l) (integerp m) (integerp n) (natp k))
           (equal (mod (* l m (expt (mod n (p)) k)) (p))
                  (mod (* l m (expt n k)) (p))))
  :hints (("Goal" :use ((:instance mod-expt-rewrite-3 (m (* l m)))))))

(defthm mod-expt-rewrite-5
  (implies (and (integerp j) (integerp l) (integerp m) (integerp n) (natp k))
           (equal (mod (* j l m (expt (mod n (p)) k)) (p))
                  (mod (* j l m (expt n k)) (p))))
  :hints (("Goal" :use ((:instance mod-expt-rewrite-3 (m (* j l m)))))))

;; Why is this not in lib/basic.lisp?

(defthm mod-equal-0
  (implies (and (integerp a)
                (integerp b)
                (integerp n)
                (< 0 n))
           (iff (= (mod a n) (mod b n))
                (= (mod (- a b) n) 0)))
  :rule-classes ()
  :hints (("Goal" :use (mod-equal-int-reverse mod-equal-int
                        (:instance mod-0-int (m (- a b)))))))

(defthm natp-frcp
  (implies (integerp n)
           (natp (frcp n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable frcp))))

(defthmd frcp-lemma
  (implies (and (integerp n) (not (= (mod n (p)) 0)))
           (equal (mod (* n (frcp n)) (p))
                  1))
  :hints (("Goal" :in-theory (enable frcp)
                  :use ((:instance divides-mod-0 (n (p)) (a n))
                        (:instance fermat (p (p)) (m n))))))

(defthmd frcp-inverts
  (implies (and (fp n) (not (= n 0)))
           (equal (f* (frcp n) n)
                  1))
  :hints (("Goal" :use (frcp-lemma))))

(defthm frcp-cor
  (implies (and (integerp n) (not (= (mod n (p)) 0)) (integerp m))
           (equal (mod (* m n (frcp n)) (p))
                  (mod m (p))))
  :rule-classes ()
  :hints (("Goal" :use (frcp-lemma
                        (:instance mod*rewrite-1 (a (* n (frcp n))) (b m))))))

(defthmd frcp-prod
  (implies (and (integerp n) (integerp m))
           (equal (frcp (* n m))
                  (mod (* (frcp n) (frcp m)) (p))))
  :hints (("Goal" :in-theory (enable p frcp))))

(defthm mod-frcp
  (implies (integerp n)
           (equal (mod (frcp n) (p))
                  (frcp n)))
  :hints (("Goal" :in-theory (enable frcp))))

(defthm frcp-mod
  (implies (integerp n)
           (equal (frcp (mod n (p)))
                  (frcp n)))
  :hints (("Goal" :in-theory (enable mod-expt-rewrite frcp))))

(defthm prime-divides-1
  (implies (primep p)
           (not (divides p 1)))
  :hints (("Goal" :use ((:instance divides-leq (x p) (y 1))))))

(defthmd frcp-expt
 (implies (and (integerp n) (natp k))
          (equal (frcp (expt n k))
                 (mod (expt (frcp n) k) (p))))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :use ((:instance frcp-prod (m (expt n (1- k))))))
          ("Subgoal *1/1" :use ((:instance divides-mod-0 (n (p)) (a 1))))))

(defthmd prime-divides-expt
  (implies (and (integerp n)
                (primep p)
                (natp k)
                (divides p (expt n k)))
           (divides p n))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :use ((:instance euclid (a n) (b (expt n (1- k))))))))

(defthmd mod-expt-0
  (implies (and (integerp n)
                (primep p)
                (natp k)
                (= (mod (expt n k) p) 0))
           (equal (mod n p) 0))
  :hints (("Goal" :use (prime-divides-expt
                        (:instance divides-mod-0 (a n) (n p))
                        (:instance divides-mod-0 (a (expt n k)) (n p))))))

(defthmd mod-frcp-0
  (implies (and (integerp n)
                (= (mod (frcp n) (p)) 0))
           (equal (mod n (p)) 0))
  :hints (("Goal" :in-theory (enable frcp)
                  :use ((:instance mod-expt-0 (p (p)) (k (- (p) 2)))))))

(defthmd f/cancel
  (implies (and (integerp n)
                (integerp m)
                (integerp  a)
                (not (= (mod a (p)) 0)))
           (equal (f/ (* a n) (* a m))
                  (f/ n m)))
  :hints (("Goal" :use ((:instance frcp-cor (m (* n (frcp m))) (n a)))
                  :in-theory (enable frcp-prod))))

(defthmd f/mod
  (implies (and (integerp n)
                (integerp m)
                (not (= (mod m (p)) 0)))
           (equal (f/ (mod n (p)) (mod m (p)))
                  (f/ n m))))

(local-defthmd f*/-1
  (implies (and (integerp n)
                (integerp m)
                (integerp a)
                (not (= (mod a (p)) 0))
                (= (mod (* n a) (p))
                   (mod m (p))))
           (equal (mod (* (mod (* n a) (p)) (frcp a)) (p))
                  (mod (* (mod m (p)) (frcp a)) (p)))))

(defthmd f*/
  (implies (and (integerp n)
                (integerp m)
                (integerp a)
                (not (= (mod a (p)) 0))
                (= (mod (* n a) (p))
                   (mod m (p))))
           (equal (f/ m a) (mod n (p))))
  :hints (("Goal" :use (f*/-1 (:instance frcp-cor (m n) (n a))))))

(defthmd odd-char
  (implies (and (integerp n) (not (= (mod n (p)) 0)))
           (not (equal (mod (* 2 n) (p)) 0)))
  :hints (("Goal" :use ((:instance divides-mod-0 (a n) (n (p)))
                        (:instance divides-mod-0 (a (* 2 n)) (n (p)))
                        (:instance divides-leq (x (p)) (y 2))
                        (:instance euclid (p (p)) (a 2) (b n))))))

(defun inf () 'infinity)

(defun x (r) (car r))

(defun y (r) (cdr r))

(defun a () 486662)

(defund ecp (r)
  (or (eql r (inf))
      (and (fp (x r))
           (fp (y r))
           (= (fexpt (y r) 2)
              (f+ (f+ (fexpt (x r) 3)
                      (f* (a) (fexpt (x r) 2)))
                  (x r))))))

(defthm integerp-ec-x
  (implies (and (ecp r)
                (not (equal r (inf))))
           (integerp (car r)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable ecp))))

(defthm integerp-ec-y
  (implies (and (ecp r)
                (not (equal r (inf))))
           (integerp (cdr r)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable ecp))))

(local-defthmd a2-4-nonresidue-1
  (equal (fast-mod-expt (- (expt (a) 2) 4) (/ (1- (p)) 2) (p))
         (1- (p)))
  :hints (("Goal" :in-theory (enable p))))

(local-defthmd a2-4-nonresidue-2
  (not (divides (p) (- (expt (a) 2) 4)))
  :hints (("Goal" :in-theory (enable p))))

(defthm natp-p-1/2
  (natp (+ -1/2 (* 1/2 (P))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable p))))

(defthm a2-4-nonresidue
  (not (residue (- (expt (a) 2) 4) (p)))
  :hints (("Goal" :use (a2-4-nonresidue-1 a2-4-nonresidue-2
                        (:instance euler-criterion (m (- (expt (a) 2) 4)) (p (p)))))))

(local-defthmd ec-x-0-1
  (implies (and (integerp x)
                (ecp (cons x 0)))
           (equal (mod (+ (expt x 3) (* (a) (expt x 2)) x) (p))
                  0))
  :hints (("Goal" :in-theory (enable ecp))))

(local-defthmd ec-x-0-2
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (+ (expt x 2) (* (a) x) 1) (p))
                  0))
  :hints (("Goal" :use (ec-x-0-1 (:instance mod*0 (m x) (n (+ (expt x 2) (* (a) x) 1)))))))

(local-defthmd ec-x-0-3
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (* x (- (a) 2)) (p))
                  (mod (- (expt (1+ x) 2)) (p))))
  :hints (("Goal" :use (ec-x-0-2 (:instance mod-equal-0 (a (* x (- (a) 2))) (b (- (expt (1+ x) 2))) (n (p)))))))

(local-defthmd ec-x-0-4
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (* x (+ (a) 2)) (p))
                  (mod (- (expt (1- x) 2)) (p))))
  :hints (("Goal" :use (ec-x-0-2 (:instance mod-equal-0 (a (* x (+ (a) 2))) (b (- (expt (1- x) 2))) (n (p)))))))

(local-defthmd ec-x-0-5
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (* (mod (* x (+ (a) 2)) (p))
                          (mod (* x (- (a) 2)) (p)))
                       (p))
                  (mod (* (mod (- (expt (1- x) 2)) (p))
                          (mod (- (expt (1+ x) 2)) (p)))
                       (p))))
  :hints (("Goal" :use (ec-x-0-3 ec-x-0-4))))

(local-defthmd ec-x-0-6
  (implies (integerp x)
           (equal (mod (* (mod (* x (+ (a) 2)) (p))
                          (mod (* x (- (a) 2)) (p)))
                       (p))
                  (mod (* (expt x 2) (- (expt (a) 2) 4))
                       (p)))))

(local-defthmd ec-x-0-7
  (implies (integerp x)
           (equal (mod (* (mod (- (expt (1- x) 2)) (p))
                          (mod (- (expt (1+ x) 2)) (p)))
                       (p))
                  (mod (expt (1- (expt x 2)) 2)
                       (p))))
  :hints (("Goal" :use ((:instance mod*rewrite-1 (a (- (expt (1- x) 2))) (b (mod (- (expt (1+ x) 2)) (p))))
                        (:instance mod*rewrite-2 (a (- (expt (1- x) 2))) (b (- (expt (1+ x) 2))))))))

(local-defthmd ec-x-0-8
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (* (expt x 2) (- (expt (a) 2) 4)) (p))
                  (mod (expt (1- (expt x 2)) 2) (p))))
  :hints (("Goal" :use (ec-x-0-5 ec-x-0-6 ec-x-0-7)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd ec-x-0-9
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0))
                (integerp (* (expt x 2) (- (expt (a) 2) 4)))
                (integerp (expt (1- (expt x 2)) 2))
                (integerp (frcp (expt x 2)))
                (not (zp (p))))
           (equal (mod (* (* (expt x 2) (- (expt (a) 2) 4)) (frcp (expt x 2))) (p))
                  (mod (* (expt (1- (expt x 2)) 2) (frcp (expt x 2))) (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (ec-x-0-8
                        (:instance mod-times-mod (a (* (expt x 2) (- (expt (a) 2) 4)))
                                                 (b (expt (1- (expt x 2)) 2))
                                                 (c (frcp (expt x 2)))
                                                 (n (p)))))))

(local-defthmd ec-x-0-10
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (* (expt x 2) (frcp (expt x 2)) (- (expt (a) 2) 4)) (p))
                  (mod (* (frcp (expt x 2)) (expt (1- (expt x 2)) 2)) (p))))
  :hints (("Goal" :use (ec-x-0-9))))

(local-defthmd ec-x-0-11
  (implies (integerp x)
           (equal (mod (* (frcp (expt x 2)) (expt (1- (expt x 2)) 2)) (p))
                  (mod (expt (* (frcp x) (1- (expt x 2))) 2) (p))))
  :hints (("Goal" :in-theory (enable frcp-expt)
                  :use ((:instance mod*rewrite-1 (a (expt (frcp x) 2)) (b (expt (1- (expt x 2)) 2)))))))

(local-defthmd ec-x-0-12
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (* (expt x 2) (frcp (expt x 2)) (- (expt (a) 2) 4)) (p))
                  (mod (expt (* (frcp x) (1- (expt x 2))) 2) (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (ec-x-0-10 ec-x-0-11))))

(local-defthmd ec-x-0-13
  (implies (and (integerp x)
                (not (= (mod x (p)) 0))
                (ecp (cons x 0)))
           (equal (mod (- (expt (a) 2) 4) (p))
                  (mod (expt (* (frcp x) (1- (expt x 2))) 2) (p))))
  :hints (("Goal" :use (ec-x-0-12
                        (:instance mod*0 (m x) (n x))
                        (:instance frcp-cor (m (- (expt (a) 2) 4)) (n (expt x 2)))))))

(local-defthmd ec-x-0-14
    (implies (and (primep p)
                  (integerp m)
                  (not (divides p m))
		  (not (residue m p))
		  (natp j)
		  (< j p))
	     (not (equal (mod (* j j) p) (mod m p))))
  :hints (("Goal" :in-theory (enable residue)
		  :use ((:instance divides-mod-0 (n p) (a m))
                        (:instance not-res-no-root-lemma (n (1- p)))))))

(local-defthmd ec-x-0-15
  (implies (integerp j)
           (and (natp (mod j (p)))
                (< (mod j (p)) (p))
                (= (mod (* (mod j (p)) (mod j (p))) (p))
                   (mod (* j j) (p))))))

(local-defthm ec-x-0-16
    (implies (and (integerp m)
                  (not (divides (p) m))
		  (not (residue m (p)))
		  (integerp j))
	     (not (equal (mod (* j j) (p)) (mod m (p)))))
  :hints (("Goal" :use (ec-x-0-15
                        (:instance divides-mod-0 (n (p)) (a m))
                        (:instance ec-x-0-14 (j (mod j (p))) (p (p)))))))

(local-defthmd ec-x-0-17
  (implies (and (integerp x)
                (ecp (cons x 0)))
           (= (mod x (p)) 0))
  :hints (("Goal" :use (ec-x-0-13
                        a2-4-nonresidue-2
                        a2-4-nonresidue
                        (:instance ec-x-0-16 (m (- (expt (a) 2) 4))
                                             (j (* (frcp x) (1- (expt x 2)))))))))

(defthm ec-x-0
  (implies (ecp (cons x 0))
           (= x 0))
  :rule-classes ()
  :hints (("Goal" :use (ec-x-0-17)
                  :in-theory (enable ecp))))

(defthm ec-y-0
  (implies (ecp (cons 0 y))
           (= y 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-expt-0 (p (p)) (n y) (k 2)))
                  :in-theory (enable ecp))))

(defund ec- (r)
  (if (equal r (inf))
      (inf)
    (cons (x r) (f- 0 (y r)))))

(defund ec+ (r1 r2)
  (if (equal r1 (inf))
      r2
    (if (equal r2 (inf))
        r1
      (if (equal r2 (ec- r1))
          (inf)
        (let* ((x1 (x r1)) (y1 (y r1)) (x2 (x r2)) (y2 (y r2))
               (lam (if (= x1 x2)
                       (f/ (f+ (f+ (f* 3 (fexpt x1 2))
                                   (f* (f* 2 (a)) x1))
                               1)
                           (f* 2 y1))
                     (f/ (f- y1 y2)
                         (f- x1 x2))))
              (x (f- (f- (f- (fexpt lam 2)
                             (a))
                         x1)
                     x2))
              (y (f- (f* lam (f- x1 x))
                     y1)))
          (cons x y))))))

(defund ec+slope (r1 r2)
  (if (= (x r1) (x r2))
      (f/ (f+ (f+ (f* 3 (fexpt (x r1) 2))
                  (f* (f* 2 (a)) (x r1)))
              1)
          (f* 2 (y r1)))
   (f/ (f- (y r1) (y r2))
       (f- (x r1) (x r2)))))

(defthm integerp-ec+slope
  (implies (and (ecp r1) (consp r1) (ecp r2) (consp r2))
           (integerp (ec+slope r1 r2)))
  :hints (("Goal" :in-theory (enable ec+slope ecp)))
  :rule-classes (:type-prescription :rewrite))

(defund ec+x (r1 r2)
  (f- (f- (f- (fexpt (ec+slope r1 r2) 2)
              (a))
          (x r1))
      (x r2)))

(defun ec+y (r1 r2)
  (f- (f* (ec+slope r1 r2) (f- (x r1) (ec+x r1 r2)))
      (y r1)))

(defthmd ec+rewrite
  (implies (and (consp r1)
                (consp r2)
                (not (equal r2 (ec- r1))))
           (equal (ec+ r1 r2)
                  (cons (ec+x r1 r2) (ec+y r1 r2))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(inf ec+ ec+slope ec+x ec+y)))))

(defthmd ec--
  (implies (ecp r)
           (equal (ec- (ec- r)) r))
  :hints (("Goal" :in-theory (enable ecp ec-)
                  :use ((:instance mod-rewrite-2 (a 0) (b (- (y r))))))))

(defthm ec-ecp
  (implies (ecp r)
           (ecp (ec- r)))
  :hints (("Goal" :in-theory (enable ecp ec-)
                  :use ((:instance mod-rewrite-2 (a 0) (b (- (y r))))))))

(defthm consp-ec-
  (implies (consp r)
           (consp (ec- r)))
  :hints (("Goal" :in-theory (enable ec-))))

(defthm car-ec-
  (implies (consp r)
           (equal (car (ec- r))
                  (car r)))
  :hints (("Goal" :in-theory (enable ec-))))

(defthm cdr-ec-
  (implies (consp r)
           (equal (cdr (ec- r))
                  (f- 0 (cdr r))))
  :hints (("Goal" :in-theory (enable ec-))))

(defthmd ec-inverse-unique
  (implies (and (ecp r1) (ecp r2))
           (iff (equal (ec+ r1 r2) (inf))
                (equal r2 (ec- r1))))
  :hints (("Goal" :in-theory (enable ec- ec+))))

(local-defthmd x=-1
  (implies (and (ecp r1)
                (ecp r2)
                (not (equal r1 (inf)))
                (not (equal r2 (inf)))
                (= (x r1) (x r2)))
          (equal (mod (expt (y r1) 2) (p))
                 (mod (expt (y r2) 2) (p))))
  :hints (("Goal" :in-theory (enable ecp))))

(local-defthmd x=-2
  (implies (and (ecp r1)
                (ecp r2)
                (not (equal r1 (inf)))
                (not (equal r2 (inf)))
                (= (x r1) (x r2)))
          (equal (mod (- (expt (y r1) 2) (expt (y r2) 2)) (p))
                 0))
  :hints (("Goal" :use (x=-1
                        (:instance mod-equal-0 (a (expt (y r1) 2)) (b (expt (y r2) 2)) (n (p))))
                  :in-theory (enable ecp))))

(local-defthm x=-3
  (implies (and (ecp r1)
                (ecp r2)
                (not (equal r1 (inf)))
                (not (equal r2 (inf)))
                (= (x r1) (x r2)))
          (or (equal (mod (+ (y r1) (y r2)) (p)) 0)
              (equal (mod (- (y r1) (y r2)) (p)) 0)))
  :rule-classes ()
  :hints (("Goal" :use (x=-2
                        (:instance mod*0 (n (+ (y r1) (y r2))) (m (- (y r1) (y r2)))))
                  :in-theory (enable ecp))))

(local-defthm x=-4
  (implies (and (ecp r1)
                (ecp r2)
                (not (equal r1 (inf)))
                (not (equal r2 (inf)))
                (= (x r1) (x r2)))
          (or (equal (y r1) (y r2))
              (equal (y r1) (f- 0 (y r2)))))
  :rule-classes ()
  :hints (("Goal" :use (x=-3
                        (:instance mod-equal-0 (a (y r1)) (b (y r2)) (n (p)))
                        (:instance mod-equal-0 (a (y r1)) (b (- (y r2))) (n (p))))
                  :in-theory (enable ecp))))

(defthm x=
  (implies (and (ecp r1)
                (ecp r2)
                (not (equal r1 (inf)))
                (not (equal r2 (inf))))
          (iff (= (x r1) (x r2))
               (or (equal r1 r2)
                   (equal r1 (ec- r2)))))
  :rule-classes ()
  :hints (("Goal" :use (x=-4)
                  :in-theory (enable ecp ec-))))

(local-defthm r=-r-1
  (implies (and (ecp r)
                (not (equal r (inf)))
                (= (y r) (f- 0 (y r))))
           (equal (y r) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ecp)
                  :use ((:instance odd-char (n (y r)))
                        (:instance mod-equal-0 (a (y r)) (b (- (y r))) (n (p)))))))

(defun o () '(0 . 0))

(defthm r=-r
  (implies (ecp r)
           (iff (equal r (ec- r))
                (or (equal r (inf))
                    (equal r (o)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ecp ec-)
                  :use (r=-r-1
                        (:instance ec-x-0 (x (x r)))))))

;; we shall constrain values of these variables to satisfy the EC requirement:

(encapsulate (((y0) => *) ((y1) => *) ((y2) => *) ((x0) => *) ((x1) => *) ((x2) => *))
  (local (defun y0 () 0))
  (local (defun y1 () 0))
  (local (defun y2 () 0))
  (local (defun x0 () 0))
  (local (defun x1 () 0))
  (local (defun x2 () 0))
  (defun p0 () (cons (x0) (y0)))
  (defun p1 () (cons (x1) (y1)))
  (defun p2 () (cons (x2) (y2)))
  (defthm ecp-assumption
    (and (ecp (p0)) (ecp (p1)) (ecp (p2)))))

(defthm natp-x0
  (natp (x0))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption)))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-x1
  (natp (x1))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption)))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-x2
  (natp (x2))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption)))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-y0
  (natp (y0))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption)))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-y1
  (natp (y1))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption)))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-y2
  (natp (y2))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption)))
  :rule-classes (:type-prescription :rewrite))

(defthm mod-xi-yi
  (and (equal (mod (x0) (p)) (x0))
       (equal (mod (x1) (p)) (x1))
       (equal (mod (x2) (p)) (x2))
       (equal (mod (y0) (p)) (y0))
       (equal (mod (y1) (p)) (y1))
       (equal (mod (y2) (p)) (y2)))
  :hints (("Goal" :in-theory (enable ecp)
                  :use (ecp-assumption))))

(local-defthmd p0+p1<>p0-1
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (- (y0)) (p)) (y0))))
  :hints (("goal" :use (ecp-assumption
                        (:instance ec-inverse-unique (r2 (p1)) (r1 (p0))))
                  :in-theory (enable ec+rewrite))))

(local-defthmd p0+p1<>p0-2
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (f+ (y0) (y0)) 0)))
  :hints (("Goal" :use (ecp-assumption p0+p1<>p0-1
                        (:instance mod-equal-0 (a (y0)) (b (- (y0))) (n (p)))))))

(local-defthmd p0+p1<>p0-3
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (y0) 0)))
  :hints (("Goal" :use (ecp-assumption p0+p1<>p0-2
                        (:instance odd-char (n (y0)))))))

(local-defthmd p0+p1<>p0-4
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (p0) (o))))
  :hints (("Goal" :use (ecp-assumption p0+p1<>p0-3
                        (:instance ec-x-0 (x (x0)))))))

(local-defthmd p0+p1<>p0-5
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (not (= (x1) 0))))
  :hints (("Goal" :use (ecp-assumption p0+p1<>p0-4
                        (:instance ec-y-0 (y (y1)))))))

(local-defthmd p0+p1<>p0-6
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (- (expt (ec+slope (p0) (p1)) 2) (+ (a) (x1))) (p)) 0)))
  :hints (("goal" :use (ecp-assumption p0+p1<>p0-4
                        (:instance ec-inverse-unique (r2 (p1)) (r1 (p0))))
                  :expand ((EC+X '(0 . 0) (CONS (X1) (Y1))))
                  :in-theory (enable ec+rewrite))))

(local-defthmd p0+p1<>p0-7
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (ec+slope (p0) (p1))
                    (f/ (y1) (x1)))))
  :hints (("goal" :use (p0+p1<>p0-4 p0+p1<>p0-5
                        (:instance f/cancel (a -1) (n (y1)) (m (x1)))
                        (:instance divides-minus (y (x1))(x (p)))
                        (:instance divides-minus (y (- (x1)))(x (p)))
                        (:instance divides-mod-0 (a (x1))(n (p)))
                        (:instance divides-mod-0 (a (- (x1)))(n (p))))
                 :in-theory (enable ec+slope))))

(local-defthmd p0+p1<>p0-8
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (expt (ec+slope (p0) (p1)) 2) (p))
                    (mod (+ (a) (x1)) (p)))))
  :hints (("goal" :use (ecp-assumption p0+p1<>p0-6
                        (:instance mod-equal-0 (a (expt (ec+slope (p0) (p1)) 2)) (b (+ (a) (x1))) (n (p)))))))

(local-defthmd p0+p1<>p0-9
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (expt (* (y1) (frcp (x1))) 2) (p))
                    (mod (+ (a) (x1)) (p)))))
  :hints (("goal" :use (p0+p1<>p0-7 p0+p1<>p0-8))))

(local-defthmd p0+p1<>p0-10
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (expt (* (y1) (x1) (frcp (x1))) 2) (p))
                    (mod (* (expt (x1) 2) (+ (a) (x1))) (p)))))
  :hints (("goal" :use (p0+p1<>p0-9
                        (:instance mod-times-mod (a (expt (* (y1) (frcp (x1))) 2))
                                                 (b (+ (a) (x1)))
                                                 (c (expt (x1) 2))
                                                 (n (p)))))))

(local-defthmd p0+p1<>p0-11
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (expt (y1) 2) (p))
                    (mod (* (expt (x1) 2) (+ (a) (x1))) (p)))))
  :hints (("goal" :in-theory (enable frcp-expt)
                  :use (p0+p1<>p0-5 p0+p1<>p0-10
                        (:instance mod-expt-0 (p (p)) (k 2) (n (x1)))
                        (:instance frcp-cor (m (expt (y1) 2)) (n (expt (x1) 2)))))))

(local-defthmd p0+p1<>p0-12
  (let ((p (ec+ (p0) (p1))))
    (implies (equal p (p0))
             (equal (mod (+ (x1) (* (expt (x1) 2) (+ (a) (x1))))  (p))
                    (mod (* (expt (x1) 2) (+ (a) (x1))) (p)))))
  :hints (("goal" :in-theory (enable ecp)
                  :use (ecp-assumption p0+p1<>p0-11))))

(defthm p0+p1<>p0
  (not (equal (ec+ (p0) (p1)) (p0)))
  :hints (("goal" :use (p0+p1<>p0-5 p0+p1<>p0-12
                        (:instance mod-equal-0 (a (+ (x1) (* (expt (x1) 2) (+ (a) (x1)))))
                                               (b (* (expt (x1) 2) (+ (a) (x1))))
                                               (n (p)))))))

(local-defthmd p0+p1=p0-p1-1
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (equal (p0) (ec- (p1))))
           (equal (ec+ (p0) (p0)) (inf)))
  :hints (("Goal" :use (ecp-assumption
                        (:instance ec-- (r (p1)))
                        (:instance ec-inverse-unique (r1 (ec- (p1))) (r2 (p1)))))))

(local-defthmd p0+p1=p0-p1-2
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (equal (p0) (ec- (p1))))
           (equal (p0) (o)))
  :hints (("Goal" :use (ecp-assumption p0+p1=p0-p1-1
                        (:instance ec-inverse-unique (r1 (p0)) (r2 (p0)))
                        (:instance r=-r (r (p0)))))))

(local-defthmd p0+p1=p0-p1-3
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (equal (p0) (p1)))
           (equal (ec+ (p0) (p0)) (inf)))
  :hints (("Goal" :use (ecp-assumption
                        (:instance ec-inverse-unique (r1 (p0)) (r2 (ec- (p0))))))))

(local-defthmd p0+p1=p0-p1-4
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (equal (p0) (p1)))
           (equal (p0) (o)))
  :hints (("Goal" :use (ecp-assumption p0+p1=p0-p1-3
                        (:instance ec-inverse-unique (r1 (p0)) (r2 (p0)))
                        (:instance r=-r (r (p0)))))))

(local-defthmd p0+p1=p0-p1-5
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (equal (x0) (x1)))
           (equal (p0) (o)))
  :hints (("Goal" :use (ecp-assumption p0+p1=p0-p1-2 p0+p1=p0-p1-4
                        (:instance x= (r1 (p0)) (r2 (p1)))))))

(local-defthmd p0+p1=p0-p1-6
  (implies (not (equal (p0) (ec- (p1))))
           (not (equal (p1) (ec- (p0)))))
  :hints (("Goal" :use (ecp-assumption (:instance ec-- (r (p0)))))))

(local-defthmd p0+p1=p0-p1-7
  (implies (not (equal (p0) (ec- (p1))))
           (equal (x (ec+ (p0) (p1)))
                  (mod (- (expt (ec+slope (p0) (p1)) 2)
                          (+ (a) (x0) (x1)))
                       (p))))
  :hints (("Goal" :use (ecp-assumption p0+p1=p0-p1-6)
                  :in-theory (enable ec+x ec+rewrite))))

(local-defthmd p0+p1=p0-p1-8
  (implies (equal (ec- (p0)) (ec- (p1)))
           (equal (p1) (p0)))
  :hints (("Goal" :use (ecp-assumption (:instance ec-- (r (p0))) (:instance ec-- (r (p1)))))))

(local-defthmd p0+p1=p0-p1-9
  (implies (not (equal (p0) (p1)))
           (equal (x (ec+ (p0) (ec- (p1))))
                  (ec+x (p0) (ec- (p1)))))
  :hints (("Goal" :use (ecp-assumption p0+p1=p0-p1-8)
                  :in-theory (enable ec+rewrite))))

(local-defthmd p0+p1=p0-p1-10
  (equal (ec+x (p0) (ec- (p1)))
         (f- (f- (f- (fexpt (ec+slope (p0) (ec- (p1))) 2)
                     (a))
                 (x (p0)))
             (x (ec- (p1)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :expand ((:free (r1 r2) (ec+x r1 r2))))))

(local-defthmd p0+p1=p0-p1-11
  (implies (integerp s)
           (equal (mod (- (expt s 2)
                          (+ (a) (x0) (x1)))
                       (p))
                  (f- (f- (f- (fexpt s 2)
                              (a))
                          (x (p0)))
                      (x (ec- (p1))))))
  :hints (("Goal" :use (ecp-assumption))))

(local-defthmd p0+p1=p0-p1-12
  (integerp (ec+slope (p0) (ec- (p1))))
  :hints (("Goal" :use (ecp-assumption))))

(local-defthmd p0+p1=p0-p1-13
  (implies (not (equal (p0) (p1)))
           (equal (x (ec+ (p0) (ec- (p1))))
                  (mod (- (expt (ec+slope (p0) (ec- (p1))) 2)
                          (+ (a) (x0) (x1)))
                       (p))))
  :hints (("Goal" :use (p0+p1=p0-p1-9 p0+p1=p0-p1-10 p0+p1=p0-p1-12
                        (:instance p0+p1=p0-p1-11 (s (ec+slope (p0) (ec- (p1))))))
                  :in-theory (theory 'minimal-theory))))

(local-defthmd p0+p1=p0-p1-14
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (equal (mod (- (expt (ec+slope (p0) (p1)) 2)
                          (+ (a) (x0) (x1)))
                       (p))
                  (mod (- (expt (ec+slope (p0) (ec- (p1))) 2)
                          (+ (a) (x0) (x1)))
                       (p))))
  :hints (("Goal" :use (ecp-assumption p0+p1=p0-p1-7 p0+p1=p0-p1-13
                        (:instance x= (r1 (p0)) (r2 (p1)))))))

(in-theory (disable (ec+slope) (ec-) (ec+)))

(local-defthmd p0+p1=p0-p1-15
  (integerp (ec+slope (p0) (p1)))
  :hints (("Goal" :use (ecp-assumption))))

(local-defthmd p0+p1=p0-p1-16
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (equal (mod (expt (ec+slope (p0) (p1)) 2) (p))
                  (mod (expt (ec+slope (p0) (ec- (p1))) 2) (p))))
  :hints (("Goal" :in-theory (disable integerp-ec+slope)
                  :use (p0+p1=p0-p1-12 ecp-assumption p0+p1=p0-p1-14 p0+p1=p0-p1-15
                        (:instance mod-plus-mod (n (p))
                                                (a (- (expt (ec+slope (p0) (p1)) 2) (+ (a) (x0) (x1))))
                                                (b (- (expt (ec+slope (p0) (ec- (p1))) 2) (+ (a) (x0) (x1))))
                                                (c (+ (a) (x0) (x1))))))))

(defthmd ec+slope-rewrite
  (implies (and (ecp r1) (ecp r2) (consp r1) (consp r2) (not (= (x r1) (x r2))))
           (equal (ec+slope r1 r2)
                  (mod (* (- (y r1) (y r2)) (frcp (- (x r1) (x r2)))) (p))))
  :hints (("Goal" :in-theory (enable ec+slope))))

(defthmd ec+slope-2-rewrite
  (implies (and (ecp r1) (ecp r2) (consp r1) (consp r2) (not (= (x r1) (x r2))))
           (equal (mod (expt (ec+slope r1 r2) 2) (p))
                  (mod (* (expt (- (y r1) (y r2)) 2) (expt (frcp (- (x r1) (x r2))) 2)) (p))))
  :hints (("Goal" :in-theory (enable ec+slope-rewrite)
                  :use ((:instance mod-expt-rewrite (n (* (- (y r1) (y r2)) (frcp (- (x r1) (x r2))))) (k 2))))))

(local-defthmd p0+p1=p0-p1-17
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (equal (mod (* (expt (- (y0) (y1)) 2) (expt (frcp (- (x0) (x1))) 2)) (p))
                  (mod (* (expt (- (y0) (mod (- (y1)) (p))) 2) (expt (frcp (- (x0) (x1))) 2)) (p))))
  :hints (("Goal" :in-theory (enable ec+slope-2-rewrite)
                  :use (ecp-assumption p0+p1=p0-p1-16))))

(local-defthmd p0+p1=p0-p1-18
  (implies (and (integerp a1)
                (integerp a2)
                (integerp b)
                (not (= (mod b (p)) 0))
                (equal (mod (* a1 (expt (frcp b) 2)) (p))
                       (mod (* a2 (expt (frcp b) 2)) (p))))
           (equal (mod (* a1 (expt (frcp b) 2) (expt b 2)) (p))
                  (mod (* a2 (expt (frcp b) 2) (expt b 2)) (p))))
  :hints (("Goal" :use ((:instance mod-times-mod (a (* a1 (expt (frcp b) 2)))
                                                  (b (* a2 (expt (frcp b) 2)))
                                                  (c (expt b 2))
                                                  (n (p)))))))

(local-defthmd p0+p1=p0-p1-19
  (implies (and (integerp a)
                (integerp b)
                (not (= (mod b (p)) 0)))
           (equal (mod (* a (expt (frcp b) 2) (expt b 2)) (p))
                  (mod (* a b (frcp b)) (p))))
  :hints (("Goal" :use ((:instance frcp-cor (m (* a b (frcp b))) (n b))))))

(local-defthmd p0+p1=p0-p1-20
  (implies (and (integerp a)
                (integerp b)
                (not (= (mod b (p)) 0)))
           (equal (mod (* a b (frcp b)) (p))
                  (mod a (p))))
  :hints (("Goal" :use ((:instance frcp-cor (m a) (n b))))))

(local-defthmd p0+p1=p0-p1-21
  (implies (and (integerp a1)
                (integerp a2)
                (integerp b)
                (not (= (mod b (p)) 0))
                (equal (mod (* a1 (expt (frcp b) 2)) (p))
                       (mod (* a2 (expt (frcp b) 2)) (p))))
           (equal (mod a1 (p))
                  (mod a2 (p))))
  :hints (("Goal" :use (p0+p1=p0-p1-18
                        (:instance p0+p1=p0-p1-19 (a a1))
                        (:instance p0+p1=p0-p1-19 (a a2))
                        (:instance p0+p1=p0-p1-20 (a a1))
                        (:instance p0+p1=p0-p1-20 (a a2)))
                  :in-theory (theory 'minimal-theory))))

(local-defthmd p0+p1=p0-p1-22
  (implies (not (equal (x0) (x1)))
           (and (integerp (expt (- (y0) (y1)) 2))
                (integerp (expt (- (y0) (mod (- (y1)) (p))) 2))
                (integerp (- (x0) (x1)))
                (not (= (mod (- (x0) (x1)) (p)) 0))))
  :hints (("Goal" :cases ((< (x0) (x1))) :in-theory (enable ecp) :use (ecp-assumption))))

(local-defthmd p0+p1=p0-p1-23
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (equal (mod (expt (- (y0) (y1)) 2) (p))
                  (mod (expt (- (y0) (mod (- (y1)) (p))) 2) (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p0+p1=p0-p1-17 p0+p1=p0-p1-22
                        (:instance p0+p1=p0-p1-21 (a1 (expt (- (y0) (y1)) 2))
                                                  (a2 (expt (- (y0) (mod (- (y1)) (p))) 2))
                                                  (b (- (x0) (x1))))))))

(local-defthmd p0+p1=p0-p1-24
  (equal (mod (expt (- (y0) (mod (- (y1)) (p))) 2) (p))
         (mod (expt (mod (- (y0) (mod (- (y1)) (p))) (p)) 2) (p)))
  :hints (("Goal" :use ((:instance mod-expt-rewrite (n (- (y0) (mod (- (y1)) (p)))) (k 2))))))

(local-defthmd p0+p1=p0-p1-25
  (equal (mod (- (y0) (mod (- (y1)) (p))) (p))
         (mod (+ (y0) (y1)) (p))))

(local-defthmd p0+p1=p0-p1-26
  (equal (mod (expt (- (y0) (mod (- (y1)) (p))) 2) (p))
         (mod (expt (mod (+ (y0) (y1)) (p)) 2) (p)))
  :hints (("Goal" :use (p0+p1=p0-p1-24 p0+p1=p0-p1-25))))

(local-defthmd p0+p1=p0-p1-27
  (equal (mod (expt (mod (+ (y0) (y1)) (p)) 2) (p))
         (mod (expt (+ (y0) (y1)) 2) (p))))

(local-defthmd p0+p1=p0-p1-28
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (equal (mod (expt (- (y0) (y1)) 2) (p))
                  (mod (expt (+ (y0) (y1)) 2) (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p0+p1=p0-p1-23 p0+p1=p0-p1-26 p0+p1=p0-p1-27))))

(local-defthmd p0+p1=p0-p1-29
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (equal (mod (* 4 (y0) (y1)) (p))
                  0))
  :hints (("Goal" :use (p0+p1=p0-p1-28
                        (:instance mod-equal-0 (n (p))
                                               (a (expt (+ (y0) (y1)) 2))
                                               (b (expt (- (y0) (y1)) 2)))))))

(local-defthm p0+p1=p0-p1-30
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (or (equal (y0) 0)
               (equal (y1) 0)))
  :rule-classes ()
  :hints (("Goal" :use (p0+p1=p0-p1-29
                        (:instance mod*0 (n (* 4 (y0))) (m (y1)))
                        (:instance mod*0 (n 4) (m (y0)))))))

(local-defthm p0+p1=p0-p1-31
  (implies (and (equal (ec+ (p0) (p1))
                       (ec+ (p0) (ec- (p1))))
                (not (equal (x0) (x1))))
           (or (equal (p0) (o))
               (equal (p1) (o))))
  :rule-classes ()
  :hints (("Goal" :use (p0+p1=p0-p1-30 ecp-assumption
                        (:instance ec-x-0 (x (x0)))
                        (:instance ec-x-0 (x (x1)))))))

(defthm p0+p1=p0-p1
  (implies (equal (ec+ (p0) (p1))
                  (ec+ (p0) (ec- (p1))))
           (or (equal (p0) (o))
               (equal (p1) (o))))
  :rule-classes ()
  :hints (("Goal" :use (p0+p1=p0-p1-5 p0+p1=p0-p1-31))))
