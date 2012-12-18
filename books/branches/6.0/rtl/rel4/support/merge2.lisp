(in-package "ACL2")

; This book includes theorems we would like to put in merge, but cannot because
; that would introduce circular dependences.  For example, below we include the
; land book, but land includes land-proofs which includes merge.  (Perhaps
; land-proofs does not need to include merge, but we take the easy path here.)

; Finally, lemmas relating lior and cat.  The first of these use sumbits.

(include-book "merge")

(include-book "lior")

(local
 (defthmd lior-cat-1
   (implies (and (case-split (integerp n))
                 (case-split (integerp m))
                 (>= n 0)
                 (>= m 0)
                 (equal l (+ m n))
                 (integerp k)
                 (<= 0 k)
                 (< k l))
            (equal (bitn (lior (cat x1 m y1 n) (cat x2 m y2 n) l) k)
                   (bitn (cat (lior x1 x2 m) m (lior y1 y2 n) n) k)))
   :hints (("Goal" :in-theory (enable bitn-cat)))))

(defthmd lior-cat
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
		(> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (lior (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (lior x1 x2 m) m (lior y1 y2 n) n)))
  :hints (("Goal"
           :in-theory (e/d (sumbits-badguy-is-correct
                            sumbits-badguy-bounds
                            lior-cat-1)
                           (bitn-lior))
           :restrict ((sumbits-badguy-is-correct ((k (+ m n))))))))

(local
 (defthm lior-bits-1
   (implies (and (case-split (integerp n))
                 (case-split (integerp i))
                 (>= (1+ i) n))
            (equal (lior (bits x i 0) y n)
                   (lior x y n)))
   :hints (("Goal" :in-theory (e/d (lior) (lior-commutative))))))

(defthm lior-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (lior c (cat x2 m y2 n) l)
                  (cat (lior (bits c (+ -1 m n) n) x2 m)
                       m
                       (lior (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use (:instance lior-cat (x2 x2) (y2 y2) (m m) (n n)
                                  (x1 (bits c (+ -1 m n) n))
                                  (y1 (bits c (1- n) 0))
                                  (l (+ m n))))))

(include-book "logs")

(include-book "land")

(local (include-book "bvecp"))

(defthmd log=-cat-constant
  (implies (and (syntaxp (quotep k))
                (case-split (bvecp k (+ m n)))
                (case-split (bvecp x m))
                (case-split (bvecp y n))
                (case-split (integerp n))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (<= 0 m)))
           (equal (log= k (cat x m y n))
                  (land (log= x (bits k (+ -1 m n) n))
                        (log= y (bits k (1- n) 0))
                        1)))
  :hints (("Goal" :use (:instance cat-equal-rewrite (x2 x) (y2 y) (n n) (m m)
                                  (x1 (bits k (+ -1 m n) n))
                                  (y1 (bits k (1- n) 0)))
           :in-theory (enable log=))))

