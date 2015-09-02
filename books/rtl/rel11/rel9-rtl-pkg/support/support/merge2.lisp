; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

; This book includes theorems we would like to put in merge, but cannot because
; that would introduce circular dependences.  For example, below we include the
; land0 book, but land0 includes land0-proofs which includes merge.  (Perhaps
; land0-proofs does not need to include merge, but we take the easy path here.)

; Finally, lemmas relating lior0 and cat.  The first of these use sumbits.

(include-book "merge")

(include-book "lior0")

(local
 (defthmd lior0-cat-1
   (implies (and (case-split (integerp n))
                 (case-split (integerp m))
                 (>= n 0)
                 (>= m 0)
                 (equal l (+ m n))
                 (integerp k)
                 (<= 0 k)
                 (< k l))
            (equal (bitn (lior0 (cat x1 m y1 n) (cat x2 m y2 n) l) k)
                   (bitn (cat (lior0 x1 x2 m) m (lior0 y1 y2 n) n) k)))
   :hints (("Goal" :in-theory (enable bitn-cat)))))

(defthmd lior0-cat
  (implies (and (case-split (natp n))
                (case-split (integerp m))
                (> m 0)
                (equal l (+ m n)))
           (equal (lior0 (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (lior0 x1 x2 m) m (lior0 y1 y2 n) n)))
  :hints (("Goal"
           :in-theory (e/d (sumbits-badguy-is-correct
                            sumbits-badguy-bounds
                            lior0-cat-1)
                           (bitn-lior0))
           :restrict ((sumbits-badguy-is-correct ((k (+ m n))))))))

(local
 (defthm lior0-bits-1-alt
   (implies (and (case-split (integerp n))
                 (case-split (integerp i))
                 (>= (1+ i) n))
            (equal (lior0 (bits x i 0) y n)
                   (lior0 x y n)))
   :hints (("Goal" :in-theory (e/d (lior0) (lior0-commutative))))))

(defthm lior0-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (lior0 c (cat x2 m y2 n) l)
                  (cat (lior0 (bits c (+ -1 m n) n) x2 m)
                       m
                       (lior0 (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use (:instance lior0-cat (x2 x2) (y2 y2) (m m) (n n)
                                  (x1 (bits c (+ -1 m n) n))
                                  (y1 (bits c (1- n) 0))
                                  (l (+ m n))))))

; Copy the above events but modify for land.

(include-book "land0")

(local
 (defthmd land0-cat-1
   (implies (and (case-split (integerp n))
                 (case-split (integerp m))
                 (>= n 0)
                 (>= m 0)
                 (equal l (+ m n))
                 (integerp k)
                 (<= 0 k)
                 (< k l))
            (equal (bitn (land0 (cat x1 m y1 n) (cat x2 m y2 n) l) k)
                   (bitn (cat (land0 x1 x2 m) m (land0 y1 y2 n) n) k)))
   :hints (("Goal" :in-theory (enable bitn-cat)))))

(defthmd land0-cat
  (implies (and (case-split (natp n))
                (case-split (integerp m))
                (> m 0)
                (equal l (+ m n)))
           (equal (land0 (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (land0 x1 x2 m) m (land0 y1 y2 n) n)))
  :hints (("Goal"
           :in-theory (e/d (sumbits-badguy-is-correct
                            sumbits-badguy-bounds
                            land0-cat-1)
                           (bitn-land0))
           :restrict ((sumbits-badguy-is-correct ((k (+ m n))))))))

(local
 (defthm land0-bits-1-alt
   (implies (and (case-split (integerp n))
                 (case-split (integerp i))
                 (>= (1+ i) n))
            (equal (land0 (bits x i 0) y n)
                   (land0 x y n)))
   :hints (("Goal" :in-theory (e/d (land0) (land0-commutative))))))

(defthm land0-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (land0 c (cat x2 m y2 n) l)
                  (cat (land0 (bits c (+ -1 m n) n) x2 m)
                       m
                       (land0 (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use (:instance land0-cat (x2 x2) (y2 y2) (m m) (n n)
                                  (x1 (bits c (+ -1 m n) n))
                                  (y1 (bits c (1- n) 0))
                                  (l (+ m n))))))

; Copy the above events but modify for lxor.

(include-book "lxor0")

(local
 (defthmd lxor0-cat-1
   (implies (and (case-split (integerp n))
                 (case-split (integerp m))
                 (>= n 0)
                 (>= m 0)
                 (equal l (+ m n))
                 (integerp k)
                 (<= 0 k)
                 (< k l))
            (equal (bitn (lxor0 (cat x1 m y1 n) (cat x2 m y2 n) l) k)
                   (bitn (cat (lxor0 x1 x2 m) m (lxor0 y1 y2 n) n) k)))
   :hints (("Goal" :in-theory (enable bitn-cat)))))

(defthmd lxor0-cat
  (implies (and (case-split (natp n))
                (case-split (integerp m))
                (> m 0)
                (equal l (+ m n)))
           (equal (lxor0 (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (lxor0 x1 x2 m) m (lxor0 y1 y2 n) n)))
  :hints (("Goal"
           :in-theory (e/d (sumbits-badguy-is-correct
                            sumbits-badguy-bounds
                            lxor0-cat-1)
                           (bitn-lxor0))
           :restrict ((sumbits-badguy-is-correct ((k (+ m n))))))))

(local
 (defthm lxor0-bits-1-alt
   (implies (and (case-split (integerp n))
                 (case-split (integerp i))
                 (>= (1+ i) n))
            (equal (lxor0 (bits x i 0) y n)
                   (lxor0 x y n)))
   :hints (("Goal" :in-theory (e/d (lxor0) (lxor0-commutative))))))

(defthm lxor0-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (lxor0 c (cat x2 m y2 n) l)
                  (cat (lxor0 (bits c (+ -1 m n) n) x2 m)
                       m
                       (lxor0 (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use (:instance lxor0-cat (x2 x2) (y2 y2) (m m) (n n)
                                  (x1 (bits c (+ -1 m n) n))
                                  (y1 (bits c (1- n) 0))
                                  (l (+ m n))))))

;;;;;;;;;;;

(include-book "logs")

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
                  (land0 (log= x (bits k (+ -1 m n) n))
                        (log= y (bits k (1- n) 0))
                        1)))
  :hints (("Goal" :use (:instance cat-equal-rewrite (x2 x) (y2 y) (n n) (m m)
                                  (x1 (bits k (+ -1 m n) n))
                                  (y1 (bits k (1- n) 0)))
           :in-theory (enable log=))))

