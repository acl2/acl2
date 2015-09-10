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

; Port land0 theorems to land.  The original definition of land (in rel4) was
; that of land0 in the current release.  So the port is to keep all the lemmas
; about land0 and then use equality of land0 with land to port them to land.

(in-package "RTL")

(include-book "land0")
(local (include-book "top1")) ; for land0-bits-1 and land0-bits-2

(defun binary-land (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)
                  :verify-guards nil))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (and (equal (bitn x 0) 1)
                       (equal (bitn y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-land (mod x 2) (mod y 2) 1))))
       :exec ; (land0 x y n)
       (logand (bits x (1- n) 0)
               (bits y (1- n) 0))))

(defmacro land (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(land x y n) -- the base case
         `(binary-land ,@x))
        (t
         `(binary-land ,(car x)
                       (land ,@(cdr x))
                       ,(car (last x))))))

; We attempt to derive all land results from corresponding land0 results.

(encapsulate
 ()

 (local
  (defun p0 (x y n)
    (equal (land x y n)
           (land0 x y n))))

 (local
  (defthm p0-holds-inductive-step
    (implies (and (not (zp n))
                  (not (equal n 1))
                  (p0 (fl (* x 1/2))
                      (fl (* y 1/2))
                      (+ -1 n))
                  (p0 (mod x 2) (mod y 2) 1))
             (p0 x y n))
    :hints (("Goal" :use (land0-def binary-land)))))

 (local
  (defthm p0-holds-base-1
    (p0 x y 1)
    :hints (("Goal" :in-theory (enable bitn)
             :expand ((binary-land0 x y 1))))))

 (local
  (defthm p0-holds-base-0
    (implies (zp n)
             (p0 x y n))
    :hints (("Goal" :expand ((binary-land0 x y n))))))

 (local
  (defthm p0-holds
    (p0 x y n)
    :hints (("Goal" :induct (land x y n)
             :in-theory (disable p0)))
    :rule-classes nil))

 (defthmd land-is-land0
   (equal (land x y n)
          (land0 x y n))
   :hints (("Goal" :use p0-holds))))

(local (in-theory (e/d (land-is-land0) (binary-land))))

;Allows things like (in-theory (disable land)) to refer to binary-land.
(add-macro-alias land binary-land)

(defthm land-nonnegative-integer-type
  (and (integerp (land x y n))
       (<= 0 (land x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription land) is no better than land-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-land)))

;drop this if we plan to keep natp enabled?
(defthm land-natp
  (natp (land x y n)))

;BOZO split into 2 rules?
(defthm land-with-n-not-a-natp
  (implies (not (natp n))
           (equal (land x y n)
                  0)))

(defthmd land-bvecp-simple
  (bvecp (land x y n) n)
  :hints (("Goal" :use land0-bvecp-simple)))

(defthm land-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (land x y n) k)))


;;
;; Rules to normalize land terms (recall that LAND is a macro for BINARY-LAND):
;;

;This guarantees that the n parameters to nested LAND calls match.
;Note the MIN in the conclusion.
;BOZO do we expect MIN to be enabled?  Maybe we should use IF instead for this and other rules?
(defthm land-nest-tighten
  (implies (and (syntaxp (not (equal m n)))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (land x (land y z m) n)
                  (land x (land y z (min m n)) (min m n)))))

; allow the n's to differ on this?
(defthm land-associative
  (equal (land (land x y n) z n)
         (land x (land y z n) n)))

(defthm land-commutative
  (equal (land y x n)
         (land x y n)))

; allow the n's to differ on this?
(defthm land-commutative-2
  (equal (land y (land x z n) n)
         (land x (land y z n) n)))

; allow the n's to differ on this?
(defthm land-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (land x (land y z n) n)
                  (land (land x y n) z n))))

(defthm land-0
  (equal (land 0 y n)
         0))

;nicer than the analogous rule for logand? is it really?
;BOZO gen the second 1 in the lhs?
(defthm land-1
  (equal (land 1 y 1)
         (bitn y 0)))

(defthm land-self
  (equal (land x x n)
         (bits x (1- n) 0)))

;perhaps use only the main rule, bits-land?
(defthmd bits-land-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j)))))
  :hints (("Goal" :use bits-land0-1)))

;perhaps use only the main rule, bits-land?
(defthmd bits-land-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ n (- j)))))
  :hints (("Goal" :use bits-land0-2)))

;Notice the call to MIN in the conclusion.
(defthm bits-land
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-land-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  (land (bitn x m)
                        (bitn y m)
                        1))))
(defthmd bitn-land-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  0)))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-land
  (implies (and (case-split (<= 0 k))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) k)
                  (if (< k n)
                      (land (bitn x k)
                            (bitn y k)
                            1)
                    0))))

;BOZO see land-equal-0
;drop bvecp hyps and put bitn in conclusion?
(defthm land-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (land x y 1))
                  (or (equal x 0)
                      (equal y 0)))))

(defthm land-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (land x y 1))
                  (and (equal x 1)
                       (equal y 1)))))

(defthm land-ones
  (equal (land (1- (expt 2 n)) x n)
         (bits x (1- n) 0))
  :hints (("Goal" :use land0-ones))
  :rule-classes ())

;land-with-all-ones will rewrite (land x n) [note there's only one value being ANDed], because (land x n)
;expands to (BINARY-LAND X (ALL-ONES N) N) - now moot???
;BOZO drop bvecp hyp and move to conclusion?
(defthm land-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (land (all-ones n) x n)
                  x)))

(defthmd land-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (equal k (1- (expt 2 n))) ;this computes on constants...
                )
           (equal (land k x n)
                  (bits x (1- n) 0)))
  :hints (("Goal" :use land0-ones-rewrite)))

(defthm land-def-original
  (implies (and (integerp x)
                (integerp y)
                (> n 0)
                (integerp n)
                )
           (equal (land x y n)
                  (+ (* 2 (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land (mod x 2) (mod y 2) 1))))
  :hints (("Goal" :use land0-def))
  :rule-classes ())

(defthmd land-mod-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (mod (land x y n) 2)
                  (land (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use land0-mod-2)))

;BOZO RHS isn't simplified...
(defthmd land-fl-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (fl (/ (land x y n) 2))
                  (land (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use land0-fl-2)))

;BOZO rename to land-with-n-0
;what if n is negative? or not an integer?
(defthm land-x-y-0
  (equal (land x y 0) 0))

;actually, maybe only either x or y must be a bvecp of length n
;n is a free var
(defthm land-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land x y m)
                    (land x y n))))

;deceptive name; this only works for single bits!
(defthm land-equal-0
  (implies (and (bvecp i 1)
                (bvecp j 1))
           (equal (equal 0 (land i j 1))
                  (or (equal i 0)
                      (equal j 0)))))

;make alt version?
(defthm land-bnd
  (implies (case-split (<= 0 x))
           (<= (land x y n) x))
  :rule-classes (:rewrite :linear))

;enable? make an alt version??
(defthmd land-ignores-bits
  (equal (land (bits x (1- n) 0) y n)
         (land x y n))
  :hints (("Goal" :use land0-ignores-bits)))

(defthmd land-with-shifted-arg
  (implies (and (integerp x) ;gen?
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land x (bits y (1- n) m) (+ n (- m))))))
  :hints (("Goal" :use land0-with-shifted-arg)))

(defthm land-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (land (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (land x y (- n k)))))
  :hints (("Goal" :use land0-shift))
  :rule-classes nil)

(defthmd land-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (equal (land x (expt 2 k) n)
                  (* (expt 2 k) (bitn x k))))
  :hints (("Goal" :use land0-expt)))

(defthm land-slice
  (implies (and (<= j i) ;drop? or not?
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j)
                )
           (equal (land x (- (expt 2 i) (expt 2 j)) n)
                  (* (expt 2 j) (bits x (1- i) j))))
  :hints (("Goal" :use land0-slice))
  :rule-classes ())

(defthmd land-slices
  (implies (and (natp n)
                (natp l)
                (natp k)
                (<= l k)
                (< k n))
           (equal (land (- (expt 2 n) (1+ (expt 2 l)))
                        (- (expt 2 n) (expt 2 k))
                        n)
                  (if (= l k)
                      (- (expt 2 n) (expt 2 (1+ k)))
                    (- (expt 2 n) (expt 2 k)))))
  :hints (("Goal" :use land0-slices)))

(defthm land-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (land x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear))

(defthm land-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (land x y n) (1- (expt 2 n)))))

(defthm land-fl-1
  (equal (land (fl x) y n)
         (land x y n)))

(defthm land-fl-2-eric ;BOZO name conflicted...
  (equal (land x (fl y) n)
         (land x y n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Added in move to rel5 (should perhaps be in a -proofs file):
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm land-bvecp-2
  (implies (and (bvecp x m)
                (bvecp y m))
           (bvecp (land x y n) m))
  :hints (("Goal" :in-theory (enable bvecp))))

; Start proof of fl-land.

(local
 (defun fl-land-induction (k n)
   (if (zp k)
       n
     (fl-land-induction (1- k) (1+ n)))))


(local
 (defthmd fl-land-induction-step-1
   (implies (not (zp k))
            (equal (land (fl (* x (/ (expt 2 k))))
                         (fl (* y (/ (expt 2 k))))
                         n)
                   (land (fl (/ (fl (* x (/ (expt 2 (1- k))))) 2))
                         (fl (/ (fl (* y (/ (expt 2 (1- k))))) 2))
                         n)))
   :hints (("Goal" :in-theory (disable land-fl-1
                                       land-fl-2-eric
                                       land-is-land0
                                       fl/int-rewrite)
            :expand ((expt 2 k))
            :use ((:instance fl/int-rewrite
                             (x (* x (/ (expt 2 (1- k)))))
                             (n 2))
                  (:instance fl/int-rewrite
                             (x (* y (/ (expt 2 (1- k)))))
                             (n 2)))))))

(local
 (defthmd fl-land-induction-step-2
   (equal (land (fl (/ (fl (* x (/ (expt 2 (1- k))))) 2))
                (fl (/ (fl (* y (/ (expt 2 (1- k))))) 2))
                n)
          (fl (/ (land (fl (* x (/ (expt 2 (1- k)))))
                       (fl (* y (/ (expt 2 (1- k)))))
                       (1+ n))
                 2)))
   :hints (("Goal" :in-theory (disable land-fl-1
                                       land-fl-2-eric
                                       land-is-land0
                                       fl/int-rewrite)
            :expand ((land (fl (* x (/ (expt 2 (1- k)))))
                           (fl (* y (/ (expt 2 (1- k)))))
                           (1+ n)))))))

(local
 (defthmd fl-land-induction-step-3
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (land x y (+ k n))))
                        (land (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (/ (land (fl (* x (/ (expt 2 (1- k)))))
                                (fl (* y (/ (expt 2 (1- k)))))
                                (1+ n))
                          2))
                   (fl (/ (fl (* (/ (expt 2 (+ -1 k)))
                                 (land x y (+ k n))))
                          2))))))

(local
 (defthmd fl-land-induction-step-4
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (land x y (+ k n))))
                        (land (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (/ (fl (* (/ (expt 2 (+ -1 k)))
                                 (land x y (+ k n))))
                          2))
                   (fl (* (/ (expt 2 k))
                          (land x y (+ k n))))))
   :hints (("Goal" :expand ((expt 2 k))))))

(local
 (defthm fl-land-induction-step
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (land x y (+ k n))))
                        (land (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (* (/ (expt 2 k))
                          (land x y (+ k n))))
                   (land (fl (* x (/ (expt 2 k))))
                         (fl (* y (/ (expt 2 k))))
                         n)))
   :hints (("Goal" :use (fl-land-induction-step-1
                         fl-land-induction-step-2
                         fl-land-induction-step-3
                         fl-land-induction-step-4)))))

(defthmd fl-land
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (land x y (+ n k)) (expt 2 k)))
                  (land (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :induct (fl-land-induction k n)
           :in-theory (disable land-is-land0 land-fl-1 land-fl-2-eric))))


(defthmd land-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (land x y n)
                  (+ (* 2 (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land (bitn x 0) (bitn y 0) 1))))
  :hints (("Goal" :in-theory (enable bitn-rec-0)
           :use land-def-original)))

; Proof of mod-land as derived from bits-land:

; (land x y k)))
; = {by land-bvecp and bits-tail}
; (bits (land x y k) (1- k) 0)
; = {by (:instance bits-land (x x) (y y) (n k) (i (1- k)) (j 0))}
; (land (bits x (1- k) 0) (bits y (1- k) 0) k)
; = {by (:instance bits-land (x x) (y y) (n n) (i (1- k)) (j 0))}
; (bits (land x y n) (1- k) 0)
; = {by hypothesis}
; (bits (land x y n) (min (1- n) (1- k)) 0)
; = {by (:instance mod-bits (x (land x y n)) (i (1- n)) (j k))}
; (mod (bits (land x y n) (1- n) 0) (expt 2 k))
; = {by land-bvecp}
; (mod (land x y n) (expt 2 k))

(defthmd mod-land
  (implies (and (integerp n)
                (integerp k)
                (<= k n))
           (equal (mod (land x y n) (expt 2 k))
                  (land x y k)))
  :hints (("Goal"
           :use
           ((:instance bits-land (x x) (y y) (n k) (i (1- k)) (j 0))
            (:instance mod-bits (x (land x y n)) (i (1- n)) (j k))))))

(defthmd land-bits-1
  (equal (land (bits x (1- n) 0)
               y
               n)
         (land x y n))
  :hints (("Goal" :use land0-bits-1)))

(defthmd land-bits-2
  (equal (land x
               (bits y (1- n) 0)
               n)
         (land x y n))
  :hints (("Goal" :use land0-bits-2)))

(defthm land-base
  (equal (land x y 1)
         (if (and (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use land0-base))
  :rule-classes nil)
