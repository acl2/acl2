;; Proof that hl-nat-combine is onto the naturals
;;
;; Public Domain 2015 David Greve
;;
;; The creative work contained within this file is free and
;; unencumbered and has been released into the public domain by its
;; creator, David Greve.  Anyone is free to copy, modify, publish,
;; use, compile, sell or distribute this work or any derivative of
;; this work for any purpose, commercial or non-commercial, and by any
;; means.  See: http://unlicense.org/
;;
;; Author: David Greve <TheBeaNerd@gmail.com>
;;
;; On 12/26/2014 Matt Kaufmann posted to the ACL2 list a challenge
;; from Bob Boyer regarding Jared Davis' work on the function
;; hl-nat-combine.  Bob is quoted as saying:
;;
;;     I hope someone some day follows up on Jared's work on this and
;;     checks that hl-addr-combine[sic] is also onto the naturals.  Just a
;;     nice little fact that tidies things up in my mind.  I love that
;;     function.
;;
;; Note that the helper function hl-nat-combine is, in fact, onto the
;; naturals whereas the top level hl-addr-combine function may produce
;; negative integer results by design.
;;
;; The proof below demonstrates that hl-nat-combine is onto the
;; naturals

(in-package "ACL2")

(include-book "system/hl-addr-combine" :dir :system)

(local
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (set-default-hints '((nonlinearp-default-hint++
                        id stable-under-simplificationp
                        hist nil)))

  (defun even-product (odd even)
    (or (and (integerp odd) (evenp even))
        (and (integerp even) (evenp odd))))

  (defthm even-product-plus-1
    (implies (and (natp x)
                  (natp y)
                  (or (equal x (+ y 1))
                      (equal y (+ x 1))))
             (even-product x y)))

  (defthm integerp-/-2
    (implies (even-product odd even)
             (integerp (/ (* odd even) 2))))

  (defthm natp-*
    (implies (and (natp x) (natp y))
             (natp (* x y))))

  (defthm natp-/
    (implies (and (integerp (/ (* x y) 2))
                  (natp x)
                  (natp y))
             (natp (/ (* x y) 2))))

  (defthm natp-plus
    (implies (and (natp a) (natp b))
             (natp (+ a b))))

  (in-theory (enable hl-nat-combine))

  (defthm natp-hl-nat-combine
    (implies
     (and (natp a) (natp b))
     (natp (hl-nat-combine a b)))
    :INSTRUCTIONS (:PRO (:DV 1)
                        :EXPAND :UP (:REWRITE NATP-PLUS)
                        (:REWRITE NATP-/)
                        (:REWRITE INTEGERP-/-2)
                        (:REWRITE EVEN-PRODUCT-PLUS-1)
                        :S))

  (defthm hl-nat-combine-zp-b
    (equal (hl-nat-combine n 0) (1+ (hl-nat-combine 0 (1- n)))))

  (defthm hl-nat-combine-delta
    (implies
     (and (integerp x) (integerp y) (integerp a))
     (equal (hl-nat-combine (+ (- a) x) (+ a y))
            (+ (hl-nat-combine x y) a))))

  (defthm hl-nat-combine-delta-instance
    (implies
     (integerp a)
     (equal (hl-nat-combine (+ -1 a) 1)
            (+ (hl-nat-combine a 0) 1)))
    :hints (("Goal" :in-theory (disable hl-nat-combine-delta)
             :use (:instance hl-nat-combine-delta (x a) (y 0) (a 1)))))

  (in-theory (disable hl-nat-combine))

  (defthm natp-a-minus-1
    (implies
     (not (zp a))
     (natp (+ -1 a))))

  (defthm natp-linear-fact
    (implies
     (natp n)
     (not (< n -1))))

  (defthm natp-implies-intergerp
    (implies
     (natp x)
     (integerp x)))

  (defun fnd (a b n)
    (declare (xargs :measure (nfix (- (nfix n)
                                      (hl-nat-combine (nfix a) (nfix b))))))
    (let ((n (nfix n))
          (a (nfix a))
          (b (nfix b)))
      (if (<= n (hl-nat-combine a b)) (cons a b)
        (if (zp a) (fnd (+ b 1) 0 n)
          (fnd (1- a) (1+ b) n)))))

  (defthm open-fnd-0
    (equal (fnd 0 b n)
           (let ((n (nfix n))
                 (a 0)
                 (b (nfix b)))
             (if (<= n (hl-nat-combine a b)) (cons a b)
               (fnd (+ b 1) 0 n))))
    :INSTRUCTIONS ((:DV 1) :X :TOP :S))

  (defthm yeah-1
    (implies
     (and
      (< (+ 1 x) n)
      (integerp n)
      (integerp x))
     (not (< n (+ 2 x))))
    :rule-classes (:rewrite :forward-chaining))

  (defthm yeah-2
    (implies
     (and
      (< x n)
      (integerp n)
      (integerp x))
     (not (< n (+ 1 x))))
    :rule-classes (:rewrite :forward-chaining))

  (defthmd fnd-works
    (implies
     (<= (hl-nat-combine (nfix a) (nfix b)) (nfix n))
     (equal (hl-nat-combine (car (fnd a b n))
                            (cdr (fnd a b n)))
            (nfix n))))

  (defthm fnd-finds-natps
    (and
     (natp (car (fnd a b n)))
     (natp (cdr (fnd a b n))))
    :hints (("Goal" :in-theory (disable nfix))))

  ))

(defthm natp-hl-nat-combine
  (implies
   (and (natp a) (natp b))
   (natp (hl-nat-combine a b))))

(defun fnd (a b n)
  (declare (xargs :measure (nfix (- (nfix n)
                                    (hl-nat-combine (nfix a) (nfix b))))))
  (let ((n (nfix n))
        (a (nfix a))
        (b (nfix b)))
    (if (<= n (hl-nat-combine a b)) (cons a b)
      (if (zp a) (fnd (+ b 1) 0 n)
        (fnd (1- a) (1+ b) n)))))

(defthm onto-property
  (implies
   (natp n)
   (let ((a (car (fnd 0 0 n)))
         (b (cdr (fnd 0 0 n))))
     (and (equal n (hl-nat-combine a b))
          (natp a)
          (natp b))))
  :rule-classes nil
  :hints (("Goal" :use (:instance fnd-works
                                  (a 0) (b 0) (n n)))))
