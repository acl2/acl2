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

(in-package "ACL2")

(include-book "../lib1/rtl")


(local (include-book "../lib1/bits"))

(local
 (defthmd cat-expand-bits
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (natp n)
                (acl2-numberp k))
           (equal (equal (cat x 1 y n) k)
                  (equal (bits y (+ -1 n) 0)
                         (if (equal (bitn x 0) 1)
                             (+ k (* -1 (expt 2 n)))
                           k))))
  :hints (("Goal" :in-theory (enable binary-cat)))))


(defthm cat-fact
  (implies (equal (cat x 1 3 2) 3)
           (not (equal (cat x 1 y 1 1 1) 5)))
  :hints (("Goal" :in-theory (enable cat-expand-bits))))


(defthm cat-fact-2
  (implies (equal (cat x 1 y 1 1 1) 5)
           (not (equal (cat x 1 y 1 z 1) 7)))
  :hints (("Goal" :in-theory (enable cat-expand-bits))))

(defthm cat-fact-3
  (implies (equal (cat x 1 3 2) 3)
           (not (equal (cat x 1 y 1 z 1) 7)))
  :hints (("Goal" :in-theory (enable cat-expand-bits))))

(defthm cat-fact-4
  (implies (equal (cat x 1 y 1 1 1) 5)
           (not (equal (cat x 1 y 1 z 1) 6)))
  :hints (("Goal" :in-theory (enable cat-expand-bits))))

(defthm cat-fact-5
  (implies (equal (cat x 1 3 2) 3)
           (not (equal (cat x 1 y 1 z 1) 6)))
  :hints (("Goal" :in-theory (enable cat-expand-bits))))


(defthm cat-fact-6
  (implies (equal (cat 1 1 x 1 y 1) 4)
           (not (equal (cat z 1 x 1 y 1) 5)))
  :hints (("Goal" :in-theory (enable cat-expand-bits))))




(local
 (defthmd bitn-0-or-1
   (implies (not (equal (bitn x 0) 0))
            (equal (bitn x 0) 1))
   :hints (("Goal" :use ((:instance bitn-0-1))))))

(local
 (defthm bitn-0-less-than-1
   (<= (bitn x 0) 1)
   :hints (("Goal" :use ((:instance bitn-0-1))))
   :rule-classes (:linear)))

(local
 (defthm bitn-0-less-than-2
   (>= (bitn x 0) 0)
   :hints (("Goal" :use ((:instance bitn-0-1))))
   :rule-classes (:linear :type-prescription)))

(local
 (defthmd bits-than-2
   (implies (and (integerp n)
                 (>= n 0))
            (< (bits x n 0)
               (expt 2 (+ 1 n))))
   :rule-classes (:linear)
   :hints (("Goal" :in-theory (e/d () (bits-bvecp
                                       BITS-BVECP-SIMPLE))
            :use ((:instance bits-bvecp
                             (i n) (j 0) (k (+ 1 n))))
            :expand (bvecp (bits x n 0) (+ 1 n))))))

(local (in-theory (enable bits-than-2)))

(local
 (defthm cat-expansion-specific
   (implies (and (integerp n)
                 (> n 0))
            (equal (cat x 1 y n)
                   (if (equal (bitn x 0) 0)
                       (bits y (+ -1 n) 0)
                     (+ (expt 2 n) (bits y (+ -1 n) 0)))))
   :hints (("Goal" :in-theory (enable binary-cat)))))



(local
 (encapsulate ()
    (local (include-book "../../arithmetic/top"))
    (defthm bits-plus-reduce
      (implies (and (integerp n)
                    (> c 0)
                    (integerp c)
                    (integerp y)
                    (<= c (expt 2 n))
                    (<= 0 y)
                    (< y (expt 2 n))
                    (> n 0))
               (equal (bits (+ c y) n 0)
                      (+ c y)))
      :hints (("Goal" :use ((:instance BITS-BITS-SUM
                                       (x c)
                                       (i n)
                                       (y (bits y n 0)))
                            (:instance sumbits-bits
                                       (x (+ c y))
                                       (n (+ 1 n)))
                            (:instance sumbits-thm
                                       (x (+ c y))
                                       (n (+ 1 n)))
                            (:instance sumbits-thm
                                       (x y)
                                       (n (+ 1 n)))
                            (:instance sumbits-bits
                                       (x y)
                                       (n (+ 1 n))))
               :in-theory (e/d (bvecp
                                expt-2-reduce-leading-constant)
                               (sumbits)))))))





(DEFTHM CAT-FACT-7
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1) 1)
           (NOT (EQUAL (CAT X 1 Y1 1 Z1 1) 7))))

(DEFTHM CAT-FACT-8
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1) 3)
           (NOT (EQUAL (CAT X 1 Y1 1 Z1 1) 5))))

(DEFTHM CAT-FACT-9
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1) 1)
           (NOT (EQUAL (CAT X 1 Y 1 Z1 1) 3))))


(DEFTHM CAT-FACT-10
  (IMPLIES (EQUAL (CAT 1 1 X 1 Y 1) 4)
           (NOT (EQUAL (CAT Z 1 X 1 Y 1) 1))))


;; [Jared] added this to fix the proof after building these into ACL2
(local (in-theory (disable acl2::commutativity-2-of-+
                           acl2::fold-consts-in-+)))

(DEFTHM CAT-FACT-11
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                  125)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))

(DEFTHM CAT-FACT-12
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                  123)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                       125))))

(DEFTHM CAT-FACT-13
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3) 119)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                       123))))



(DEFTHM CAT-FACT-14
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3)
                       119))))


(DEFTHM CAT-FACT-15
  (IMPLIES (EQUAL (CAT X 1 Y 1 31 5) 95)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111))))

(DEFTHM CAT-FACT-16
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 31 5) 95))))


(DEFTHM CAT-FACT-17
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111))))

(DEFTHM CAT-FACT-18
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3)
                       119))))


(DEFTHM CAT-FACT-19
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                       123))))


(DEFTHM CAT-FACT-20
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                       125))))


(DEFTHM CAT-FACT-21
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))

(DEFTHM CAT-FACT-22
  (IMPLIES (EQUAL (CAT X 1 Y 1 31 5) 95)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3)
                       119))))


(DEFTHM CAT-FACT-23
  (IMPLIES (EQUAL (CAT X 1 Y 1 31 5) 95)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                       123))))


(DEFTHM CAT-FACT-24
  (IMPLIES (EQUAL (CAT X 1 Y 1 31 5) 95)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                       125))))


(DEFTHM CAT-FACT-25
  (IMPLIES (EQUAL (CAT X 1 Y 1 31 5) 95)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))


(DEFTHM CAT-FACT-26
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))


(DEFTHM CAT-FACT-27
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                       125))))


(DEFTHM CAT-FACT-28
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                       123))))

(DEFTHM CAT-FACT-29
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3)
                       119))))


(DEFTHM CAT-FACT-30
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3) 119)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                       125))))


(DEFTHM CAT-FACT-31
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3) 119)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))


(DEFTHM CAT-FACT-32
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                  123)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))


(DEFTHM CAT-FACT-33
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                  125)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       127))))


(DEFTHM CAT-FACT-34
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 1 1)
                  125)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       126))))


(DEFTHM CAT-FACT-35
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 3 2)
                  123)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       126))))


(DEFTHM CAT-FACT-36
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 U 1 7 3) 119)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       126))))


(DEFTHM CAT-FACT-37
  (IMPLIES (EQUAL (CAT X 1 Y 1 Z 1 15 4) 111)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       126))))


(DEFTHM CAT-FACT-38
  (IMPLIES (EQUAL (CAT X 1 Y 1 31 5) 95)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       126))))


(DEFTHM CAT-FACT-39
  (IMPLIES (EQUAL (CAT X 1 63 6) 63)
           (NOT (EQUAL (CAT X 1 Y 1 Z 1 U 1 V 1 W 1 P 1)
                       126))))




