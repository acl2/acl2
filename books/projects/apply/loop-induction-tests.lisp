; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains a series of theorems about loop$ that are easy to prove by the
; correct induction argument.  The file is designed to test the :induction rules in
; loop-lemmas.lisp.

(in-package "ACL2")
(include-book "top")

(defthm loop$-induction-challenge-1
  (implies (natp i0)
           (nat-listp (loop$ for i from i0 to max collect i)))
  :rule-classes nil)

(defthm loop$-induction-challenge-2
  (implies (and (natp i0)
                (natp bump))
           (nat-listp (loop$ for i from i0 to max collect (+ i bump))))
  :rule-classes nil)

(defthm loop$-induction-challenge-3
  (implies (and (natp i0)
                (natp j0))
           (nat-listp (loop$ for i from i0 to max
                             as  j from j0 to max
                             collect (+ i j))))
  :rule-classes nil)

(defthm loop$-induction-challenge-4a
  (implies (and (nat-listp lst1)
                (nat-listp lst2))
           (nat-listp (loop$ for i in lst1
                             as  j in lst2
                             collect (+ i j))))
  :rule-classes nil)

(defthm loop$-induction-challenge-4b
  (implies (and (nat-listp lst1)
                (nat-listp lst2))
           (nat-listp (loop$ for i in lst1
                             as  l on lst2
                             collect (+ i (car l)))))
  :rule-classes nil)

(defthm loop$-induction-challenge-4c
  (implies (nat-listp lst)
           (loop$ for i in lst
                  as  j in lst
                  always (equal i j)))
  :rule-classes nil)

(defthm loop$-induction-challenge-4d
  (implies (and (symbol-listp lst1)
                (nat-listp lst2))
           (symbol-alistp
            (loop$ for e in lst1
                   as  i in lst2
                   collect (cons e i))))
  :rule-classes nil)

(defthm loop$-induction-challenge-5a
  (implies (and (nat-listp lst1)
                (natp j0))
           (nat-listp (loop$ for i in lst1
                             as  j from j0 to (+ j0 (len lst1) -1)
                             collect (+ i j))))
  :rule-classes nil)

(defthm loop$-induction-challenge-5b
  (implies (and (nat-listp lst1)
                (natp j0))
           (nat-listp (loop$ for j from j0 to (+ j0 (len lst1) -1)
                             as  i in lst1
                             collect (+ i j))))
  :rule-classes nil)

(defthm loop$-induction-challenge-5c
  (implies (and (nat-listp lst1)
                (natp j0))
           (nat-listp (loop$ for j from j0 to (+ j0 (len lst1) -1)
                             as  l on lst1
                             collect (+ (car l) j))))
  :rule-classes nil)

(defthm loop$-induction-challenge-5d
  (implies (and (natp i0)
                (natp j0))
           (nat-listp (loop$ for i from i0 to maxi
                             as  j from j0 to maxj
                             collect (+ i j))))
  :rule-classes nil)

(defthm loop$-induction-challenge-6a
  (implies (natp i0)
           (equal (loop$ for e in lst as i from i0 to (+ i0 (len lst) -1) always (equal i e))
	          (loop$ for i from i0 to (+ i0 (len lst) -1) as e in lst always (equal i e))))
  :rule-classes nil)

(defthm loop$-induction-challenge-6b
  (implies (natp i0)
           (equal (loop$ for e in lst as i from i0 to max always (equal i e))
	          (loop$ for i from i0 to max as e in lst always (equal i e))))
  :rule-classes nil)

; The following theorem is not proved automatically:

; (defthm loop$-induction-challenge-7a
;   (implies (and (integerp lo1) (integerp hi1)
;                 (integerp lo2) (integerp hi2))
;            (loop$ for i from lo1 to hi1 by 1
;                   as  j from lo2 to hi2 by 1
;                   always (equal (- i j) (- lo1 lo2))))
;   :rule-classes nil)

; But we can prove it this way:

(encapsulate
  nil
  (local
   (defthm lemma
     (implies (and (integerp lo1)
                   (integerp lo2))
              (equal (always$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
                                        (EQUAL (+ (CAR LOOP$-IVARS)
                                                  (- (CADR LOOP$-IVARS)))
                                               (+ (CAR LOOP$-GVARS)
                                                  (- (CADR LOOP$-GVARS)))))
                               (list lo1 lo2)
                               targets)
                     (always$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
                                        (EQUAL (+ (CAR LOOP$-IVARS)
                                                  (- (CADR LOOP$-IVARS)))
                                               (CAR LOOP$-GVARS)))
                               (list (- lo1 lo2))
                               targets)))))
  (defthm loop$-induction-challenge-7a
    (implies (and (integerp lo1) (integerp hi1)
                  (integerp lo2) (integerp hi2))
             (loop$ for i from lo1 to hi1 by 1
                    as  j from lo2 to hi2 by 1
                    always (equal (- i j) (- lo1 lo2))))
    :rule-classes nil))

; We can prove essentially the same theorem, without needing the lemma, by just
; stating it differently, i.e., moving the arithmetic on lo1 and lo2 outside
; the lambda.

(defthm loop$-induction-challenge-7b
  (implies (and (integerp lo1) (integerp hi1)
                (integerp lo2) (integerp hi2))
           (let ((diff (- lo1 lo2)))
             (loop$ for i from lo1 to hi1 by 1
                    as  j from lo2 to hi2 by 1
                    always (equal (- i j) diff))))
  :rule-classes nil)

(defthm loop$-induction-challenge-8
  (equal (loop$ for a in lst1 as b in lst2
                thereis (if (equal x a) b nil))
         (loop$ for  b in lst2 as a in lst1
                thereis (if (equal x a) b nil)))
  :rule-classes nil)

(defthm loop$-induction-challenge-9
  (equal (loop$ for a in lst1
                as  b in lst2
                when (and (equal a 1)
                          (equal b -1))
                sum (+ a b))
         0)
  :rule-classes nil)
