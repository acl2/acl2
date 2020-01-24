; MYIF, an alias for IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; MYIF is just an alias for IF, but MYIF can be disabled to prevent
;; case-splitting.

;; STATUS: In-progress

;; TODO: Now that we can rewrite an IF (which was not possible when we
;; introduced MYIF), perhaps MYIF could be used less or eliminated.

;; TODO: Consider giving this a better name.

(defund myif (test thenpart elsepart)
  (declare (xargs :guard t))
  (if test thenpart elsepart))

;add myif when non nil?
(defthm myif-of-t
  (equal (myif t thenpart elsepart)
         thenpart)
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-nil
  (equal (myif nil thenpart elsepart)
         elsepart)
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-same-branches
  (equal (myif test x x)
         x)
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-not
  (equal (myif (not test) x y)
         (myif test y x))
  :hints (("Goal" :in-theory (enable myif))))

;okay since nth is an extractor?
(defthm nth-of-myif
  (equal (nth n (myif test l1 l2))
         (myif test (nth n l1)
               (nth n l2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm mv-nth-of-myif
  (equal (mv-nth n (myif test l1 l2))
         (myif test
               (mv-nth n l1)
               (mv-nth n l2)))
  :hints (("Goal" :in-theory (enable myif))))

;should be okay since n is the term that gets duplicated
(defthm nth-of-myif-limited
  (implies (syntaxp (quotep n))
           (equal (nth n (myif test l1 l2))
                  (myif test (nth n l1)
                        (nth n l2))))
  :hints (("Goal" :in-theory (enable myif))))


;requires that the indices be the same
;BOZO handle the other cases?
(defthm myif-of-update-nth
  (equal (myif test (update-nth n val1 lst1) (update-nth n val2 lst2))
         (update-nth n (myif test val1 val2) (myif test lst1 lst2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm integerp-of-myif
  (implies (and (integerp a)
                (integerp b))
           (equal (integerp (myif test a b))
                  t))
  :hints (("Goal" :in-theory (enable myif))))

(defthm integerp-of-myif-strong
  (equal (integerp (myif test a b))
         (myif test (integerp a) (integerp b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-same-test
  (equal (myif test a (myif test b c))
         (myif test a c))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-same-test2
  (equal (myif test (myif test x y) z)
         (myif test x z))
  :hints (("Goal" :in-theory (enable myif))))

;expensive?
(defthmd myif-of-myif-implication-of-tests
  (implies (implies test1 test2)
           (equal (myif test1 (myif test2 a b) c)
                  (myif test1 a c)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-nil-t
  (equal (myif test nil t)
         (not test))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-t-nil
  (implies (booleanp test)
           (equal (myif test t nil)
                  test))
  :hints (("Goal" :in-theory (enable myif))))

;used for inside-out rewriting
(defthm myif-when-not-nil
  (implies (not (equal nil x)) ;can be slow for normal rewriting (inside-out, without memo?)?
           (equal (myif x y z)
                  y))
  :hints (("Goal" :in-theory (enable myif))))

;used for inside-out rewriting
(defthm myif-when-nil
  (implies (equal nil x) ;can be slow?
           (equal (myif x y z)
                  z))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-constant-when-not-nil
  (implies (and (syntaxp (quotep x))
                (not (equal x nil)))
           (equal (myif x y z)
                  y))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd equal-of-myif-arg2
  (equal (equal x (myif test a b))
         (myif test
               (equal x a)
               (equal x b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd equal-of-myif-arg1
  (equal (equal (myif test a b) x)
         (myif test
               (equal a x)
               (equal b x)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm equal-of-myifs-same-test
  (equal (equal (myif test a b) (myif test c d))
         (myif test (equal a c) (equal b d)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-myif-myif-1
  (equal (myif test x (myif test2 y (myif test z w)))
         (myif test x (myif test2 y w)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-myif-myif-2
  (equal (myif test (myif a b (myif test c d)) e)
         (myif test (myif a b c) e))
  :hints (("Goal" :in-theory (enable myif))))

;could be done better with congruences
;or go to boolif?
(defthm myif-of-myif-x-x-t
  (equal (myif (myif x x t) y z)
         y)
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-not-myif-same
  (equal (myif test x (not (myif test y z)))
         (myif test x (not z)))
  :hints (("Goal" :in-theory (enable myif))))
