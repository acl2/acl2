; MYIF, an alias for IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;; TODO: Now that we can rewrite an IF (which was not possible when we
;; introduced MYIF), perhaps MYIF could be used less or eliminated.

(include-book "myif-def")

;; This is now a legal rewrite rule.
(defthmd if-becomes-myif
  (equal (if x y z)
         (myif x y z))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-constant-when-not-nil
  (implies (and (syntaxp (quotep x))
                (not (equal x nil)) ; todo: simplify?
                )
           (equal (myif x y z)
                  y))
  :hints (("Goal" :in-theory (enable myif))))

;; disabled since we have myif-of-constant-when-not-nil
(defthmd myif-of-t
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
           (integerp (myif test a b)))
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

;rename
(defthm myif-nil-t
  (equal (myif test nil t)
         (not test))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-t-and-nil-when-booleanp
  (implies (booleanp test)
           (equal (myif test t nil)
                  test))
  :hints (("Goal" :in-theory (enable myif))))

;; todo: where should this go?
;; (defthm myif-of-t-and-nil
;;   (equal (myif test t nil)
;;          (bool-fix test))
;;   :hints (("Goal" :in-theory (enable myif))))

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

(defthm equal-of-myif-arg1-safe
  (implies (syntaxp (quotep x))
           (equal (equal (myif test a b) x)
                  (myif test
                        (equal a x)
                        (equal b x))))
  :hints (("Goal" :in-theory (enable myif))))

(defthm equal-of-myif-arg2-safe
  (implies (syntaxp (quotep x))
           (equal (equal x (myif test a b))
                  (myif test
                        (equal x a)
                        (equal x b))))
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

;;;
;;; myif "lifting" rules
;;;

;; In general, lifting MYIFs using rules of the form "foo of myif" can cause
;; the term size to explode, because other arguments of foo appear once in the
;; LHS but more than once in the RHS.  However, for unary functions, or when
;; those other arguments are small (e.g., constants), lifting is probably a
;; good idea.

(defthm len-of-myif
  (equal (len (myif test thenpart elsepart))
         (myif test (len thenpart) (len elsepart)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm cdr-of-myif
  (equal (cdr (myif test thenpart elsepart))
         (myif test (cdr thenpart) (cdr elsepart)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm car-of-myif
  (equal (car (myif test thenpart elsepart))
         (myif test (car thenpart) (car elsepart)))
  :hints (("Goal" :in-theory (enable myif))))

;is this inefficient?
(defthm true-listp-of-myif-strong
  (equal (true-listp (myif test a b))
         (myif test
               (true-listp a)
               (true-listp b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd true-listp-of-myif
  (implies (and (true-listp a)
                (true-listp b))
           (true-listp (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm consp-of-myif-strong
  (equal (consp (myif test a b))
         (myif test (consp a) (consp b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm unsigned-byte-p-of-myif
  (implies (and (unsigned-byte-p n a)
                (unsigned-byte-p n b))
           (unsigned-byte-p n (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm unsigned-byte-p-of-myif-strong
  (equal (unsigned-byte-p n (myif test a b))
         (myif test
               (unsigned-byte-p n a)
               (unsigned-byte-p n b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm signed-byte-p-of-myif
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p n (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm signed-byte-p-of-myif-strong
  (equal (signed-byte-p n (myif test a b))
         (myif test
               (signed-byte-p n a)
               (signed-byte-p n b)))
  :hints (("Goal" :in-theory (enable myif))))

;strengthen?
(defthm acl2-numberp-of-myif
  (implies (and (acl2-numberp a) (acl2-numberp b))
           (acl2-numberp (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd myif-of-nil-special
  (implies (implies ep (not test))
           (equal (myif test nil ep)
                  ep))
  :hints (("Goal" :in-theory (enable myif))))

;rename
(defthm myif-of-myif-test
  (equal (myif (myif test t nil) a b)
         (myif test a b))
  :hints (("Goal" :in-theory (enable myif))))

;i suppose we could use any predicate here in place of booleanp
;shouldn't we turn myif into boolif in this case?
(defthm booleanp-of-myif
  (implies (and (booleanp y)
                (booleanp z))
           (booleanp (myif x y z)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-x-x-t-not-nil
  (implies (not (equal nil val))
           (equal (equal nil (myif x x val))
                  nil))
  :hints (("Goal" :in-theory (enable myif))))

;move
(defthmd not-of-myif
  (equal (not (myif test tp ep))
         (myif test (not tp) (not ep)))
  :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd <-of-myif-arg1
  (equal (< (myif test a b) k)
         (myif test (< a k) (< b k)))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd <-of-myif-arg2
  (equal (< k (myif test a b))
         (myif test (< k a) (< k b)))
  :hints (("Goal" :in-theory (enable myif))))

;; could a and/or b to be constant as well
(defthmd <-of-myif-arg1-when-constant
  (implies (syntaxp (quotep k))
           (equal (< (myif test a b) k)
                  (myif test (< a k) (< b k))))
  :hints (("Goal" :in-theory (enable myif))))

;; could a and/or b to be constant as well
(defthmd <-of-myif-arg2-when-constant
  (implies (syntaxp (quotep k))
           (equal (< k (myif test a b))
                  (myif test (< k a) (< k b))))
  :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
(defthm natp-of-myif2
  (implies (and (natp a)
                (natp b))
           (natp (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))
