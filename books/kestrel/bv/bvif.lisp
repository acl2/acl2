; An if-then-else function over bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "kestrel/booleans/booleans" :dir :system) ;todo: reduce
(include-book "trim")
(local (include-book "unsigned-byte-p"))

;note that the test is a boolean, not a bit vector
(defund bvif (size test thenpart elsepart)
  (declare (xargs :guard (and (natp size)
                              (integerp thenpart)
                              (integerp elsepart))))
  (if test
      (bvchop size thenpart)
    (bvchop size elsepart)))

(defthm integerp-of-bvif
  (integerp (bvif size test thenpart elsepart)))

(defthm natp-of-bvif
  (natp (bvif size test thenpart elsepart)))

(defthm bvchop-of-bvif
  (implies (and (<= n m)
                (natp n)
                (natp m))
           (equal (bvchop n (bvif m test a b))
                  (bvif n test a b)))
  :hints (("Goal" :cases ((and (integerp a) (integerp b))
                          (and (integerp a) (not (integerp b)))
                          (and (not (integerp a)) (integerp b)))
           :in-theory (enable bvif))))

(defthm bvif-same-branches
  (equal (bvif size test a a)
         (bvchop size a))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-when-true
  (equal (bvif size t a b)
         (bvchop size a))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-when-false
  (equal (bvif size nil a b)
         (bvchop size b))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-not
  (equal (bvif size (not test) x y)
         (bvif size test y x))
  :hints (("Goal" :in-theory (enable bvif))))

;fixme what if there is just one constant?
(defthm equal-of-constant-and-bvif-of-constant-and-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep k3)
                              (quotep size)))
                (natp size))
           (equal (equal k1 (bvif size test k2 k3))
                  (and (unsigned-byte-p size k1)
                       (if (equal k1 (bvchop size k2)) ;gets computed
                           (if (equal k1 (bvchop size k3)) ;gets computed
                               t
                             (bool-fix test))
                         (if (equal k1 (bvchop size k3)) ;gets computed
                             (not test)
                           nil)))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-when-true-cheap
  (implies test
           (equal (bvif size test a b)
                  (bvchop size a)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil)))
  :hints (("Goal" :in-theory (enable bvif))))


;for outside-in rewriting:
(defthm bvif-when-not-nil
  (implies test
           (equal (bvif size test x y)
                  (bvchop size x)))
  :rule-classes nil)

;for outside-in rewriting:
(defthm bvif-when-nil
  (implies (equal nil test)
           (equal (bvif size test x y)
                  (bvchop size y)))
  :rule-classes nil)

(defthm bvif-of-0-arg1
  (equal (bvif 0 test thenpart elsepart)
         0)
  :hints (("Goal" :in-theory (enable bvif))))

(defthm equal-of-bvif-same-1
  (implies (natp size)
           (equal (equal x (bvif size test x y))
                  (and (unsigned-byte-p size x)
                       (if test t (equal (bvchop size x) (bvchop size y))))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm equal-of-bvif-same-2
  (implies (natp size)
           (equal (equal x (bvif size test y x))
                  (and (unsigned-byte-p size x)
                       (if test (equal (bvchop size x) (bvchop size y)) t))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-bvchop-arg3
  (equal (bvif size test (bvchop size x) y)
         (bvif size test x y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-bvchop-arg4
  (equal (bvif size test x (bvchop size y))
         (bvif size test x y))
  :hints (("Goal" :in-theory (enable bvif))))

;move to bvif
(defthm bvif-equal-0-0-1
  (implies (unsigned-byte-p 1 bit)
           (equal (bvif 1 (equal bit 0) 0 1)
                  bit))
  :hints (("Goal" :in-theory (enable bvif myif))))

;move to bvif
(defthm bvif-equal-0-0-1-alt
  (implies (unsigned-byte-p 1 bit)
           (equal (bvif 1 (equal 0 bit) 0 1)
                  bit))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm myif-0-1-becomes-bvif
  (equal (myif test 0 1)
         (bvif 1 test 0 1))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthmd myif-becomes-bvif-when-sizes-are-1
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (myif test x y)
                  (bvif 1 test x y)))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthmd bvif-becomes-myif
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                (natp size))
           (equal (bvif size test x y)
                  (myif test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;todo: combine with other rules into a single rule
(defthmd equal-of-bvif-constants
  (implies (and (syntaxp (quotep v1))
                (syntaxp (quotep v2))
                (not (equal v1 v2))
                (unsigned-byte-p size v1)
                (unsigned-byte-p size v2)
                (posp size))
           (equal (equal v1 (bvif size test v1 v2))
                  (bool-fix test)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd equal-of-bvif-constants2
  (implies (and (syntaxp (quotep v1))
                (syntaxp (quotep v2))
                (not (equal v1 v2))
                (unsigned-byte-p size v1)
                (unsigned-byte-p size v2)
                (posp size))
           (equal (equal v2 (bvif size test v1 v2))
                  (not test)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm trim-of-bvif
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvif size2 test x y))
                  (bvif size1 test x y)))
  :hints (("Goal" :in-theory (e/d (trim) nil))))

(defthm bvif-of-myif-t-nil
  (equal (bvif size (myif test t nil) x y)
         (bvif size test x y))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm myif-of-bvif-becomes-bvif-arg1
  (implies (and (unsigned-byte-p size y)
                (natp size))
           (equal (myif test (bvif size test2 tp ep) y)
                  (bvif size test (bvif size test2 tp ep) y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm myif-of-bvif-becomes-bvif-arg2
  (implies (and (unsigned-byte-p size y)
                (natp size))
           (equal (myif test y (bvif size test2 tp ep))
                  (bvif size test y (bvif size test2 tp ep))))
    :hints (("Goal" :in-theory (enable bvif myif))))

(defthmd bvif-trim-constant-arg1
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep size))
                (not (unsigned-byte-p size x))
                )
           (equal (bvif size test x y)
                  (bvif size test (bvchop size x) y)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvif-trim-constant-arg2
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep size))
                (not (unsigned-byte-p size x))
                )
           (equal (bvif size test y x)
                  (bvif size test y (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvif))))

;dup
(defthm unsigned-byte-p-of-bvif-gen2
  (implies (and (<= n m)
                (natp n)
                (natp m))
           (unsigned-byte-p m (bvif n test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;bozo gross to guess the size is 1?
;bozo see MYIF-BECOMES-BVIF-WHEN-SIZES-ARE-1
(defthm if-becomes-bvif-1
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (if test x y)
                  (bvif 1 test x y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (bvif myif) (MYIF-BECOMES-BVIF-WHEN-SIZES-ARE-1)))))

(defthm bvif-numeric-bound
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvif size test x y) k))
  :hints (("Goal" :use (:instance UNSIGNED-BYTE-P-OF-Bvif-gen2
                                  (Y Y) (X X) (n size) (m size))
           ;bbozo how many of these rules do we freakin have?
           :in-theory (disable UNSIGNED-BYTE-P-OF-BVIF-GEN2))))

(defthm bvif-of-bvif-tighten-arg1
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvif size1 test (bvif size2 test2 x y) z)
                  (bvif size1 test (bvif size1 test2 x y) z)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-bvif-tighten-arg2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvif size1 test z (bvif size2 test2 x y))
                  (bvif size1 test z (bvif size1 test2 x y))))
  :hints (("Goal" :in-theory (enable bvif myif))))

;bozo copy all myif rules for bvif...
(defthm bvif-same-tests-and-vals
  (equal (bvif size test y (bvif size test x y))
         (bvchop size y))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm bvif-same-tests-and-vals2
  (equal (bvif size test (bvif size test x y) y)
         (bvif size test x y))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm bvif-same-tests
  (equal (bvif size test y (bvif size test x z))
         (bvif size test y z))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm bvif-same-tests2
  (equal (bvif size test (bvif size test x z) y)
         (bvif size test x y))
  :hints (("Goal" :in-theory (enable myif bvif))))

;bozo kind of a hack (what if more than one other if intervenes between the occurrences of test?)
(defthm bvif-test-test2-test
  (equal (bvif size test (bvif size test2 x (bvif size test y z)) w)
         (bvif size test (bvif size test2 x y) w))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-test-test2-test-alt
  (equal (bvif size test (bvif size test2 (bvif size test y z) x) w)
         (bvif size test (bvif size test2 y x) w))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-test-test2-test-alt2
  (equal (bvif size test w (bvif size test2 x (bvif size test y z)))
         (bvif size test w (bvif size test2 x z)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-test-test2-test-alt3
  (equal (bvif size test w (bvif size test2 (bvif size test y z) x))
         (bvif size test w (bvif size test2 z x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthmd <-of-bvif-constants-false
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2))
                (syntaxp (quotep k3))
                (<= (BVCHOP size K2) k1)
                (<= (BVCHOP size K3) k1))
           (not (< k1 (bvif size test k2 k3))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd <-of-bvif-constants-true
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2))
                (syntaxp (quotep k3))
                (< k1 (bvchop size k2))
                (< k1 (bvchop size k3)))
           (< k1 (bvif size test k2 k3)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-bvif-same-1
  (equal (bvif size test1 (bvif size test2 x y) x)
         (bvif size (or (not test1) test2) x y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-bvif-same-2
  (equal (bvif size test1 (bvif size test2 y x) x)
         (bvif size (or (not test1) (not test2)) x y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-bvif-same-3
  (equal (bvif size test1 x (bvif size test2 x y))
         (bvif size (or test1 test2) x y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-bvif-same-4
  (equal (bvif size test1 x (bvif size test2 y x))
         (bvif size (or test1 (not test2)) x y))
  :hints (("Goal" :in-theory (enable bvif))))

;drop?
(defthm unsigned-byte-p-of-bvif
  (implies (natp n)
           (unsigned-byte-p n (bvif n test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;drop?
(defthm unsigned-byte-p-of-bvif-gen
  (implies (and (<= n m)
                (natp n)
                (natp m))
           (unsigned-byte-p m (bvif n test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm BVIF-equal-bvif-same-test-and-else-part
  (equal (EQUAL (BVIF 32 test a b) (BVIF 32 test c b))
         (implies test
                  (equal (bvchop 32 a) (bvchop 32 c))))
  :hints (("Goal" :in-theory (enable BVIF myif))))

(defthm BVIF-equal-bvif-same-test-and-then-part
  (equal (EQUAL (BVIF 32 test b a) (BVIF 32 test b c))
         (implies (not test)
                  (equal (bvchop 32 a) (bvchop 32 c))))
  :hints (("Goal" :in-theory (enable BVIF myif))))

;drop?
(defthm usbp-of-bvif
  (implies (natp size)
           (unsigned-byte-p size (bvif size test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;drop?
(defthm usbp-of-bvif-gen
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (unsigned-byte-p n (bvif size test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;bozo gen somehow?
(defthm bvif-trim-constant-1
  (implies (and (syntaxp (and (quotep x) (quotep n)))
                (not (unsigned-byte-p n x))
                (natp n))
           (equal (bvif n test x y)
                  (bvif n test (bvchop n x) y)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-trim-constant-2
  (implies (and (syntaxp (and (quotep y) (quotep n)))
                (not (unsigned-byte-p n y))
                (natp n))
           (equal (bvif n test x y)
                  (bvif n test x (bvchop n y))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvif-of-myif-1
  (equal (bvif size test (myif a b c) d)
         (bvif size test (bvif size a b c) d))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-myif-2
  (equal (bvif size test d (myif a b c))
         (bvif size test d (bvif size a b c)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvchop-of-myif
  (equal (bvchop size (myif test a b))
         (bvif size test a b))
  :hints (("Goal" :in-theory (enable bvif myif))))

;same as bvif-of-myif-2?
(defthm bvif-of-myif-arg2
  (equal (bvif n test1 x (myif test a b))
         (bvif n test1 x (bvif n test a b)))
  :hints (("Goal" :in-theory (enable myif bvif bvif))))

;same as bvif-of-myif-1?
(defthm bvif-of-myif-arg1
  (equal (bvif n test1 (myif test a b) x)
         (bvif n test1 (bvif n test a b) x))
  :hints (("Goal" :in-theory (enable myif bvif))))

;move
(defthm myif-same-arg1-arg2-when-booleanp
  (implies (and (syntaxp (not (equal x *t*))) ;prevent loops
                (booleanp x))
           (equal (myif x x y)
                  (myif x t y)))
  :hints (("Goal" :in-theory (enable myif))))

;; Helps justify the correctness of Axe using IFF when dealing with contexts
(defthm bvif-of-bool-fix
  (equal (bvif size (bool-fix test) x y)
         (bvif size test x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline))))

;; If we have an assumption about x's size, try to show that y is the same size.
(defthmd myif-becomes-bvif-when-unsigned-byte-p-arg1
  (implies (and (unsigned-byte-p xsize x) ;xsize is a free variable
                (unsigned-byte-p xsize y))
           (equal (myif test x y)
                  (bvif xsize test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;; If we have an assumption about y's size, try to show that x is the same size
(defthmd myif-becomes-bvif-when-unsigned-byte-p-arg2
  (implies (and (unsigned-byte-p ysize y) ; ysize is a free variable
                (unsigned-byte-p ysize x))
           (equal (myif test x y)
                  (bvif ysize test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;; Just guesses that the size is 32
(defthmd myif-becomes-bvif-32
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (myif test y x)
                  (bvif 32 test y x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;; Just guesses that the size is 64
(defthmd myif-becomes-bvif-64
  (implies (and (unsigned-byte-p 64 x)
                (unsigned-byte-p 64 y))
           (equal (myif test y x)
                  (bvif 64 test y x)))
  :hints (("Goal" :in-theory (enable bvif myif))))
