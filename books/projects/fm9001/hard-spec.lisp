;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2021

(in-package "FM9001")

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/take" :dir :system)

;; ======================================================================

;; X and Z

(defconst *x* 'x)
(defconst *z* 'z)

(defun 4vp (x)
  (declare (xargs :guard t))
  (or (equal x t)
      (equal x nil)
      (equal x *x*)
      (equal x *z*)))

(defun 4v-fix (x)
  (declare (xargs :guard t))
  (mbe :logic (if (4vp x) x *x*)
       :exec  (if (or (equal x t)
                      (equal x nil)
                      (equal x *z*))
                  x
                *x*)))

(in-theory (disable 4vp))

(defun 4v-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (4vp (car x))
         (4v-listp (cdr x)))))

;; 3-valued logic

(defun 3vp (x)
  (declare (xargs :guard t))
  (or (equal x t)
      (equal x nil)
      (equal x *x*)))

(defun 3v-fix (x)
  (declare (xargs :guard t))
  (mbe :logic (if (3vp x) x *x*)
       :exec  (if (or (equal x t)
                      (equal x nil))
                  x
                *x*)))

(defthm 3v-fix-idempotent
  (equal (3v-fix (3v-fix x))
         (3v-fix x)))

(in-theory (disable 3vp))

(defun 3v-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (3vp (car x))
         (3v-listp (cdr x)))))

;; Bit-vector

(defun bvp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (booleanp (car x))
         (bvp (cdr x)))))

(defthmd booleanp-car-of-bvp
  (implies (bvp x)
           (booleanp (car x)))
  :rule-classes :type-prescription)

(defthm nth-of-bvp-is-booleanp
  (implies (bvp x)
           (booleanp (nth n x)))
  :rule-classes :type-prescription)

(defthm bvp-take
  (implies (bvp x)
           (bvp (take n x)))
  :hints (("Goal" :in-theory (enable repeat)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-nthcdr
  (implies (bvp x)
           (bvp (nthcdr n x)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-repeat-of-booleanp
  (implies (booleanp x)
           (bvp (repeat n x)))
  :hints (("Goal" :in-theory (enable bvp repeat)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-append
  (implies (bvp a)
           (equal (bvp (append a b))
                  (bvp b))))

(defthm bvp-rev
  (implies (bvp x)
           (bvp (rev x)))
  :hints (("Goal" :in-theory (enable rev))))

(defthm bvp-is-true-listp
  (implies (bvp x)
           (true-listp x)))

(defthm true-listp-make-list
  (true-listp (make-list n :initial-element v))
  :rule-classes :type-prescription)

(defthm bvp-make-list
  (equal (bvp (make-list n :initial-element v))
         (or (zp n) (booleanp v)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm len-make-list
  (equal (len (make-list n :initial-element v))
         (nfix n)))

(in-theory (disable bvp))

;; BV2P

(defun bv2p (x y)
  (declare (xargs :guard t))
  (and (bvp x)
       (bvp y)
       (= (len x) (len y))))

;; BVP-LEN

;; BVP-LEN is a concept introduced in order to be able to decide (BOOLEANP (CAR
;; (CD...DR X))) if X is a long-enough BVP.  This decision is made by
;; continually rewriting the hypothesis (BVP-LEN bvp n).

(defun bvp-len (bvp n)
  (declare (xargs :guard (natp n)))
  (and (bvp bvp)
       (<= n (len bvp))))

(defthmd bvp-len-cdr
  (implies (bvp-len x (1+ n))
           (bvp-len (cdr x) n))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bool-fix-car-x=x
  (implies (bvp-len x 1)
           (equal (bool-fix (car x))
                  (car x)))
  :hints (("Goal" :in-theory (enable bvp))))

(defthmd booleanp-car-x
  (implies (bvp-len x 1)
           (booleanp (car x)))
  :rule-classes :type-prescription)

(defthm bvp-len-nthcdr
  (implies (and (bvp bvp)
                (natp n)
                (<= n (len bvp)))
           (equal (bvp-len (nthcdr n bvp) m)
                  (<= m (- (len bvp) n))))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes :linear)

(in-theory (disable bvp-len))

;; PRIMITIVE SPECIFICATIONS

;; We use the "b-" functions instead of simply AND, OR, etc. in order to gain
;; ENABLE/DISABLE control.

(defun b-buf (x)
  (declare (xargs :guard t))
  (if x t nil))

(defun b-not (x)
  (declare (xargs :guard t))
  (not x))

(defun b-nand (a b)
  (declare (xargs :guard t))
  (not (and a b)))

(defun b-nand3 (a b c)
  (declare (xargs :guard t))
  (not (and a b c)))

(defun b-nand4 (a b c d)
  (declare (xargs :guard t))
  (not (and a b c d)))

(defun b-nand5 (a b c d e)
  (declare (xargs :guard t))
  (not (and a b c d e)))

(defun b-nand6 (a b c d e g)
  (declare (xargs :guard t))
  (not (and a b c d e g)))

(defun b-nand8 (a b c d e g h i)
  (declare (xargs :guard t))
  (not (and a b c d e g h i)))

(defun b-or (a b)
  (declare (xargs :guard t))
  (or (bool-fix a) (bool-fix b)))

(defun b-or3 (a b c)
  (declare (xargs :guard t))
  (or (bool-fix a) (bool-fix b) (bool-fix c)))

(defun b-or4 (a b c d)
  (declare (xargs :guard t))
  (or (bool-fix a) (bool-fix b) (bool-fix c) (bool-fix d)))

(defun b-xor (a b)
  (declare (xargs :guard t))
  (xor a b))

(defun b-xor3 (a b c)
  (declare (xargs :guard t))
  (b-xor (b-xor a b) c))

(defun b-equv (a b)
  (declare (xargs :guard t))
  (if a (if b t nil) (if b nil t)))

;; ???
(defun b-equv3 (a b c)
  (declare (xargs :guard t))
  (b-equv a (b-xor b c)))

(defun b-and (a b)
  (declare (xargs :guard t))
  (and a (bool-fix b)))

(defun b-and3 (a b c)
  (declare (xargs :guard t))
  (and a b (bool-fix c)))

(defun b-and4 (a b c d)
  (declare (xargs :guard t))
  (and a b c (bool-fix d)))

(defun b-nor (a b)
  (declare (xargs :guard t))
  (not (or a b)))

(defun b-nor3 (a b c)
  (declare (xargs :guard t))
  (not (or a b c)))

(defun b-nor4 (a b c d)
  (declare (xargs :guard t))
  (not (or a b c d)))

(defun b-nor5 (a b c d e)
  (declare (xargs :guard t))
  (not (or a b c d e)))

(defun b-nor6 (a b c d e g)
  (declare (xargs :guard t))
  (not (or a b c d e g)))

(defun b-nor8 (a b c d e g h i)
  (declare (xargs :guard t))
  (not (or a b c d e g h i)))

(defun b-if (c a b)
  (declare (xargs :guard t))
  (if c (if a t nil) (if b t nil)))

;; A boolean gate theory

(deftheory b-gates
  '(b-buf
    b-not
    b-nand b-nand3 b-nand4 b-nand5 b-nand6 b-nand8
    b-or b-or3 b-or4
    b-xor b-xor3
    b-equv b-equv3
    b-and b-and3 b-and4
    b-nor b-nor3 b-nor4 b-nor5 b-nor6 b-nor8
    b-if))

;; This lemma allows us to prove that specifications written in terms of
;; 4-valued gate-level functions (see below) are equivalent to Boolean
;; gate-level functions when the inputs are constrained to be Boolean, without
;; opening up the gate-level definitions, which would potentially result in
;; massive clauses and/or case splitting.

(defthmd booleanp-b-gates
  (and
   (booleanp (b-buf x))
   (booleanp (b-not x))
   (booleanp (b-nand a b))
   (booleanp (b-nand3 a b c))
   (booleanp (b-nand4 a b c d))
   (booleanp (b-nand5 a b c d e))
   (booleanp (b-nand6 a b c d e g))
   (booleanp (b-nand8 a b c d e g h i))
   (booleanp (b-or a b))
   (booleanp (b-or3 a b c))
   (booleanp (b-or4 a b c d))
   (booleanp (b-xor a b))
   (booleanp (b-xor3 a b c))
   (booleanp (b-equv a b))
   (booleanp (b-equv3 a b c))
   (booleanp (b-and a b))
   (booleanp (b-and3 a b c))
   (booleanp (b-and4 a b c d))
   (booleanp (b-nor a b))
   (booleanp (b-nor3 a b c))
   (booleanp (b-nor4 a b c d))
   (booleanp (b-nor5 a b c d e))
   (booleanp (b-nor6 a b c d e g))
   (booleanp (b-nor8 a b c d e g h i))
   (booleanp (b-if c a b))))

;; These "compound gates" correspond to LSI Logic macrocells.

(defun ao2 (a b c d)
  (declare (xargs :guard t))
  (b-nor (b-and a b) (b-and c d)))

(defun ao4 (a b c d)
  (declare (xargs :guard t))
  (b-nand (b-or a b) (b-or c d)))

(defun ao6 (a b c)
  (declare (xargs :guard t))
  (b-nor (b-and a b) c))

(defun ao7 (a b c)
  (declare (xargs :guard t))
  (b-nand (b-or a b) c))

;; Power and ground

(defun vss ()
  (declare (xargs :guard t))
  nil)

(defun vdd ()
  (declare (xargs :guard t))
  t)

;; VECTOR SPECIFICATIONS

;; We now define our basic vector hardware specification functions.

(defun v-buf (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (b-buf (car x))
          (v-buf (cdr x)))))

(defun v-not (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (b-not (car x))
          (v-not (cdr x)))))

(defun v-and (x y)
  (declare (xargs :guard (true-listp y)))
  (if (atom x)
      nil
    (cons (b-and (car x) (car y))
          (v-and (cdr x) (cdr y)))))

(defun v-or (x y)
  (declare (xargs :guard (true-listp y)))
  (if (atom x)
      nil
    (cons (b-or (car x) (car y))
          (v-or (cdr x) (cdr y)))))

(defun v-xor (x y)
  (declare (xargs :guard (true-listp y)))
  (if (atom x)
      nil
    (cons (b-xor (car x) (car y))
          (v-xor (cdr x) (cdr y)))))

(defun v-shift-right (a si)
  (declare (xargs :guard t))
  (if (atom a)
      nil
    (append (v-buf (cdr a))
            (list (bool-fix si)))))

(defun v-lsr (a)
  (declare (xargs :guard t))
  (v-shift-right a nil))

(defun v-ror (a si)
  (declare (xargs :guard t))
  (v-shift-right a si))

(defun v-asr (a)
  (declare (xargs :guard (true-listp a)))
  (if (atom a)
      nil
    (v-shift-right a
                   (nth (1- (len a)) a))))

(defun v-if (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (cons (if (if c (car a) (car b)) t nil)
          (v-if c (cdr a) (cdr b)))))

;; Vector functions return bit vectors.

(defthm bvp-v-buf
  (bvp (v-buf a))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-not
  (bvp (v-not a))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-and
  (bvp (v-and a b))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-or
  (bvp (v-or a b))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-xor
  (bvp (v-xor a b))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-shift-right
  (bvp (v-shift-right a si))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-lsr
  (bvp (v-lsr a))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-asr
  (bvp (v-asr a))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-ror
  (bvp (v-ror a c))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-if
  (bvp (v-if c a b))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

;; Lengths of vector functions

(defthm len-v-buf
  (equal (len (v-buf a))
         (len a)))

(defthm len-v-not
  (equal (len (v-not a))
         (len a)))

(defthm len-v-and
  (equal (len (v-and a b))
         (len a)))

(defthm len-v-or
  (equal (len (v-or a b))
         (len a)))

(defthm len-v-xor
  (equal (len (v-xor a b))
         (len a)))

(defthm len-v-shift-right
  (equal (len (v-shift-right a b))
         (len a)))

(defthm len-v-lsr
  (equal (len (v-lsr a))
         (len a)))

(defthm len-v-asr
  (equal (len (v-asr a))
         (len a)))

(defthm len-v-ror
  (equal (len (v-ror a b))
         (len a)))

(defthm len-v-if
  (equal (len (v-if c a b))
         (len a)))

;; APPEND lemmas for vector functions

(defthm append-v-and
  (implies (equal (len a) (len b))
           (equal (append (v-and a b)
                          (v-and d e))
                  (v-and (append a d) (append b e)))))

(defthm append-v-or
  (implies (equal (len a) (len b))
           (equal (append (v-or a b)
                          (v-or d e))
                  (v-or (append a d) (append b e)))))

(defthm append-v-xor
  (implies (equal (len a) (len b))
           (equal (append (v-xor a b)
                          (v-xor d e))
                  (v-xor (append a d) (append b e)))))

(defthm append-v-not
  (equal (append (v-not a) (v-not b))
         (v-not (append a b))))

(defthm append-v-buf
  (equal (append (v-buf a) (v-buf b))
         (v-buf (append a b))))

(defthm append-v-if
  (implies (equal (len a) (len b))
           (equal (append (v-if c a b) (v-if c d e))
                  (v-if c (append a d) (append b e)))))

;; A congruence for V-IF

(defthm v-if-c-congruence
  (implies c
           (equal (equal (v-if c a b) (v-if t a b))
                  t)))

;;  Vector functions with take/nthcdr

(defthm v-not-take
  (implies (<= n (len l))
           (equal (v-not (take n l))
                  (take n (v-not l)))))

(defthmd take-v-not
  (implies (<= n (len l))
           (equal (take n (v-not l))
                  (v-not (take n l)))))

(defthm nthcdr-nil
  (not (nthcdr n nil)))

(defthm v-not-nthcdr
  (equal (v-not (nthcdr n l))
         (nthcdr n (v-not l))))

(defthmd nthcdr-v-not
  (equal (nthcdr n (v-not l))
         (v-not (nthcdr n l))))

;; An interesting fact about V-NOT

(defthm nth-v-not
  (implies (and (consp l)
                (< n (len l)))
           (equal (nth n (v-not l))
                  (b-not (nth n l)))))

;; Another fascinating fact

(defthm v-or-make-list
  (implies (and (bvp a)
                (equal (len a) n))
           (equal (v-or (make-list n) a)
                  a))
  :hints (("Goal" :in-theory (enable bvp))))

(in-theory (disable v-buf v-not
                    v-and v-or v-xor
                    v-shift-right
                    v-if))

;; V-TO-NAT and NAT-TO-V

(defun v-to-nat (v)
  (declare (xargs :guard t))
  (if (atom v)
      0
    (+ (if (car v) 1 0)
       (* 2 (v-to-nat (cdr v))))))

(defthm natp-v-to-nat
  (natp (v-to-nat v))
  :rule-classes :type-prescription)

(in-theory (disable v-to-nat))

(defun bit->bool (x)
  (declare (xargs :guard (bitp x)))
  (if (= x 1) t nil))

(defthm booleanp-bit->bool
  (booleanp (bit->bool x))
  :rule-classes :type-prescription)

(local (include-book "arithmetic-5/top" :dir :system))

(defun nat-to-v (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))))
  (if (zp n)
      nil
    (cons (bit->bool (mod x 2))
          (nat-to-v (floor x 2) (1- n)))))

(defthm len-nat-to-v
  (equal (len (nat-to-v x n))
         (nfix n)))

(defthm take-nat-to-v
  (implies (and (<= n m)
                (integerp m))
           (equal (take n (nat-to-v x m))
                  (nat-to-v x n))))

(defthm nthcdr-of-len-l
  (implies (and (true-listp l)
                (equal (len l) n))
           (not (nthcdr n l))))

(defthm nthcdr-nat-to-v-0-hack
  (implies (and (<= n m)
                (natp m)
                (natp n))
           (equal (nthcdr n (nat-to-v 0 m))
                  (nat-to-v 0 (- m n)))))

(defthm bvp-nat-to-v
  (bvp (nat-to-v x n))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm car-nat-to-v-0-is-nil
  (not (car (nat-to-v 0 n))))

(local
 (defun any-of-nat-to-v-0-is-nil-induct (m n)
   (if (zp m)
       n
     (any-of-nat-to-v-0-is-nil-induct (1- m) (1- n)))))

(defthm any-of-nat-to-v-0-is-nil
  (not (nth n (nat-to-v 0 m)))
  :hints (("Goal" :induct (any-of-nat-to-v-0-is-nil-induct m n))))

(in-theory (disable nat-to-v))

;; V-NTH

(defund v-nth (v lst)
  (declare (xargs :guard (true-listp lst)))
  (nth (v-to-nat v) lst))

;; UPDATE-V-NTH

(defund update-v-nth (v value lst)
  (declare (xargs :guard (true-listp lst)))
  (update-nth (v-to-nat v) value lst))

;; V-NZP and V-ZP

(defun v-nzp (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (or (car x)
        (v-nzp (cdr x)))))

(defun v-zp (x)
  (declare (xargs :guard t))
  (not (v-nzp x)))

(defthm booleanp-v-nzp
  (implies (bvp x)
           (booleanp (v-nzp x)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes :type-prescription)

(defthm v-nzp-as-or-crock
  (and
   (implies (v-nzp (take n a))
            (v-nzp a))
   (implies (v-nzp (nthcdr n a))
            (v-nzp a)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm not-v-nzp-take-nthcdr
  (implies (and (not (v-nzp (take n l)))
                (not (v-nzp (nthcdr n l))))
           (not (v-nzp l))))

(defthm v-zp-as-and-crock
  (implies (and (v-zp (take n a))
                (v-zp (nthcdr n a)))
           (v-zp a)))

(defthm v-zp-v-xor-x-x
  (v-zp (v-xor x x))
  :hints (("Goal" :in-theory (enable v-xor))))

(defthm v-nzp-v-xor=not-equal
  (implies (bv2p a b)
           (equal (v-nzp (v-xor a b))
                  (not (equal a b))))
  :hints (("Goal" :in-theory (enable bvp v-xor))))

(defthm v-zp-make-list
  (v-zp (make-list n))
  :hints (("Goal" :in-theory (enable repeat)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable v-nzp v-zp))

;; V-NEGP

(defun v-negp (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom (cdr x))
        (car x)
      (v-negp (cdr x)))))

(defthm booleanp-v-negp
  (implies (bvp v)
           (booleanp (v-negp v)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes :type-prescription)

(defthm v-negp-as-nth
  (implies (not (equal (len bv) 0))
           (equal (v-negp bv)
                  (nth (1- (len bv)) bv))))

(in-theory (disable v-negp v-negp-as-nth))

;; SIGN-EXTEND

(defun sign-extend (v n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (if (atom v)
        (make-list n)
      (if (atom (cdr v))
          (cons (bool-fix (car v))
                (make-list (1- n)
                           :initial-element (bool-fix (car v))))
        (cons (bool-fix (car v))
              (sign-extend (cdr v) (1- n)))))))

(defthm len-sign-extend
  (equal (len (sign-extend v n))
         (nfix n)))

(local
 (defthm bvp-repeat-bool
   (implies (booleanp x)
            (bvp (repeat n x)))
   :hints (("Goal" :in-theory (enable bvp repeat)))
   :rule-classes (:rewrite :type-prescription)))

(defthm bvp-sign-extend
  (bvp (sign-extend v n))
   :hints (("Goal" :in-theory (enable bvp repeat))))

(defthm sign-extend-as-append
  (implies (and (bvp v)
                (integerp n)
                (<= (len v) n)
                (not (equal (len v) 0)))
           (equal (sign-extend v n)
                  (append v (make-list (- n (len v))
                                       :initial-element
                                       (nth (1- (len v)) v)))))
  :hints (("Goal" :in-theory (enable bvp repeat))))

(in-theory (disable sign-extend sign-extend-as-append))

;; V-ADDER is a recursive definition of a binary adder.

(defun v-adder (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      (list (bool-fix c))
    (cons (b-xor3 c (car a) (car b))
          (v-adder (b-or3 (b-and (car a) (car b))
                          (b-and (car a) c)
                          (b-and (car b) c))
                   (cdr a)
                   (cdr b)))))

(defthm len-of-v-adder
  (equal (len (v-adder c a b))
         (1+ (len a))))

(defthm bvp-v-adder
  (bvp (v-adder c a b))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable v-adder))

(defun v-adder-output (c a b)
  (declare (xargs :guard (true-listp b)))
  (take (len a) (v-adder c a b)))

(defthm len-v-adder-output
  (equal (len (v-adder-output c a b))
         (len a)))

(defun v-adder-carry-out (c a b)
  (declare (xargs :guard (true-listp b)))
  (nth (len a) (v-adder c a b)))

(defun v-adder-overflowp (c a b)
  (declare (xargs :guard (and (consp a)
                              (true-listp a)
                              (consp b)
                              (true-listp b))))
  (b-and (b-equv (nth (1- (len a)) a)
                 (nth (1- (len b)) b))
         (b-xor (nth (1- (len a)) a)
                (nth (1- (len a)) (v-adder-output c a b)))))

(defun v-subtracter-output (c a b)
  (declare (xargs :guard (true-listp b)))
  (v-adder-output (b-not c) (v-not a) b))

(defthm len-v-subtracter-output
  (equal (len (v-subtracter-output c a b))
         (len a)))

(defun v-subtracter-carry-out (c a b)
  (declare (xargs :guard (true-listp b)))
  (b-not (v-adder-carry-out (b-not c) (v-not a) b)))

(defun v-subtracter-overflowp (c a b)
  (declare (xargs :guard (and (consp a)
                              (true-listp a)
                              (consp b)
                              (true-listp b))
                  :guard-hints (("Goal" :in-theory (enable v-not)))))
  (v-adder-overflowp (b-not c) (v-not a) b))

(defun v-inc (x)
  (declare (xargs :guard (true-listp x)))
  (v-adder-output t x (nat-to-v 0 (len x))))

(defun v-dec (x)
  (declare (xargs :guard (true-listp x)))
  (v-subtracter-output t (nat-to-v 0 (len x)) x))

(defthm bvp-len-v-inc-v-dec
  (and (bvp (v-inc x))
       (bvp (v-dec x))
       (equal (len (v-inc x)) (len x))
       (equal (len (v-dec x)) (len x))))

(in-theory (disable v-inc v-dec))

;; Prove the correctness of the vector buffer, selector, and adder.

(defthm v-buf-works
  (implies (bvp x)
           (equal (v-buf x) x))
  :hints (("Goal" :in-theory (enable bvp v-buf))))

(defthm v-if-works
  (implies (bv2p x y)
           (equal (v-if c x y)
                  (if c x y)))
  :hints (("Goal" :in-theory (enable bvp v-if))))

(defthm v-adder-works
  (implies (bv2p x y)
           (equal (v-to-nat (v-adder c x y))
                  (+ (if c 1 0)
                     (v-to-nat x)
                     (v-to-nat y))))
  :hints (("Goal" :in-theory (enable bvp v-adder v-to-nat))))

;; V-THREEFIX -- A useful concept for registers.

(defun v-threefix (v)
  (declare (xargs :guard t))
  (if (atom v)
      nil
    (cons (3v-fix (car v))
          (v-threefix (cdr v)))))

(defthm open-v-threefix
  (and
   (implies (atom v)
            (equal (v-threefix v)
                   nil))
   (implies (consp v)
            (equal (v-threefix v)
                   (cons (3v-fix (car v))
                         (v-threefix (cdr v)))))))

(defthm v-threefix-bvp
  (implies (bvp v)
           (equal (v-threefix v)
                  v))
  :hints (("Goal" :in-theory (enable bvp))))

(defthm len-v-threefix
  (equal (len (v-threefix x))
         (len x)))

(defthm append-v-threefix
  (equal (append (v-threefix a)
                 (v-threefix b))
         (v-threefix (append a b))))

(defthmd v-threefix-append
  (equal (v-threefix (append a b))
         (append (v-threefix a) (v-threefix b))))

(defthm v-threefix-idempotence
  (equal (v-threefix (v-threefix x))
         (v-threefix x)))

(defthm bvp-v-threefix
  (implies (true-listp v)
           (equal (bvp (v-threefix v))
                  (bvp v)))
  :hints (("Goal" :in-theory (enable bvp))))

(defthm v-threefix-make-list-4x
  (equal (v-threefix (make-list n :initial-element *x*))
         (make-list n :initial-element *x*))
  :hints (("Goal" :in-theory (enable repeat))))

(in-theory (disable v-threefix))

;;   V-FOURFIX

(defun v-fourfix (v)
  (declare (xargs :guard t))
  (if (atom v)
      nil
    (cons (4v-fix (car v))
          (v-fourfix (cdr v)))))

(defthm 4v-listp-v-fourfix
  (4v-listp (v-fourfix x)))

(defthm len-v-fourfix
  (equal (len (v-fourfix v))
         (len v)))

(defthm bvp-v-fourfix
  (implies (bvp v)
           (equal (v-fourfix v) v))
  :hints (("Goal" :in-theory (enable bvp))))

(defthm v-fourfix-make-list
  (implies (4vp x)
           (equal (v-fourfix (make-list n :initial-element x))
                  (make-list n :initial-element x)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm v-threefix-v-fourfix
  (equal (v-threefix (v-fourfix v))
         (v-threefix v))
  :hints (("Goal" :in-theory (enable 3vp 4vp v-threefix))))

(in-theory (disable v-fourfix))

;; V-IFF -- A reducing vector IFF.  Vector equivalence.

(defun v-iff (a b)
  (declare (xargs :guard t))
  (if (or (atom a) (atom b))
      t
    (and (iff (car a) (car b))
         (v-iff (cdr a) (cdr b)))))

(defthm v-iff-x-x
  (v-iff x x))

(local
 (defthm append-associativity
   (equal (append (append x y) z)
          (append x (append y z)))))

(defthm v-iff-revappend
  (implies (equal (len a) (len b))
           (equal (v-iff (revappend a x) (revappend b y))
                  (and (v-iff a b)
                       (v-iff x y)))))

(defthm v-iff-append
  (implies (equal (len a) (len b))
           (equal (v-iff (append a x) (append b y))
                  (and (v-iff a b)
                       (v-iff x y)))))

(defthm v-iff-rev
  (implies (equal (len a) (len b))
           (equal (v-iff (rev a) (rev b))
                  (v-iff a b))))

(defthm v-iff=equal
  (implies (bv2p a b)
           (equal (v-iff a b)
                  (equal a b)))
  :hints (("Goal" :in-theory (enable bvp))))

(in-theory (disable v-iff))

;; Odds and ends...

(defthm bvp-subseq
  (implies (and (bvp v)
                (<= n (len v)))
           (bvp (subseq v m n)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-subseq-list
  (equal (len (subseq-list x i j))
         (nfix (- j i))))

(defthm booleanp-if*
  (implies (and (booleanp a)
                (booleanp b))
           (booleanp (if* c a b)))
  :rule-classes :type-prescription)

(defthm true-listp-if*
  (implies (and (true-listp a)
                (true-listp b))
           (true-listp (if* c a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-if*
  (implies (and (bvp a)
                (bvp b))
           (bvp (if* c a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-if*
  (implies (equal (len a) (len b))
           (equal (len (if* c a b))
                  (len a))))

(defthm if*-rewrite
  (and (equal (if* t a b) a)
       (equal (if* nil a b) b)))

