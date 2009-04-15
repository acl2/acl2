#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;(include-book "memberp" :dir :lists)
(include-book "basic" :dir :bags)

;;
;; ADDR-RANGE
;;

;; I like this function better than the very similar gacc::blk.  I'd like to
;; change gacc::blk to act like this function.  -ews

;do we want this, or the wrapped version, or both?
;what should this do when base is not an integerp?
;previously we got gross behavior like (addr-range t 4) = '(t 1 2 3). Now we call ifix on base.
(defund addr-range (base k)
  (declare (type t base)
           (type (integer 0 *) k)
           (xargs :measure (acl2-count k)))
  (if (zp k)
      nil
    (cons (ifix base) 
          (addr-range (+ 1 (ifix base)) (1- k)))))

;consider disabling (:executable-counterpart addr-range) as we do for gacc::sblk?

(defthm addr-range-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (addr-range base size)
                  nil))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-size-is-not-positive
  (implies (<= size 0)
           (equal (addr-range base size) nil))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (addr-range base size)
                  (addr-range 0 size)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-size-is-0
  (equal (addr-range base 0)
         nil)
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-size-is-1
  (equal (addr-range base 1)
         (list (ifix base)))
  :hints (("Goal" :expand (addr-range base 1)
           :in-theory (enable addr-range))))

(defthm consp-of-addr-range
  (equal (consp (addr-range base size))
         (and (integerp size)
              (< 0 size)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-iff
  (iff (addr-range ptr size)
       (not (zp size)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm len-of-addr-range
  (equal (len (addr-range base size))
         (nfix size))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm car-of-addr-range
  (equal (car (addr-range base size))
         (if (zp size)
             nil
           (ifix base)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm cdr-of-addr-range
  (equal (cdr (addr-range ad numbytes))
         (if (zp numbytes)
             nil
           (addr-range (+ 1 (ifix ad)) (+ -1 numbytes))))
  :hints (("Goal" :expand  (addr-range ad numbytes)
           :in-theory (enable addr-range))))


;might be expensive, so we disable it..
(defthmd memberp-when-x-is-an-integer-listp
  (implies (and (integer-listp x)
                (not (integerp a)))
           (not (bag::memberp a x))))

(defthm integer-listp-of-addr-range
  (integer-listp (addr-range base k))
  :hints (("Goal" :in-theory (enable addr-range))))

;expensive?
(defthm memberp-of-addr-range
  (equal (bag::memberp k (addr-range i j))
         (and (<= (ifix i) k)
              (< k (+ (ifix i) j))
              (integerp j)
              (<= 0 j)
              (integerp k)))
  :hints (("Goal" :in-theory (enable ifix addr-range))))

(defthm memberp-of-addr-range-base
  (equal (bag::memberp base (addr-range base k))
         (and (< 0 k)
              (integerp base)
              (integerp k))))

;bzo. just use memberp-of-cons?
(defthm memberp-cons-addr-range
  (equal (bag::memberp addr1 (cons addr2 (addr-range addr3 k)))
         (or (equal addr1 addr2)
             (bag::memberp addr1 (addr-range addr3 k)))))

(defthm addr-range-of-ifix
  (equal (addr-range (ifix base) size)
         (addr-range base size))
  :hints (("Goal" :in-theory (enable addr-range ifix))))

;bzo do we want this?
(defthm addr-range-plus
  (implies (and (< addr (+ base k))
                (<= base addr)
                (integerp k)
                (< 0 k)
                (integerp addr)
                (integerp base))
           (bag::memberp addr (addr-range base k))))

;bzo do we want this?
(defthm addr-range-plus-corollary
  (implies (and (equal addr (+ base j)) ;j is a free variable
                (< j k)
                (acl2::natp j)
                (integerp k)
;                (< 0 k)
                (integerp base))
           (bag::memberp addr (addr-range base k))))

(defthm addr-not-member-addr-range-greater
  (implies (and (< addr1 addr2)
                (integerp addr2))
           (not (bag::memberp addr1 (addr-range addr2 n)))))

;drop? see ADDR-NOT-MEMBER-ADDR-RANGE-GREATER
(defthm addr-range-monotonic
  (implies (and (bag::memberp addr (addr-range base k))
                (integerp base))
           (<= base addr))
  :rule-classes nil)


;; ;bzo. The enable proved it - consider a new rule that shows (subbagp
;; ;(cons a x) y) if a and x have no overlap and both are subbagps of y.
;;
;; (defthm SUBBAGP-of-2-addr-ranges
;;   (implies (and (integerp size1)
;;                 (integerp size2)
;;                 (integerp base2)
;;                 (integerp base1)
;;                 )
;;            (equal (BAG::SUBBAGP (ADDR-RANGE base1 size1)
;;                                 (ADDR-RANGE base2 size2))
;;                   (or (zp size1)
;;                       (and  (<= base2 base1)
;;                             (<= (+ base1 size1) (+ base2 size2))))))
;;   :hints (("Goal" :in-theory (enable BAG::SUBBAGP-OF-CONS))))

(defthm subbagp-of-2-addr-ranges-better
  (equal (bag::subbagp (addr-range base1 size1)
                       (addr-range base2 size2))
         (or (zp size1)
             (and (<= (ifix base2) (ifix base1))
                  (<= (+ (ifix base1) (ifix size1))
                      (+ (ifix base2) (ifix size2))))))
  :hints (("Goal" :cases ((and (integerp size2) (integerp size1))
                          (and (not (integerp size2)) (integerp size1))
                          (and (integerp size2) (not (integerp size1)))
                          
                          )
           :in-theory (enable ifix zp bag::subbagp-of-cons addr-range))))

;special case of subbagp-of-2-addr-ranges in case we diable that one
(defthm subbagp-of-two-addr-ranges-with-same-base
 (implies (< (ifix size1) (ifix size2))
          (BAG::SUBBAGP (ADDR-RANGE base size1)
                        (ADDR-RANGE base size2))))

;maybe we want helper-1 and helper-2 (perhaps somewhat improved) to still be around?

;; (defthm helper-1
;;   (IMPLIES (AND (< (+ -1 BASE1 SIZE1) BASE2)
;;                 (integerp base1)
;;                 (integerp base2)
;;                 (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 )
;;            (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                           (ADDR-RANGE BASE2 SIZE2)))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

;; (defthm helper-2
;;   (IMPLIES (AND (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 (integerp base1)
;;                 (integerp base2)
;;                 (<= BASE2 (+ -1 BASE1 SIZE1))
;;                 (< (+ -1 BASE2 SIZE2) BASE1)
;;                 )
;;            (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                           (ADDR-RANGE BASE2 SIZE2)))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

;; ;drop?
;; (defthm helper-3
;;   (IMPLIES (AND (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 (integerp base1)
;;                 (integerp base2)
;;                 (<= BASE2 (+ -1 BASE1 SIZE1))
;;                 (NOT (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                                     (ADDR-RANGE BASE2 SIZE2))))
;;            (<= BASE1 (+ -1 BASE2 SIZE2)))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

;; (defthm helper-4
;;   (IMPLIES (AND (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 (INTEGERP BASE1)
;;                 (INTEGERP BASE2)
;;                 (<= BASE2 (+ -1 BASE1 SIZE1))
;;                 (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                                (ADDR-RANGE BASE2 SIZE2)))
;;            (< (+ -1 BASE2 SIZE2) BASE1))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))



(encapsulate
 () 
 (local (defthm disjoint-of-two-addr-ranges-helper
          (implies (integerp base2)
                   (equal (BAG::DISJOINT (ADDR-RANGE base1 size1) (ADDR-RANGE base2 size2))
                          (or (not (integerp size1))
                              (not (integerp size2))
                              (<= size1 0)
                              (<= size2 0)
                              (< (+ -1 (ifix base1) size1) base2)
                              (< (+ -1 base2 size2) (ifix base1)))))
          :hints (("Goal" :cases ((equal 0 size1))
                   :in-theory (enable addr-range  BAG::DISJOINT-OF-CONS-ONE)))))


;bzo Consider disabling this?
 (defthm disjoint-of-two-addr-ranges
   (equal (bag::disjoint (addr-range base1 size1) (addr-range base2 size2))
          (or (< (+ -1 (ifix base1) size1) (ifix base2))
              (< (+ -1 (ifix base2) size2) (ifix base1))
              (not (integerp size1))
              (not (integerp size2))
              (<= size1 0)
              (<= size2 0)))
   :hints (("Goal" :use (:instance disjoint-of-two-addr-ranges-helper (base1 (ifix base1)) (base2 (ifix base2)))
            :in-theory (disable disjoint-of-two-addr-ranges-helper)))))

(defthm unique-of-addr-range
  (bag::unique (addr-range base size))
  :hints (("Goal" :in-theory (enable addr-range bag::unique-of-cons))))

(defthm not-memberp-of-addr-range-when-not-integerp
  (implies (not (integerp k))
           (not (bag::memberp k (addr-range i j))))
  :hints (("Goal" :in-theory (enable addr-range))))

;I doubt I want this enabled very often...
(defthmd addr-range-expand-when-k-is-a-constant
  (implies (syntaxp (quotep k))
           (equal (addr-range base k)
                  (if (zp k)
                      nil
                      (cons (ifix base)
                            (addr-range (+ 1 (ifix base)) (1- k))))))
  :hints (("Goal" :in-theory (enable addr-range))))

;addr-range when zp?

(defthm addr-ranges-equal-same-base
  (equal (EQUAL (ADDR-RANGE base size1)
                (ADDR-RANGE base size2))
         (equal (nfix size1)
                (nfix size2)))
  :hints (("Goal" :in-theory (enable addr-range))))

(encapsulate
 ()
 (local (defthm equal-of-two-addr-ranges-helper
          (implies (and (not (zp size)) 
                        (not (zp size2)))
                   (equal (EQUAL (ADDR-RANGE base size)
                                 (ADDR-RANGE base2 size2))
                          (and (equal size size2)
                               (equal (ifix base)
                                      (ifix base2)))))
          :hints (("Goal" :in-theory (enable addr-range)))))

 (defthm equal-of-two-addr-ranges
   (equal (EQUAL (ADDR-RANGE base size)
                 (ADDR-RANGE base2 size2))
          (if (zp size)
              (zp size2)
            (if (zp size2)
                nil 
              (and (equal size size2)
                   (equal (ifix base)
                          (ifix base2))))))
   :hints (("Goal" :use (:instance equal-of-two-addr-ranges-helper)
            :in-theory (e/d (zp) (equal-of-two-addr-ranges-helper))))))
