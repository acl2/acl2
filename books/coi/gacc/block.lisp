#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

(include-book "basic" :dir :bags)

;bzo make this local?
(include-book "arithmetic/top-with-meta" :dir :system) 

(in-theory (disable acl2::append-true-listp-type-prescription)) ;we have a better rule

;;
;; BLK-REC
;;

;returns a list of the integers from base+off to base+max-1
;Eric thinks the "max" parameter should be called "size".
;why does this take 3 parameters?
(defund blk-rec (base off max)
  (declare (type t base off max)
           (xargs :measure (nfix (- (ifix max) (ifix off)))))
  (if (not (< (ifix off) (ifix max)))
      nil
    (cons (+ (ifix off) (ifix base)) 
          (blk-rec base (1+ (ifix off)) (ifix max)))))

(defthm true-listp-blk-rec
  (true-listp (blk-rec base off size))
  :rule-classes (:rewrite :TYPE-PRESCRIPTION))

(defthm blk-rec-non-integer-ptr
  (implies (not (integerp x))
           (equal (blk-rec x y z)
                  (blk-rec 0 y z)))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm blk-rec-non-integer-off
  (implies (not (integerp off))
           (equal (blk-rec ptr off max)
                  (blk-rec ptr 0 max)))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm blk-rec-non-integer-size
  (implies (not (integerp size))
           (equal (blk-rec base off size)
                  (blk-rec base off 0)))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm unfixed-base-blk-rec
  (equal (blk-rec (ifix base) off max)
         (blk-rec base off max))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm len-blk-rec
  (equal (len (blk-rec base off max))
         (nfix (- (ifix max) (ifix off))))
  :hints (("goal" :in-theory (enable ifix blk-rec))))

(defthm integer-listp-blk-rec
  (integer-listp (blk-rec ptr off max))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm consp-blk-rec
  (equal (consp (blk-rec base off max))
         (< (ifix off) (ifix max)))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm blk-rec-consp-type
  (implies (and (< off max)
                (integerp off)
                (integerp max)
                )
           (consp (blk-rec base off max)))
  :rule-classes (:type-prescription))

(defthmd open-blk-rec
  (implies (< (ifix off) (ifix size))
           (equal (blk-rec ptr off size)
                  (cons (+ (ifix off) (ifix ptr))
                        (blk-rec ptr (1+ (ifix off)) (ifix size)))))
  :hints (("Goal" :in-theory '(blk-rec))))


(defthm subbagp-blk-rec-memberp
  (implies (and (subbagp (blk-rec ptr off size) y)
                (integerp off)
                (integerp size)
                (< off size)
                (integerp ptr)
                )
           (memberp (+ off ptr) y))
  :hints (("Goal" :in-theory (enable blk-rec))))

(encapsulate
 ()
 (local (defun blk-blk-rec (off b1 m1 b2 m2)
          (declare (xargs :measure (nfix (- (max (ifix m1) (ifix m2)) (ifix off)))))
          (let ((off (ifix off))
                (m1  (ifix m1))
                (m2  (ifix m2)))
            (if (and (<= m1 off)
                     (<= m2 off))
                nil
              (cons (list off b1 m1 b2 m2)
                    (blk-blk-rec (1+ off) 
                                 b1 m1
                                 b2 m2))))))

;move hyps to conclusion?
;this requires that off be the same in both cases
 (defthm equal-blk-rec-to-equal-args
   (implies (and (integerp b1)
                 (integerp b2)
                 (integerp m1)
                 (integerp m2)
                 (integerp off)
;     (< off m1)
                 )
            (equal (equal (blk-rec b1 off m1) (blk-rec b2 off m2))
                   (if (< off m2)
                       (and (equal b1 b2)
                            (equal m1 (ifix m2)))
                     (equal (blk-rec b1 off m1) nil) ;simplify this?
                     )))
   :hints (("goal" :induct (blk-blk-rec off b1 m1 b2 m2)
            :in-theory (enable ifix blk-rec)))))

;added by eric (make blk analogues of these?)
(defthm car-of-blk-rec
  (equal (car (blk-rec base off max))
         (if (< (ifix off) (ifix max))
             (+ (ifix off) (ifix base))
           nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

;Treat as zeros non-integers in the comparison
(defthm disjoint-blk-rec-subbagp
  (implies (and (disjoint list (blk-rec ptr off size1))
                (<= (ifix size0) (ifix size1)))
           (disjoint list (blk-rec ptr off size0)))
  :hints (("Goal" :in-theory (enable blk-rec)
           :do-not '(generalize eliminate-destructors)))) 
  
(defthm disjoint-blk-rec-subbagp-right
  (implies (and (not (disjoint list (blk-rec ptr off size0)))
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint list (blk-rec ptr off size1))
                  nil))) 
   
(defthm disjoint-blk-rec-subbagp-left
  (implies (and (not (disjoint (blk-rec ptr off size0) list))
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint (blk-rec ptr off size1) list)
                  nil)))
   
;make a blk analogue of this?
(defthm blk-rec-non-membership-less
  (implies (< n (+ (ifix ptr) (ifix off)))
           (equal (memberp n (blk-rec ptr off m))
                  nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm blk-rec-non-membership-more
  (implies (<= (+ (ifix ptr) (ifix m)) n)
           (equal (memberp n (blk-rec ptr off m)) nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm blk-rec-membership-subbagp
  (implies (and (not (memberp addr (blk-rec ptr off size2)))
                (<= (ifix size1) (ifix size2))
                )
           (equal (memberp addr (blk-rec ptr off size1))
                  nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm blk-rec-membership
  (implies (and (integerp ptr)
                (< (ifix off) (ifix size))
                (<= (+ (ifix base) (ifix off)) (ifix ptr))
                (< (ifix ptr) (+ (ifix base) (ifix size))))
           (memberp ptr (blk-rec base off size)))
  :hints (("Goal" :in-theory (e/d (blk-rec)
                                  ( BLK-REC-NON-INTEGER-PTR ;why??
                                    blk-rec-non-integer-size
                                    )))))

(defthm null-blk-rec
  (implies (<= (ifix max) (ifix off))
           (equal (blk-rec ptr off max)
                  nil))
  :hints (("Goal" :in-theory (enable blk-rec))))


;In order to keep usable need the integer hyps
;The problem taking them out comes cause x and rptr could be rationals
;For example, if x=5/2 and rptr=3/2, lhs of equal starts at 4+(ifix off)
; and rhs starts at 0+(ifix off).
(defthm blk-rec-normalization
  (implies (and (integerp rptr)
                (integerp x)
                (<= 0 x))
           (equal (blk-rec (+ x rptr) roff rmax)
                  (blk-rec rptr 
                           (+ x (ifix roff)) 
                           (+ x (ifix rmax)))))
  :hints (("goal" :in-theory (enable blk-rec)
           :induct (blk-rec (+ x rptr) roff rmax))))

(encapsulate
 ()
 (local (defun blk-rec-induction (max1 max2 off ptr)
          (declare (xargs :measure (NFIX (BINARY-+ (IFIX MAX1) (UNARY-- (IFIX OFF))))
                          :guard (and (equal max2 max2) (equal ptr ptr))))
          (if (<= (ifix max1) (ifix off))
              nil
            (blk-rec-induction (ifix max1) (ifix max2) (1+ (ifix off)) ptr))))

;allow the off params to differ?             
 (defthm blk-rec-upper-subbagp
   (implies (<= (ifix max1) (ifix max2))
            (subbagp (blk-rec ptr off max1)
                     (blk-rec ptr off max2)))
   :hints (("goal" :in-theory (enable blk-rec)
            :induct (blk-rec-induction max1 max2 off ptr)))))

(defthm blk-rec-lower-subbagp
  (implies (and (<= (ifix m) (ifix n))
                (<= (ifix max1) (ifix max2))
                )
           (subbagp (blk-rec ptr n max1)
                    (blk-rec ptr m max2)))
  :hints (("Goal" :in-theory (enable blk-rec)
           :induct (blk-rec ptr m max2))))

(defthm disjoint-of-blk-recs-1
   (implies (and (<= (+ (ifix rptr) (ifix rsize)) (ifix wptr))
                 (<= 0 (ifix roff))
                 (<= 0 (ifix woff))
                 )
            (disjoint (blk-rec rptr roff rsize)
                      (blk-rec wptr woff wsize)))
   :hints (("Goal" :in-theory (e/d ( LIST::memberp-of-cons
                                     blk-rec
                                     bag::disjoint-of-cons-one)
                                   ( bag::disjoint-commutative ;why??
                                     ))
            :induct (blk-rec rptr roff rsize)
            )))

(defthm disjoint-of-blk-recs-2
  (implies (and (<= (+ (ifix wptr) (ifix wsize)) (ifix rptr))
                (<= 0 (ifix roff))
                (<= 0 (ifix woff))
                )
           (disjoint (blk-rec rptr roff rsize)
                     (blk-rec wptr woff wsize)))
  :hints (("Goal" :in-theory (disable blk-rec
;DISJOINT-BLK-REC-SUBBAGP-LEFT
                                      disjoint-of-blk-recs-1)
           :use (:instance disjoint-of-blk-recs-1
                           (rptr wptr)
                           (wptr rptr)
                           (roff woff)
                           (woff roff)
                           (wsize rsize)
                           (rsize wsize)
                           ))))
                                       
(defthm memberp-of-blk-rec-when-not-integerp
  (implies (not (integerp x))
           (not (bag::memberp x (gacc::blk-rec base offset max))))
  :hints (("Goal" :in-theory (enable gacc::blk-rec))))

(defthm unique-blk-rec
  (unique (blk-rec base off size))
  :hints (("goal" :in-theory (enable unique blk-rec))))




;;
;; BLK
;;


;return a list of the addresses from base to base+size-1
(defund blk (base size)
  (declare (type t base size))
  (blk-rec base 0 size))
 
;We disable the executable-counterpart of blk, so that ACL2 doesn't actually compute big lists of addresses
;For instance, (blk 5 10) does not get expanded to (5 6 7 8 9 10 11 12 13 14) if the executablec-counterpart is disabled.
(in-theory (disable (:executable-counterpart blk)))

(defthm true-listp-blk
  (true-listp (blk base size)))

(defthm true-listp-blk-type-prescription
  (true-listp (blk base size))
  :rule-classes :TYPE-PRESCRIPTION)

(in-theory (disable (:TYPE-PRESCRIPTION BLK))) ;we'll use true-listp-blk-type-prescription instead

(defthm unique-blk
  (unique (blk base size))
  :hints (("goal" :in-theory (enable unique blk))))

(defthm integer-listp-blk
  (integer-listp (blk base size))
  :hints (("Goal" :in-theory (enable blk))))

(defthm null-blk
  (implies (zp max)
           (equal (blk ptr max) nil))
  :hints (("goal" :in-theory (enable blk))))

(defthm consp-blk
  (equal (consp (blk base size))
         (< 0 (ifix size)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-consp-type
  (implies (and (integerp size)
                (< 0 size))
            (consp (blk base size)))
  :rule-classes (:type-prescription))

;make this an equal rule?
(defthm blk-upper-subbagp
  (implies (<= (ifix max1) (ifix max2))
           (subbagp (blk ptr max1)
                    (blk ptr max2)))
  :hints (("Goal" :in-theory (enable blk))))
   
 ;; These should be among the last rules attempted ..

(defthm blk-disjoint-from-blk-1
  (implies (and (<= (+ (ifix rptr) (ifix rsize)) (ifix wptr))
                (<= 0 (ifix rsize))
                (<= 0 (ifix wsize))
                )
           (disjoint (blk rptr rsize)
                     (blk wptr wsize)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-disjoint-from-blk-2
  (implies (and (<= (+ (ifix wptr) (ifix wsize)) (ifix rptr))
                (<= 0 (ifix rsize))
                (<= 0 (ifix wsize))
                )
           (disjoint (blk rptr rsize)
                     (blk wptr wsize)))
  :hints (("Goal" :in-theory (enable blk))))
 
(defthm blk-membership-subbagp
  (implies (and (not (memberp addr (blk ptr size2))) ;size2 is a free variable
                (<= (ifix size1) (ifix size2))
                )
           (equal (memberp addr (blk ptr size1))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-non-membership-less
  (implies (< n (ifix ptr))
           (equal (memberp n (blk ptr size))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-non-membership-more
  (implies (< (+ (ifix ptr) (ifix size)) n)
           (equal (memberp n (blk ptr size))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

;we need the integerp for the same reason as in blk-rec-membership
(defthm blk-membership
  (implies (and (integerp ptr)
                (<= (ifix base) ptr)
                (< ptr (+ (ifix base) (ifix size))))
           (memberp ptr (blk base size)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm disjoint-blk-subbagp-right
  (implies (and (not (disjoint list (blk ptr size0))) ;size0 is a free variable
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint list (blk ptr size1))
                  nil))
  :hints (("Goal" :in-theory (enable blk)))) 
 
(defthm disjoint-blk-subbagp-left
  (implies (and (not (disjoint (blk ptr size0) list)) ;size0 is a free variable
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint (blk ptr size1) list)
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

;;
;; XBLOCK
;;

;; ;bzo do we ever use xblock? 

;; (defun xblock (base size)
;;   (declare (type integer size base))
;;   (if (zerop base) 
;;       nil
;;     (blk base size)))
 
;; (defthm zp-xblock
;;   (implies (zerop base)
;;            (equal (xblock base size)
;;                   nil)))


;;
;; relocate-blk
;;

(defun relocate-blk (off list)
  (declare (type (satisfies integer-listp) list))
  (if (consp list)
      (cons (+ (ifix off) (car list)) (relocate-blk off (cdr list)))
    nil))

(defthm len-of-relocate-blk
  (equal (len (gacc::relocate-blk off list))
         (len list)))

;really do need to know that x and the list are integer based,
; but no longer need y to be an integer
; for these the problem is that +/- treats non-numbers as 0, so
; if x is a non-number, or anything in the list isn't, doesn't hold
(defthm memberp-relocate-blk
  (implies 
   (and
    (integer-listp list)
    (integerp x)
    ) 
   (equal (memberp x (relocate-blk y list))
          (memberp (- x (ifix y)) list)))
  :hints (("Goal" :in-theory (enable LIST::memberp-of-cons))))

;can remove hyp that x is integerp, but still need nice lists
; see comments above for memberp-relocate-blk
(defthm disjoint-relocation
  (implies
   (and
    (integer-listp list1)
    (integer-listp list2)
    )
   (equal (disjoint (relocate-blk x list1)
                    (relocate-blk x list2))
          (disjoint list1 list2)))
  :hints (("Goal" :in-theory (enable LIST::memberp-of-cons
                                     BAG::DISJOINT-OF-CONS-TWO))))

;need the integerp or its just not true always
; see comment for blk-rec-normalization and memberp-relocate-blk
(defthm relocate-blk-rec-offset
  (implies
   (and
    (integerp ptr)
    (integerp x))
   (equal (blk-rec (+ ptr x) off max)
          (relocate-blk x (blk-rec ptr off max))))
  :hints (("Goal" :in-theory (enable blk-rec))))


(defthmd relocate-blk-offset
  (implies
   (and
    (integerp ptr)
    (integerp x))
   (equal (blk (+ x ptr) size)
          (relocate-blk x (blk ptr size))))
  :hints (("goal" :in-theory (enable blk))))

(defmacro implies* (a b)
  `(if ,a ,b t))

;Checks whether LIST is a true-listp of consecutive integers.
;despite the name of this, we define sblkp well before we define sblk.
;perhaps the name should be blkp?
(defund sblkp (list)
  (declare (type t list))
  (if (consp list)
      (let ((x (car list)))
        (and (integerp x)
             (implies* (consp (cdr list))
                       (equal (1+ x) (cadr list)))
             (sblkp (cdr list))))
    (null list)))

(defthm sblkp-blk-rec
  (sblkp (blk-rec base off max))
  :hints (("goal" :in-theory (enable blk-rec sblkp))))

(defun equal-x-blk-rec-induction (x base off max)
  (if (and (consp x)
           (< (ifix off) (ifix max)))
      (equal-x-blk-rec-induction (cdr x) base (1+ (ifix off)) (ifix max))
    (list x base off max)))

(defthm equal-blk-rec-extensionality
  (implies (and (integerp base)
                (integerp max)
                (integerp off)
                (< off max))
           (equal (equal x (blk-rec base off max))
                  (and (sblkp x)
                       (equal (car x) (+ base off))
                       (equal (len x) (- max off)))))
  :hints (("goal" :induct (equal-x-blk-rec-induction x base off max)
           :in-theory (enable sblkp len blk-rec open-blk-rec ;fix-size
                              ))))



;add to gacc, or is something like this already there?
(defthm sblkp-of-relocate-blk
  (implies (gacc::sblkp list)
           (gacc::sblkp (gacc::relocate-blk off list)))
  :hints (("Goal" :in-theory (enable  gacc::relocate-blk gacc::sblkp))))


;add to gacc, or is something like this already there?
(defthm car-of-relocate-blk
  (equal (car (gacc::relocate-blk off list))
         (if (consp list)
             (+ (ifix off) (car list))
           nil))
  :hints (("Goal" :in-theory (enable  gacc::relocate-blk gacc::sblkp))))

(defthmd blk-rec-normalize
  (IMPLIES (AND (case-split (INTEGERP SIZE))
;                (case-split (< 0 SIZE))
                (case-split (integerp base))
                (case-split (integerp e))
                (case-split (integerp off))
                )
           (EQUAL (GACC::BLK-REC base (+ e off) (+ e SIZE))
                  (GACC::BLK-REC (+ e base) off SIZE)))
  :hints (("Goal" ;:induct (ADDR-RANGE BASE SIZE)
           :in-theory (enable gacc::blk-rec))))

;looped
(defthmd blk-rec-normalize-to-0-offset
  (IMPLIES (AND (syntaxp (not (and (quotep off) (equal off ''0)))) ;prevents loops
                (case-split (INTEGERP SIZE))
;                (case-split (< 0 SIZE))
                (case-split (integerp base))
                (case-split (integerp off))
                )
           (EQUAL (GACC::BLK-REC base off size)
                  (GACC::BLK-REC (+ base off) 0 (- SIZE off))))
  :hints (("Goal" :use (:instance blk-rec-normalize (base base) (off 0) (size (- SIZE off)) (e off)))))


;bzo make nicer?
(defthm cdr-of-blk-rec
  (equal (cdr (gacc::blk-rec base off max))
         (if (<= (ifix max) (ifix off))
             nil
           (gacc::blk-rec base (+ 1 (ifix off)) max)))
  :hints (("Goal" :expand ( (gacc::blk-rec base off max)
                            (gacc::blk-rec (+ 1 base) off max))
           :in-theory (enable ;acl2::cons-equal-rewrite ;bzo
                              ifix
                              gacc::blk-rec))))

(defthm blk-when-size-is-1
  (equal (GACC::BLK PTR 1)
         (list (ifix ptr)))
  :hints (("Goal" :in-theory (enable gacc::blk)))
  )
