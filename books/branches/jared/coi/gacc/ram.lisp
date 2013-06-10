#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

(include-book "ram0")
(include-book "block")

(include-book "../bags/two-level-meta") ;we need this, because of mentions of "flat below"; move that stuff to a different book?

(local (include-book "rtl/rel4/arithmetic/fl" :dir :system))

;(local (include-book "../super-ihs/loglist")) ;bzo
(local (include-book "../super-ihs/super-ihs")) ;bzo

;;
;;
;; FIX-SIZE
;;
;;

(defund fix-size (size)
  (declare (type t size))
  (let ((size (nfix size)))
    (if (<= size (word-size))
        (word-size)
      (+ (word-size) (fix-size (- size (word-size)))))))

(defthm fix-size-fix-size
  (equal (fix-size (fix-size size))
         (fix-size size))
  :hints (("Goal" :in-theory (enable fix-size))))

(defthm max-offset-fix-size
  (equal (max-offset (fix-size size))
         (max-offset size))
  :hints (("Goal" :in-theory (enable max-offset fix-size))))

(defthm fix-size-+8
  (implies (and (integerp v)
                (< 0 v))
           (equal (fix-size (+ 8 v))
                  (+ 8 (fix-size v))))
  :hints (("Goal" :in-theory (enable fix-size))))

;this seems odd -why have 2 lower bounds?  make a linear rule?
(defthm fix-size-magnitude
  (and (<= 8 (fix-size s))
       (< 0 (fix-size s)))
  :hints (("Goal" :in-theory (enable fix-size))))

(defthm negative-fix-size
  (implies (<= size 0)
           (equal (fix-size size) 
                  8))
  :hints (("Goal" :in-theory (enable fix-size))))

(defthm fix-size-bound
  (implies (integerp sz)
           (<= sz (fix-size sz)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fix-size))))

;bzo move and generalize!
(defthm integerp-of-one-eighth
  (implies (not (integerp size))
           (equal (integerp (* 1/8 size))
                  (not (acl2-numberp size))))
  :hints (("Goal" :use (:instance ACL2::INTEGERP-+-MINUS-* (acl2::i 8) (acl2::j (* 1/8 size))))))


;bzo
(defthm one-eighth-rule-2
  (implies (and (integerp (* 1/8 size))
                (acl2-numberp size))
           (integerp size))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:instance ACL2::INTEGERP-+-MINUS-* (acl2::i 8) (acl2::j (* 1/8 size))))))

;bzo
(defthm one-eighth-rule-3
  (implies (and (multiple-of-8 size)
                (acl2-numberp size))
           (integerp size))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable multiple-of-8))))
 
(defthm fix-size-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (fix-size size)
                  (word-size)))
  :hints (("goal" :in-theory (enable fix-size))))


;fix-size rounds its argument up to the next multiple of 8.
(defthmd fix-size-rewrite
  (equal (fix-size size)
         (if (zp size)
             8
           (* 8 (+ 1 (floor (+ -1 size) 8)))
           ))
  :hints (("Goal" :in-theory (e/d (max-offset ;floor 
                                   FIX-SIZE
                                   ) 
                                  ( ;UNFIXED-SIZE-MAX-OFFSET ;looped
                                   ))
           :do-not '(generalize eliminate-destructors))))


;bzo
(defthm multiple-of-8-of-fix-size
  (multiple-of-8 (fix-size size))
  :hints (("Goal" :in-theory (enable multiple-of-8 fix-size))))

(defthm fix-size-when-multiple-of-8
  (implies (multiple-of-8 size)
           (equal (fix-size size)
                  (if (< 0 size)
                      size
                    8)))
  :hints (("Goal" :in-theory (enable multiple-of-8 fix-size-rewrite))))


(defun syntax-unfixed-size (size)
  (declare (type t size) (xargs :guard-hints (("Goal" :in-theory (enable quotep)))))
  (if (and (quotep size)
           (consp (cdr size)))
      (or (equal (nfix (cadr size)) 0)
          (not (equal (mod (nfix (cadr size)) (word-size)) 0)))
    (not (and (consp size) (equal (car size) 'fix-size)))))


(defthm maxoffset-recollapse-to-fix-size
  (equal (+ 8 (* 8 (max-offset size)))
         (fix-size size))
  :hints (("Goal" :in-theory (enable fix-size))))

;;
;;
;; sblk
;;
;;

(include-book "addr-range")

;bzo order of args doesn't match blk
;return a list of word addresses which starts at PTR and which is long enough to represent SIZE bits
;always returns a cons, since if SIZE is 0, it still returns (0).
(defund sblk (size ptr)
  (declare (type t size ptr))
  (blk ptr (1+ (max-offset size)))
;;  (gacc::addr-range ptr (1+ (MAX-OFFSET SIZE))) ;;trying this equivalent definition...
  )

(defthm consp-sblk
  (and (sblk size ptr) ;do we need this?
       (consp (sblk size ptr)))
  :hints (("goal" :in-theory (enable sblk blk ifix)
           :expand (:free (base max) (blk-rec base 0 max))
           )))

(defthm sblk-type-prescription
  (and (consp (sblk size ptr))
       (true-listp (sblk size ptr)))
  :rule-classes ((:type-prescription)))

(defthm true-listp-sblk
  (true-listp (sblk size ptr))
  :hints (("goal" :in-theory (enable sblk))))

(defthm sblk-when-size-is-not-an-integerp
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
;(syntaxp (not (quotep n)))
            (not (integerp size)))
           (equal (sblk size ptr)
                  (sblk 0 ptr)))
  :hints (("goal" :in-theory (enable sblk))))

(defthm sblk-when-size-is-not-positive
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
; (syntaxp (not (quotep n)))
            (<= size 0) ;(not (equal n (nfix n)))
            )
           (equal (sblk size ptr)
                  (sblk 0 ptr)))
  :hints (("goal" :in-theory (enable sblk))))

(defthm car-sblk
  (equal (car (sblk size ptr))
         (ifix ptr))
  :hints (("goal" :in-theory (enable sblk blk ifix)
           :expand (:free (base max) (blk-rec base 0 max))
           )))

(defthm len-sblk
  (equal (len (sblk size ptr))
         (1+ (max-offset size)))
  :hints (("goal" :in-theory (enable ifix sblk blk))))

(defthm sblk-linear-disjointness
  (and (implies (<= (+ (ifix rptr) (1+ (max-offset rsize))) (ifix wptr))
                (disjoint (sblk rsize rptr) (sblk wsize wptr)))
       (implies (<= (+ (ifix wptr) (1+ (max-offset wsize))) (ifix rptr))
                (disjoint (sblk rsize rptr) (sblk wsize wptr))))
  :hints (("goal" :in-theory (enable sblk 
                                     blk-disjoint-from-blk-1
                                     blk-disjoint-from-blk-2))))

(defthm unique-sblk
  (unique (sblk size ptr))
  :hints (("goal" :in-theory (enable sblk))))

(defthm integer-listp-sblk
  (integer-listp (sblk size ptr))
  :hints (("goal" :in-theory (enable sblk))))



(encapsulate 
 ()
 (local (defun offset-equal-induction (s1 s2)
          (declare (xargs :measure (max (nfix s1) (nfix s2))))
          (let ((s1 (nfix s1))
                (s2 (nfix s2)))
            (if (and (<= s1 (word-size))
                     (<= s2 (word-size))) nil
              (cons (list s1 s2)
                    (offset-equal-induction (- s1 (word-size))
                                            (- s2 (word-size))))))))

 (defthm max-offset-to-fix-size
   (equal (equal (max-offset s1) (max-offset s2))
          (equal (fix-size s1) (fix-size s2)))
   :hints (("goal" :in-theory (enable max-offset fix-size)
            :induct (offset-equal-induction s1 s2))))

)

(defthmd max-offset-to-fix-size-rev
  (equal (equal (fix-size s1) (fix-size s2))
         (equal (max-offset s1) (max-offset s2))))




(defthm equal-sblk-to-equal-args
  (equal (equal (sblk s1 o1) (sblk s2 o2))
         (and (equal (fix-size s1)
                     (fix-size s2))
              (equal (ifix o1)
                     (ifix o2))))
  :otf-flg t
  :hints (("goal" :cases ((iff (integerp o1) (integerp o2)))
           :in-theory (e/d (;ifix
                            max-offset-to-fix-size-rev
                              blk 
                              sblk 
                              fix-size
                              ) 
                           (;BLK-REC-NON-INTEGER-PTR
                             max-offset-to-fix-size
                            )))))

(defthm sblkp-of-singleton
  (equal (sblkp (cons a nil))
         (integerp a))
  :hints (("Goal" :in-theory (enable sblkp))))

(defthm sblkp-of-addr-range
  (gacc::sblkp (gacc::addr-range base k))
  :hints (("Goal" :in-theory (enable gacc::addr-range gacc::sblkp))))

(defthm sblkp-sblk
  (sblkp (sblk size off))
  :hints (("goal" :in-theory (enable sblk blk))))

(defthmd sblk-8-rewrite
  (equal (sblk 8 addr)
         (list (ifix addr)))
  :hints (("Goal" :in-theory (enable sblk blk
                                     open-blk-rec
                                     ))))



(defthm sblk-when-size-is-0
  (equal (GACC::SBLK 0 PTR)
         (list (ifix ptr)))
  :hints (("Goal" :in-theory (enable gacc::sblk))))

(defthm sblk-when-size-is-1
  (equal (GACC::SBLK 1 PTR)
         (list (ifix ptr)))
  :hints (("Goal" :in-theory (enable gacc::sblk))))

;bzo


;bzo gen!
(defthmd blk-rec-goes-to-addr-range
  (IMPLIES (AND (case-split (INTEGERP SIZE))
                (case-split (< 0 SIZE))
                (case-split (integerp base))
                )
           (EQUAL (GACC::BLK-REC base 0 SIZE)
                  (GACC::ADDR-RANGE base SIZE)))
  :hints (("Goal" ;:induct (GACC::ADDR-RANGE BASE SIZE)
           :in-theory (enable gacc::sblkp))))

(defthmd sblk-as-addr-range
  (implies (and (case-split (integerp size))
                (case-split (< 0 size))
                (case-split (gacc::multiple-of-8 size)))
           (equal (gacc::sblk size x)
                  (gacc::addr-range (ifix x) (/ size 8))))
  :hints (("Goal" :in-theory (enable blk-rec-goes-to-addr-range gacc::sblk gacc::blk))))

;only works when offse is 0?
(defthmd blk-rec-goes-to-addr-range2
  (equal (gacc::blk-rec base 0 size)
         (gacc::addr-range base size))
  :hints (("Goal" ;:induct (gacc::addr-range base size)
           :in-theory (enable  blk-rec-goes-to-addr-range))))

(defthmd sblk-becomes-addr-range
  (equal (gacc::sblk size x)
         (gacc::addr-range x (1+ (MAX-OFFSET SIZE))))
  :hints (("Goal" :expand ((MAX-OFFSET SIZE)
                           (FIX-SIZE SIZE))
           :in-theory (enable blk-rec-goes-to-addr-range2 sblk-as-addr-range gacc::sblk gacc::blk))))


;;
;; lemmas about rd, wr, rx-rec, and wx-rec
;;


(defthm rx-rec-wr-non-memberp
  (implies (not (memberp x (blk-rec ptr off size)))
           (equal (rx-rec ptr off size (wr x val ram))
                  (rx-rec ptr off size ram)))
  :hints (("goal" :expand ( (RX-REC PTR 0 SIZE (WR X VAL RAM))
                             (RX-REC PTR 0 SIZE RAM))
           :in-theory (enable rx-rec blk-rec))))

(defthm rx-rec-clr-non-memberp
  (implies (not (memberp x (blk-rec ptr off size)))
           (equal (rx-rec ptr off size (memory-clr x ram))
                  (rx-rec ptr off size ram)))
  :hints (("goal" :in-theory (enable memory-clr))))
 
(defthm rd-over-wx-rec
  (implies
   (and
    (not (memberp rptr (blk-rec wptr woff bwmax)))
    (<= (ifix wmax) (ifix bwmax))
    (<= 0 (ifix woff))
    (<= 0 (ifix wmax))
    )
   (equal (rd rptr (wx-rec wptr woff wmax value ram))
          (rd rptr ram)))
  :hints (("goal" :in-theory (enable wx-rec blk-rec)
           :induct (WX-REC WPTR WOFF WMAX VALUE RAM)
           :expand ((WX-REC WPTR WOFF WMAX VALUE RAM)))))

(defthm rd-over-wx-rec-instance
  (implies
   (and
    (not (memberp rptr (blk-rec wptr woff wmax)))
    (<= 0 (ifix woff))
    (<= 0 (ifix wmax))
    )
   (equal (rd rptr (wx-rec wptr woff wmax value ram))
          (rd rptr ram)))
  :hints (("Goal" :in-theory (enable wx-rec))))

(defthm rx-rec-over-wr
  (implies
   (and
    (not (memberp wptr (blk-rec rptr roff brmax)))
    (<= (ifix rmax) (ifix brmax))
    (<= 0 (ifix rmax))
    (<= 0 (ifix roff))
    )
   (equal (rx-rec rptr roff rmax (wr wptr value ram))
          (rx-rec rptr roff rmax ram)))
  :hints (("Goal" :in-theory (enable rx-rec blk-rec))))

(defthm rx-rec-over-wr-instance
  (implies
   (and
    (not (memberp wptr (blk-rec rptr roff rmax)))
    (<= 0 (ifix rmax))
    (<= 0 (ifix roff))
    )
   (equal (rx-rec rptr roff rmax (wr wptr value ram))
          (rx-rec rptr roff rmax ram))))

(encapsulate
 ()
 (local (defthmd rx-rec-over-wx-rec-lemma
          (implies (and (disjoint (blk-rec rptr roff brmax)
                                  (blk-rec wptr woff bwmax))
                        (<= (ifix rmax) (ifix brmax))
                        (<= (ifix wmax) (ifix bwmax))
                        (<= 0 (ifix roff))
                        (<= 0 (ifix rmax))
                        (integerp woff)
                        (<= 0 (ifix woff))
                        (<= 0 (ifix wmax))
                        )
                   (equal (rx-rec rptr roff rmax (wx-rec wptr woff wmax value ram))
                          (rx-rec rptr roff rmax ram)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable wx-rec
                                      rx-rec
                                      blk-rec
                                      bag::DISJOINT-of-CONS-two ;bzo
                                      )))))

 (defthm rx-rec-over-wx-rec
   (implies
    (and
     (disjoint (blk-rec rptr roff brmax)
               (blk-rec wptr woff bwmax))
     (<= (ifix rmax) (ifix brmax))
     (<= (ifix wmax) (ifix bwmax))
     (<= 0 (ifix roff))
     (<= 0 (ifix rmax))
     (<= 0 (ifix woff))
     (<= 0 (ifix wmax))
     )
    (equal (rx-rec rptr roff rmax (wx-rec wptr woff wmax value ram))
           (rx-rec rptr roff rmax ram)))
   :hints (("goal" :in-theory (enable wx-rec)
            :use ((:instance rx-rec-over-wx-rec-lemma (woff (ifix woff))))))))

(encapsulate
 ()
 (local (defthm rx-rec-of-wx-rec-lemma
          (implies
           (and
            (equal wptr rptr)
            (equal woff roff)
            (equal wmax rmax)
            (integerp roff)
            (integerp rmax)
            (<= 0 roff)
            (<= roff rmax)
            )
           (equal (rx-rec rptr roff rmax (wx-rec wptr woff wmax value ram))
                  (;wfixw 8 (- rmax roff)
                   acl2::loghead (* 8 (nfix (- rmax roff)))
                   value)))
          :hints (("Goal" :in-theory (enable wx-rec rx-rec ;wfixw ;wcar
                                             )))))

 (defthm rx-rec-of-wx-rec
   (implies
    (and
     (equal wptr rptr)
     (equal woff roff)
     (equal wmax rmax)
     (<= 0 (ifix roff))
     (<= (ifix roff) (ifix rmax))
     )
    (equal (rx-rec rptr roff rmax (wx-rec wptr woff wmax value ram))
           (;wfixw 8 (- (ifix rmax) (ifix roff))
            acl2::loghead (* 8 (nfix (- (ifix rmax) (ifix roff))))
            value)))
   :hints (("goal" :in-theory (enable rx-rec ;bzo
                                      )
            :cases ((not (integerp roff)))))))

(encapsulate
 ()
 (local (defthm wx-rec-of-rx-rec-lemma
          (implies
           (and
            (integerp woff)
            (<= 0 (ifix woff))
            (< 0 (ifix wmax))
            (<= (ifix woff) (ifix wmax))
            (equal value (rx-rec wptr woff wmax ram))
            )
           (equal (wx-rec wptr woff wmax value ram)
                  ram))
          :hints (("Goal" :in-theory (enable wx-rec rx-rec)))))

 (defthm wx-rec-of-rx-rec
   (implies
    (and (equal value (rx-rec wptr woff wmax ram))
         (<= 0 (ifix woff))
         (< 0 (ifix wmax))
         (<= (ifix woff) (ifix wmax))
         )
    (equal (wx-rec wptr woff wmax value ram)
           ram))
   :hints (("goal" :cases ((not (integerp woff)))))))


(encapsulate
 ()
 (local (defthm wr-over-wx-rec-lemma
          (implies
           (and
            (not (memberp a (blk-rec wptr woff bwmax)))
            (<= (ifix wmax) (ifix bwmax))
            (integerp wptr)
            (<= 0 (ifix woff))
            (<= 0 (ifix wmax))
            )
           (equal (wx-rec wptr woff wmax value (wr a v ram))
                  (wr a v (wx-rec wptr woff wmax value ram))))
          :hints (("Goal" :in-theory (enable wx-rec blk-rec)
                   :induct (wx-rec wptr woff wmax value ram)))))

 (defthm wr-over-wx-rec
   (implies
    (and
     (not (memberp a (blk-rec wptr woff bwmax)))
     (<= (ifix wmax) (ifix bwmax))
     (<= 0 (ifix woff))
     (<= 0 (ifix wmax))
     )
    (equal (wx-rec wptr woff wmax value (wr a v ram))
           (wr a v (wx-rec wptr woff wmax value ram))))
   :hints (("Goal" :in-theory (enable wx-rec)
            :cases ((not (integerp wptr)))))))

(defthm wr-over-wx-rec-instance
  (implies
   (and
    (not (memberp a (blk-rec wptr woff wmax)))
    (<= 0 woff)
    (<= 0 wmax)
    )
   (equal (wx-rec wptr woff wmax value (wr a v ram))
          (wr a v (wx-rec wptr woff wmax value ram)))))

(defthm wx-rec-of-wx-rec
  (implies
   (and
    (equal wptr ptr)
    (equal woff off)
    (equal wmax max)
    (<= 0 off)
    (<= off max)
    )
   (equal (wx-rec ptr off max value (wx-rec wptr woff wmax wvalue ram))
          (wx-rec ptr off max value ram)))
  :hints (("Goal" :in-theory (enable wx-rec))))


(encapsulate
 ()
 (local (defthmd wx-rec-over-wx-rec-lemma
          (implies
           (and
            (disjoint (blk-rec ptr   off bmax)
                      (blk-rec wptr woff bwmax))
            (<= (ifix max) (ifix bmax))
            (<= (ifix wmax) (ifix bwmax))
            (<= 0 (ifix off))
            (<= 0 (ifix max))
            (integerp woff)
            (<= 0 (ifix woff))
            (<= 0 (ifix wmax))
            )
           (equal (wx-rec ptr off max value (wx-rec wptr woff wmax wvalue ram))
                  (wx-rec wptr woff wmax wvalue (wx-rec ptr off max value ram))))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable bag::disjoint-of-cons-one ; bzo
                                      wx-rec
                                      blk-rec
                                      bag::DISJOINT-of-CONS-two ; bzo
                                      )
                   :do-not-induct t
                   :induct (wx-rec ptr off max value ram)))))

 (defthm wx-rec-over-wx-rec
   (implies
    (and
     (disjoint (blk-rec ptr   off bmax)
               (blk-rec wptr woff bwmax))
     (<= (ifix max) (ifix bmax))
     (<= (ifix wmax) (ifix bwmax))
     (<= 0 (ifix off))
     (<= 0 (ifix max))
     (<= 0 (ifix woff))
     (<= 0 (ifix wmax))
     )
    (equal (wx-rec ptr off max value (wx-rec wptr woff wmax wvalue ram))
           (wx-rec wptr woff wmax wvalue (wx-rec ptr off max value ram))))
   :hints (("Goal" :in-theory (enable wx-rec)
            :use ((:instance wx-rec-over-wx-rec-lemma (woff (ifix woff))))
            ))
   :rule-classes ((:rewrite :loop-stopper ((wptr ptr wx-rec))))
   ))




(defthm wx-rec-over-wx-rec-instance
  (implies
   (and
    (disjoint (blk-rec ptr   off max)
              (blk-rec wptr woff wmax))
    (<= 0 off)
    (<= 0 max)
    (<= 0 woff)
    (<= 0 wmax)
    )
   (equal (wx-rec ptr off max value (wx-rec wptr woff wmax wvalue ram))
          (wx-rec wptr woff wmax wvalue (wx-rec ptr off max value ram))))
  :rule-classes ((:rewrite :loop-stopper ((wptr ptr wx-rec)))))

;make this an equal rule?
(defthmd ram==wx-rec
  (implies (and (equal ram2 ram1)
                (equal (;wfixw 8 (- max (ifix off))
                        acl2::loghead (* 8 (nfix  (- max (ifix off))))
                        value)
                       (rx-rec ptr off max ram1))
                (<= 0 (ifix off))
                (<= (ifix off) (ifix max))
                )
           (equal (equal ram1 (wx-rec ptr off max value ram2)) 
                  t))
  :hints (("Goal" :in-theory (enable wx-rec rx-rec ;open-wfixw ;wcar wcons wcdr
                                     )
           :induct (wx-rec ptr off max value ram2))))

(encapsulate
 ()
 (local (defthm wx-rec==wx-rec-lemma
          (implies
           (and
            (equal ptr1 ptr2)
            (equal off1 off2)
            (equal max1 max2)
            (equal (;wfixw 8 (- (ifix max2) (ifix off2))
                    acl2::loghead (* 8 (nfix (- (ifix max2) (ifix off2))))
                                  value1)
                   (;wfixw 8 (- (ifix max2) (ifix off2))
                    acl2::loghead (* 8 (nfix (- (ifix max2) (ifix off2))))
                                  value2))
            (equal ram1 ram2)
            (integerp off2)
            (<= 0 (ifix off2))
            (<= (ifix off2) (ifix max2))
            )
           (equal (equal (wx-rec ptr1 off1 max1 value1 ram1) (wx-rec ptr2 off2 max2 value2 ram2))
                  t))
          :hints (("Goal" :in-theory (e/d (wx-rec ;open-wfixw
                                                  ) (;WFIXW-REDUCTION ;bzo
                                                               ))))))

 (defthmd wx-rec==wx-rec
   (implies
    (and
     (equal ptr1 ptr2)
     (equal off1 off2)
     (equal max1 max2)
     (equal (;wfixw 8 (- (ifix max2) (ifix off2))
             acl2::loghead (* 8 (nfix (- (ifix max2) (ifix off2))))
                           value1)
            (;wfixw 8 (- (ifix max2) (ifix off2))
             acl2::loghead (* 8 (nfix (- (ifix max2) (ifix off2))))                   
                           value2))
     (equal ram1 ram2)
     (<= 0 (ifix off2))
     (<= (ifix off2) (ifix max2))
     )
    (equal (equal (wx-rec ptr1 off1 max1 value1 ram1) (wx-rec ptr2 off2 max2 value2 ram2))
           t))
   :hints (("Goal" :in-theory (disable ;WFIXW-REDUCTION
                                       )
            :cases ((not (integerp off2)))))))


(include-book "list-ops") ;bzo move up?

; trying with this disabled.
(defthmd rx-rec-to-rd-list-reduction
  (implies (and (integerp roff)
                (integerp rmax)
                (<= 0 roff)
                (<= roff rmax)
                )
           (equal (rx-rec base roff rmax ram)
                  (wintlist (rd-list (blk-rec base roff rmax) ram))))
  :hints (("goal" :in-theory (enable rx-rec
                                     blk-rec
                                     ))))

; trying with this disabled.
(defthmd wx-rec-to-wr-list-reduction
  (implies (and (integerp woff)
                (integerp wmax)
                (<= 0 woff)
                (<= woff wmax)
                )
           (equal (wx-rec base woff wmax value ram)
                  (wr-list (blk-rec base woff wmax) 
                           (enlistw (- wmax woff) value) ram)))
  :hints (("goal" :induct (wx-rec base woff wmax value ram)
           :in-theory (e/d (wx-rec
                            blk-rec
                            open-blk-rec
                            wr-list
			    gacc::wr==wr
			    GACC::MEMORY-CLR-DIFFERENTIAL 
                                        ;open-wx-rec
                            )
                           (wr==r!
                            ENLISTW-OF-0;bzo
                            )))))



;;
;; Z*-rec
;;

;Eric isn't thrilled by this name...

(defmacro z*-rec (list ram)
  `(clr-list ,list ,ram))

(table macro-aliases-table 'z*-rec 'clr-list)

#+joe
(defun z*-rec (list ram)
  ;(declare (type t list ram))
  (if (consp list)
      (let ((ram (memory-clr (car list) ram)))
        (z*-rec (cdr list) ram))
    ram))

(defthm z*-rec-over-append
  (equal (z*-rec (append x y) ram)
         (z*-rec x (z*-rec y ram)))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr append))))

;odd way to phrase this?
(defthm z*-rec-commutativity
  (equal (equal (z*-rec x (z*-rec y ram)) (z*-rec y (z*-rec x ram)))
         t)
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr))))


(defthmd wr==ram 
  (equal (equal (wr a (loghead8 v) ram1) ram2) 
         (and (equal (loghead8 v) (rd a ram2)) 
              (equal (z*-rec `(,a) ram1) 
                     (z*-rec `(,a) ram2))))
  :hints (("Goal" :in-theory (enable wr==r!))))
 

(defun z*-rec-induction (a list ram1 ram2 v) 
  (if (consp list) 
      (z*-rec-induction a (cdr list) (memory-clr (car list) ram1) 
                        (memory-clr (car list) ram2) v) 
    (equal (equal a ram1) (equal ram2 v))))

(defthm z*-rec-of-wr
  (implies (not (memberp a list))
           (equal (equal (z*-rec list (wr a (loghead8 v) ram1)) 
                         (z*-rec list ram2)) 
                  (and (equal (loghead8 v) (rd a ram2)) 
                       (equal (z*-rec (cons a list) ram1) 
                              (z*-rec (cons a list) ram2))))) 
  :hints (("goal" :in-theory (enable 
                              wr==r!
                              memberp ;bzo
                              )
           :do-not '(generalize eliminate-destructors)
           :induct (z*-rec-induction a list ram1 ram2 v))))
 
(defthm z*-rec-over-wr  
  (implies (memberp a list) 
           (equal (equal (z*-rec list (wr a v ram1)) 
                         (z*-rec list ram2)) 
                  (equal (z*-rec list ram1) 
                         (z*-rec list ram2))))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable 
;memberp ;bzo
                       ))
          ("Subgoal *1/1" :cases ((equal (car list) a)))))



(defthm rx-rec-over-z*-rec-disjoint
  (implies (disjoint (blk-rec ptr off size) list)
           (equal (rx-rec ptr off size (z*-rec list ram))
                  (rx-rec ptr off size ram))))
                                           

;stringe rule...
(defthm equality-implies-equal-reads
  (implies (equal (z*-rec list (wx-rec ptr off size value ram1))
                  (z*-rec list ram2))
           (equal (rx-rec ptr off size (z*-rec list (wx-rec ptr off size value ram1)))
                  (rx-rec ptr off size (z*-rec list ram2)))))


;;
;; RX/WX Rules
;;


(defun ram==wx-hyp (size ptr value ram)
  (declare (type t size ptr value ram))
  (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                (ifix value) ;drop the ifix once loghead's guards are weakened
                )
         (rx size ptr ram)))

;tests whether the nest of calls to wx which make up RAM includes a call to wx
;with arguments of SIZE and PTR?
;;
(defun wx-instance (size ptr ram)
  (declare (type t size ptr ram))
  (if (and (consp ram)
           (equal (car ram) 'wx) ; (wx size ptr value ram)
           (consp (cdr ram))
           (consp (cddr ram))
           (consp (cdddr ram))
           (consp (cddddr ram)))
      (if (and (equal ptr  (caddr ram))
               (equal size (cadr ram)))
          t
        (wx-instance size ptr (caddddr ram)))
    nil))

;not enabled outside of this book
(defthmd ram==wx
  (implies (and (syntaxp (not (wx-instance size ptr ram1)))
                (ram==wx-hyp size ptr value ram1)
                (equal ram2 ram1)
                )
           (equal (equal ram1 (wx size ptr value ram2))
                  t))
  :hints (("Goal" :in-theory (e/d (rx wx
                                      RAM==WX-REC
                                      ram==wx-rec) 
                                  ( ;WFIXN-REWRITE-TO-LOGHEAD ;why
                                   MAX-OFFSET
                                   )))))

;drop the ifixes when loghead's guard improves? -ews
;why do we have a separate function for this?
(defun wx==wx-hyp (size value1 value2)
  (declare (type t size value1 value2))
  (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                (ifix value1)
                )
         (acl2::loghead (fix-size size) ;wfixn 8 size 
                (ifix value2)
                )))

;(in-theory (disable (wx==wx-hyp))) ; because of encapsulated functions

;not enabled outside of this book?
(defthmd wx==wx
  (implies (and (equal addr1 addr2)
                (equal size1 size2)
                (wx==wx-hyp size2 value1 value2)
                (equal ram1 ram2))
           (equal (equal (wx size1 addr1 value1 ram1) 
                         (wx size2 addr2 value2 ram2))
                  t))
  :hints (("Goal" :cases ((integerp value1))
           :in-theory (enable wx wx-rec==wx-rec))))

;exported?
(defthm rx-of-wx
  (implies (and (equal wptr rptr)
                (equal wsize rsize)
                )
           (equal (rx rsize rptr (wx wsize wptr value ram))
                  (acl2::loghead (fix-size rsize) ;wfixn 8 rsize 
                                 value)))
  :hints (("Goal" :in-theory (enable rx wx))))

;exported?
(defthm wx-of-wx
  (implies (and (equal wptr ptr)
                (equal wsize size)
                )
           (equal (wx size ptr value (wx wsize wptr wvalue ram))
                  (wx size ptr value ram)))
  :hints (("Goal" :in-theory (enable wx))))

;; wx-of-rx is probably pretty expensive .. if we need this fact, I
;; think we will get it from backchaining on state equality.
;exported?
(defthmd wx-of-rx
  (implies (equal (acl2::loghead (fix-size wsize) value) (rx wsize wptr ram))
           (equal (wx wsize wptr value ram)
                  ram))
  :hints (("Goal" :cases ((integerp value))
           :in-theory (enable wx rx ram==wx-rec))))


;move this stuff?


;bzo can loop!
(defthmd unfixed-size-rx-back
  (implies (syntaxp (syntax-unfixed-size rsize))
           (equal (rx (fix-size rsize) rptr ram)
                  (rx rsize rptr ram)))
  :hints (("goal" :in-theory (enable rx))))

(defthm acl2::unsigned-byte-p-of-rx-hack
  (acl2::unsigned-byte-p (fix-size size) (rx size a ram))
  :hints (("Goal" :in-theory (e/d ( unfixed-size-rx-back) (unsigned-byte-p-of-rx))
           :use (:instance unsigned-byte-p-of-rx (a a)
                           (ram ram)
                           (size  (fix-size size))
                           (size1 (fix-size size)))
           :do-not '(generalize eliminate-destructors))))

;exported?
(defthm unsigned-byte-p-of-rx-better
  (implies (<= (fix-size size2) size1)
           (equal (acl2::unsigned-byte-p size1 (rx size2 a ram))
                  (integerp size1)))
  :hints (("Goal" :in-theory (e/d (rx) ( ;MAX-OFFSET-WHEN-MULTIPLE-OF-8
;                                        RX-REC-TO-RD-LIST-REDUCTION
                                        )))))

;do we want this?  see loghead-identity
(defthm loghead-of-rx
  (implies (<= (fix-size size2) size1)
           (equal (acl2::loghead size1 (rx size2 ad ram))
                  (if (integerp size1)
                      (rx size2 ad ram)
                    0))))

;exported?
;Matches less often (because ram appears twice, but maybe this is enough for most cases?
(defthm wx-of-rx-cheap
  (equal (wx size ptr (rx size ptr ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable wx-of-rx))))

;exported?
(defthm wx-over-wx
  (implies (disjoint (sblk size  ptr)
                     (sblk wsize wptr))
           (equal (wx size ptr value (wx wsize wptr wvalue ram))
                  (wx wsize wptr wvalue (wx size ptr value ram))))
  :rule-classes ((:rewrite :loop-stopper ((wptr ptr wx))))
  :hints (("goal" :in-theory (enable wx
                                     sblk blk 
                                     ))))

;exported?
(defthm rx-over-wx
  (implies (disjoint (sblk rsize rptr)
                     (sblk wsize wptr))
           (equal (rx rsize rptr (wx wsize wptr value ram))
                  (rx rsize rptr ram)))
  :hints (("goal" :in-theory (enable sblk blk 
                                     rx wx
                                     ))))

;;
;; lemmas about z*-rec together with wx/rx
;;

;where should this go?
(defthm z*-rec-wr
  (implies (not (memberp woff list))
           (equal (z*-rec list (wr woff value ram))
                  (wr woff value (z*-rec list ram)))))

;where should this go?
(defthm z*-rec-blk-rec-of-wr
  (implies (< woff (+ (ifix off) (ifix ptr)))
           (equal (z*-rec (blk-rec ptr off size) (wr woff value ram1))
                  (wr woff value (z*-rec (blk-rec ptr off size) ram1)))))
;move
;not actually a linear rule...
(defthm wr-wx-rec-linear-not-memberp
  (implies (< woff (+ (ifix off) (ifix ptr)))
           (equal (wx-rec ptr off size val1
                          (wr woff val2 ram))
                  (wr woff val2 
                      (wx-rec ptr off size val1 ram))))
  :hints (("Goal" :in-theory (enable wx-rec)
           :induct (wx-rec ptr off size val1
                           (wr woff val2 ram)))))

;move?
(defthmd open-wx-rec
  (and (implies (> (ifix max) (ifix off))
                (equal (wx-rec base off max value ram)
                       (let ((off (ifix off)) 
                             (max (ifix max)))
                         (let ((ram (wx-rec (ifix base) (1+ off) max (acl2::logtail 8 (ifix value)) ram)))
                           (wr (+ off (ifix base))
                               (acl2::loghead 8 (ifix value))
                               ram)))))
       (implies (<= (ifix max) (ifix off))
                (equal (wx-rec base off max value ram) ram)))
  :hints (("goal" :in-theory '(wx-rec))))

;move?
(defthmd open-rx-rec
  (and (implies (> (ifix max) (ifix off))
                (equal (rx-rec base off max ram)
                       (let ((off (ifix off)) 
                             (max (ifix max)))
                         (let ((v (rd (+ off (ifix base)) ram)))
                           (acl2::logapp ;wcons 
                            8 v
                                  (rx-rec (ifix base)
                                          (1+ off)
                                          max ram))))))
       (implies (<= (ifix max) (ifix off))
                (equal (rx-rec base off max ram) 0)))
  :hints (("goal" :in-theory '(rx-rec))))


(defun wx==ram-induction-8 (off ptr ram1 size value)
  (declare (xargs :measure (nfix (- (ifix size) (ifix off)))))
  (if (< (ifix off) (ifix size))
      (wx==ram-induction-8 (+ 1 (ifix off)) (ifix ptr) 
                         (wr (+ (ifix off) (ifix ptr)) (acl2::loghead ;wcar 
                                                        8 value) ram1) 
                         (ifix size) (acl2::logtail ;wcdr 
                                      8 value))
    (equal ptr (equal ram1 value))))

(defthm z*-rec-of-wx-rec
  (equal (z*-rec (blk-rec ptr off size) (wx-rec ptr off size value ram))
         (z*-rec (blk-rec ptr off size) ram))
  :hints (("goal" :in-theory (enable open-wx-rec wx-rec blk-rec)
           :induct (wx==ram-induction-8 off ptr ram size value))
          ))

(defthm wx==ram-rec-eighth
  (implies (equal (wx-rec ptr off size value ram1) ram2)
           (equal (z*-rec (blk-rec ptr off size) ram1)
                  (z*-rec (blk-rec ptr off size) ram2)))
  :hints (("Goal" :in-theory (enable blk-rec wx-rec open-wx-rec)
           :induct (wx==ram-induction-8 off ptr ram1 size value))
          )
  :rule-classes nil)

;do we need both rules?
(defthm wx==ram-rec-eighth-2
  (implies (equal ram2 (wx-rec ptr off size value ram1))
           (equal (z*-rec (blk-rec ptr off size) ram2)
                  (z*-rec (blk-rec ptr off size) ram1)))
  :hints (("Goal" :by  wx==ram-rec-eighth)))


(defthm wx==ram-rec-value-same
  (implies (and (equal (wx-rec ptr off size value ram1) ram2)
                (integerp off)
                (integerp size)
                (< off size)) 
           (equal (;wfixw 8 (- size off)
                   acl2::loghead (* 8 (nfix  (- size off)))
                   value)
                  (rx-rec ptr off size ram2)))
  :hints (("Goal" :in-theory (enable rx-rec wx-rec ;open-wfixw ;WCAR
                                     open-rx-rec
                                     )
           :expand  (WX-REC PTR OFF SIZE VALUE RAM1)
           :induct (wx==ram-induction-8 off ptr ram1 size value)))
  :rule-classes nil)

;do we need both rules?

(defthm wx==ram-rec-value-same-2
  (implies (and (equal ram2 (wx-rec ptr off size value ram1))
                (integerp off)
                (integerp size)
                (< off size)) 
           (equal (acl2::loghead (* 8 (nfix  (- size off))) value)
                  (rx-rec ptr off size ram2)))
  :hints (("Goal" :by wx==ram-rec-value-same)))

;bzo
(defthm wr-correct-val-equal
  (implies (and (< off size)
                (integerp off)
                (integerp size)
                (<= 0 off)
                (equal (acl2::loghead (* 8 (nfix (- size off))) val)
                       (rx-rec ptr off size ram2)))
           (equal (wx-rec ptr off size val ram2)
                  ram2))
  :hints (("Goal" :in-theory (e/d (wx-rec rx-rec) 
                                  (open-wx-rec open-rx-rec)))))

(defthmd z*-same-wx-rec-0
  (equal (z*-rec (blk-rec ptr off size) ram)
         (wx-rec ptr off size 0 ram))
  :hints (("Goal" :in-theory (e/d (wx-rec blk-rec) 
                                  (z*-rec-of-wx-rec)))))


(encapsulate
 ()

 (local
  (defthm useful
    (implies (and (equal (wr a val1 ram1)
                         (wr a val1 ram2))
                  (equal val2 val3)
                  (equal (wr a val3 ram2) ram2))
             (equal (wr a val2 ram1) ram2))))
 
 (defthm other-way-1
   (implies (and (equal (z*-rec (blk-rec ptr off size) ram1)
                        (z*-rec (blk-rec ptr off size) ram2))
                 (equal ( ;wfixw 8 (- size off)
                         acl2::loghead (* 8 (nfix  (- size off)))
                         value) 
                        (rx-rec ptr off size ram2))
                 (< off size)
                 (integerp off)
                 (integerp size)
                 (<= 0 off))
            (equal (wx-rec ptr off size value ram1) ram2))
   :hints (("Goal" :in-theory (enable open-wx-rec 
                                      z*-same-wx-rec-0
                                      open-rx-rec
                                      rx-rec blk-rec ;open-wfixw; wcar wcdr wcons
                                      WR==R!
                                      )
            :induct (wx==ram-induction-8 off ptr ram1 size value)))
   :rule-classes nil)

 )

(defthm other-way-2
  (implies (and (equal (z*-rec (blk-rec ptr off size) ram1)
                       (z*-rec (blk-rec ptr off size) ram2))
                (equal (;wfixw 8 (- size off)
                        acl2::loghead (* 8 (nfix  (- size off)))                              
                              value) 
                       (rx-rec ptr off size ram2))
                (< off size)
                (integerp off)
                (integerp size)
                (<= 0 off))
           (equal ram2 (wx-rec ptr off size value ram1)))
  :hints (("Goal" :use (:instance other-way-1)))
  :rule-classes nil)

;bzo -use sblk in RHS?
;exported?
(defthmd wx==ram-rec
  (implies (and (<= 0 off)
                (< off size) 
                (integerp off)
                (integerp size))
           (equal (equal (wx-rec ptr off size value ram1) ram2)
                  (and (equal (z*-rec (blk-rec ptr off size) ram1)
                              (z*-rec (blk-rec ptr off size) ram2))
                       (equal (acl2::loghead (* 8 (nfix (- size off))) value) 
                              (rx-rec ptr off size ram2)))))
  :hints (("Goal" :in-theory (disable open-rx-rec)
           :use ((:instance other-way-1)
                 (:instance other-way-2)
                 (:instance wx==ram-rec-eighth)
                 (:instance wx==ram-rec-eighth-2)
                 (:instance wx==ram-rec-value-same)
                 (:instance wx==ram-rec-value-same-2)))))

(defthm z*-rec-memberp
  (implies (memberp x y)
           (equal (z*-rec y (wr x val ram))
                  (z*-rec y ram)))
  :hints (("Subgoal *1/2" :cases ((equal x (car y))))))






(encapsulate
 ()

 (local
  (defthm lemma1
    (implies (and (integerp ptr)
                  (not (subbagp (cons (+ 1 off ptr) (blk-rec ptr (+ 2 off) size)) y))
                  (integerp off)
                  (integerp size)
                  (< off size)
                  (subbagp (cons (+ off ptr) (blk-rec ptr (+ 1 off) size)) y))
             (equal (z*-rec y (wx-rec (ifix ptr)
                                      (+ 1 (ifix off))
                                      (ifix size)
                                      (acl2::logtail ;wcdr
                                       8 value)
                                      ram))
                    (z*-rec y ram)))
    :hints (("Goal" :in-theory (enable blk-rec)
             :do-not-induct t))
    :rule-classes nil))
  
 (local
  (defthm lemma2
    (implies (and (not (integerp ptr))
                  (not (subbagp (cons (+ 1 off 0) (blk-rec 0 (+ 2 off) size)) y))
                  (integerp off)
                  (integerp size)
                  (< off size)
                  (subbagp (cons off (blk-rec 0 (+ 1 off) size)) y))
             (equal (z*-rec y (wr off (acl2::loghead ;wcar 
                                       8 value)
                                  (wx-rec (ifix ptr)
                                          (+ 1 (ifix off))
                                          (ifix size)
                                          (acl2::logtail ;wcdr
                                           8 value)
                                          ram)))
                    (z*-rec y ram)))
    :hints (("Goal" :in-theory (enable blk-rec)
             :do-not-induct t
             ;:cases ((< (+ 1 off) size))
             ))
    :rule-classes nil))
 
;disable ifix?
 (defthm z*-over-wx-subbagp
   (implies (and (integerp off)
                 (integerp size)
                 (< off size)
                 (subbagp (blk-rec ptr off size) y) ;move this hyp up?
                 )
            (equal (z*-rec y (wx-rec ptr off size value ram))
                   (z*-rec y ram)))
   :hints (("Goal" :in-theory (enable wx-rec blk-rec open-rx-rec)
            :do-not-induct t
            :expand ((WX-REC 0 OFF SIZE VALUE RAM))
            :induct (wx-rec ptr off size value ram))
           ("Subgoal *1/2" :use (lemma1
                                 lemma2
                                 ))))
 ) ;closes encapsulate


(defthm z*-rec-switcheroo
  (equal (z*-rec (blk-rec ptr off size)
                 (z*-rec list (wx-rec ptr off size value ram1)))
         (z*-rec list (z*-rec (blk-rec ptr off size) ram1)))
  :hints (("Goal" :in-theory (disable z*-rec-commutativity 
                                      open-wx-rec open-blk-rec)
           :use (:instance z*-rec-commutativity 
                           (x (blk-rec ptr off size))
                           (y list) 
                           (ram (wx-rec ptr off size value ram1))))))

(defthm z*-rec-over-wx-rec
  (implies
   (disjoint (blk-rec ptr off size) list)
   (equal (z*-rec list (wx-rec ptr off size value ram))
          (wx-rec ptr off size value (z*-rec list ram))))
  :hints (("goal" :induct (wx-rec ptr off size value ram)
           :in-theory (enable wx-rec blk-rec))))



(defthmd z*-rec-disjoint
  (implies (and (disjoint list (blk-rec ptr off size))
                (<= 0 off)
                (< off size)
                (integerp off)
                (integerp size))
           (equal (acl2::loghead (* 8 (nfix (- size off))) value)
                  (rx-rec ptr off size 
                          (z*-rec list (wx-rec ptr off size value ram)))))
  :hints (("goal" :in-theory (e/d (;wfixw
                                     blk-rec
                                     open-rx-rec
                                     open-wx-rec
                                     ) (;open-rx-rec
                                        ;Z*-REC
                                        ))
           :induct (wx==ram-induction-8 off ptr ram size value))))

(encapsulate 
 ()

 (local
  (defthm z*-of-wx-rec-8
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint (blk-rec ptr off size) list)
                  (equal (z*-rec list (wx-rec ptr off size value ram1))
                         (z*-rec list ram2)))
             (equal (z*-rec (append (blk-rec ptr off size) list) ram1)
                    (z*-rec (append (blk-rec ptr off size) list) ram2)))))

 (local
  (defthm z*-of-wx-rec-8-2
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint (blk-rec ptr off size) list)
                  (equal (z*-rec list ram2)
                         (z*-rec list (wx-rec ptr off size value ram1))))
             (equal (z*-rec (append (blk-rec ptr off size) list) ram2)
                    (z*-rec (append (blk-rec ptr off size) list) ram1)))))
 
 (local
  (defthm z*-of-wx-rec-4
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint (blk-rec ptr off size) list)
                  (equal (z*-rec list (wx-rec ptr off size value ram1))
                         (z*-rec list ram2)))
             (equal ( ;wfixw 8 (- size off)
                     acl2::loghead (* 8 (nfix  (- size off)))
                     value)
                    (rx-rec ptr off size ram2)))
    :hints (("Goal" :do-not-induct t
             :in-theory (disable open-blk-rec open-rx-rec open-wx-rec
                                 rx-rec-over-z*-rec-disjoint z*-rec-disjoint)
             :use ((:instance rx-rec-over-z*-rec-disjoint (ram ram2))
                   (:instance z*-rec-disjoint (ram ram1)))))))

 (local
  (defthm z*-of-wx-rec-4-2
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint (blk-rec ptr off size) list)
                  (equal (z*-rec list ram2)
                         (z*-rec list (wx-rec ptr off size value ram1))))
             (equal ( ;wfixw 8 (- size off)
                     acl2::loghead (* 8 (nfix  (- size off)))
                     value)
                    (rx-rec ptr off size ram2)))
    :hints (("Goal" :use (:instance z*-of-wx-rec-4)))))


 (local
  (defthm other-way
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint (blk-rec ptr off size) list)
                  (equal (z*-rec (append (blk-rec ptr off size) list) ram1)
                         (z*-rec (append (blk-rec ptr off size) list) ram2))
                  (equal ( ;wfixw 8 (- size off)
                          acl2::loghead (* 8 (nfix  (- size off)))
                          value)
                         (rx-rec ptr off size ram2)))
             (equal (z*-rec list (wx-rec ptr off size value ram1))
                    (z*-rec list ram2)))
    :hints (("Goal" :in-theory (e/d (wx==ram-rec) ( ;WFIXW-REDUCTION
                                                   ))))))
 
 (local
  (defthm other-way-of-2
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint (blk-rec ptr off size) list)
                  (equal (z*-rec (append (blk-rec ptr off size) list) ram2)
                         (z*-rec (append (blk-rec ptr off size) list) ram1))
                  (equal ( ;wfixw 8 (- size off)
                          acl2::loghead (* 8 (nfix  (- size off)))
                          value)
                         (rx-rec ptr off size ram2)))
             (equal (z*-rec list ram2)
                    (z*-rec list (wx-rec ptr off size value ram1))))
    :hints (("Goal" :in-theory (e/d (wx==ram-rec) ( ;WFIXW-REDUCTION
                                                   ))))))
 

;should bring the z*-rec inside the wx-rec?
 (defthmd z*-of-wx-rec
   (implies (and (<= 0 off)
                 (< off size)
                 (integerp off)
                 (integerp size)
                 (disjoint (blk-rec ptr off size) list))
            (equal (equal (z*-rec list (wx-rec ptr off size value ram1))
                          (z*-rec list ram2))
                   (and (equal (z*-rec (append (blk-rec ptr off size) list) ram1)
                               (z*-rec (append (blk-rec ptr off size) list) ram2))
                        (equal (acl2::loghead (* 8 (nfix  (- size off))) value)
                               (rx-rec ptr off size ram2)))))
   :hints (("Goal" :in-theory (disable other-way other-way-of-2 z*-of-wx-rec-8-2
                                       z*-of-wx-rec-8 z*-of-wx-rec-4-2 z*-of-wx-rec-4)
            :use ((:instance other-way)
                  (:instance other-way-of-2)
                  (:instance z*-of-wx-rec-8-2)
                  (:instance z*-of-wx-rec-8)
                  (:instance z*-of-wx-rec-4-2)
                  (:instance z*-of-wx-rec-4)))))                        

 ) ;closes encapsulate


;exported?
;bzo
(defthm wx-wfixn-reduction
  (equal (wx size ptr (acl2::loghead (fix-size size) value) ram)
         (wx size ptr value ram))
  :hints (("Goal" :cases ((integerp value))
           :in-theory (enable wx ;wfixn 
                              wx-rec==wx-rec))))

;(local (in-theory (disable UNFIXED-SIZE-MAX-OFFSET)))

(defthm max-offset-when-multiple-of-8
  (implies (and (multiple-of-8 size)
                (< 0 SIZE)
                )
           (equal (max-offset size)
                  (+ -1 (/ size 8))))
  :hints (("Goal" :in-theory (enable MAX-OFFSET-REWRITES-TO-FLOOR
                                     multiple-of-8))))




(defthmd rx-to-rd-list-reduction
  (equal (rx size ptr ram)
         (wintlist (rd-list (sblk size ptr) ram)))
  :hints (("goal" :in-theory (enable RX-REC-TO-RD-LIST-REDUCTION
                                     rx 
                                     blk 
                                     sblk))))

(defthmd wx-to-wr-list-reduction
  (equal (wx size ptr value ram)
         (wr-list (sblk size ptr) (enlistw (1+ (max-offset size)) value) ram))
  :hints (("goal" :in-theory (enable WX-REC-TO-WR-LIST-REDUCTION
                                     wx blk sblk))))

;exported?
;; Do we want this enabled?
(defthmd wr-to-wx
  (implies (integerp a)
           (equal (wr a v ram)
                  (wx 8 a v ram)))
  :hints (("goal" :in-theory (e/d (;WFIXW WINTW ;wintn ;wfix 
                                   OPEN-WX-REC wx wx-rec)
                                  (WX-REC-TO-WR-LIST-REDUCTION)))))



;bzo could redo the multiple of 8 stuff using divides from super-ihs

(defthmd rx-16-rewrite
  (equal (gacc::rx 16 addr ram)
         (logapp 8 ;bzo use logapp here?
                 (gacc::rd (ifix addr) ram)
                 (gacc::rd (+ 1 (ifix addr)) ram)))
  :hints (("Goal" :expand (gacc::rx 16 addr ram)
           :in-theory (enable gacc::open-blk-rec gacc::open-rx-rec))))

(defthmd rx-rd-equivalence
  (equal (gacc::rx 8 addr ram)
         (gacc::rd (ifix addr) ram))
  :hints (("Goal" :in-theory (enable gacc::rx gacc::wintlist
                                     gacc::rx-rec
                                     gacc::blk-rec gacc::rd-list))))


;should have a rule to rewrite subbagp of sblks?
;generalize?
(defthm sblk-16-subbagp-32
  (implies (integerp addr)
           (bag::subbagp (gacc::sblk 16 (+ 2 addr))
                         (gacc::sblk 32 addr)))
  :hints (("Goal" :in-theory (e/d (gacc::sblk gacc::blk
;                                     bag::subbagp
                                     bag::memberp) 
                                  (BAG::SUBBAGP-CDR-REMOVE-1-REWRITE)))))


(defthm rx-8-wx-16-hack
  (equal (gacc::rx 8 ad (gacc::wx 16 ad value ram))
         (loghead 8 value))
  :hints (("Goal" :expand  (gacc::addr-range ad 2)
           :in-theory (enable gacc::rx gacc::wx gacc::open-wx-rec gacc::open-rx-rec))))
        

;gen...        
(defthm loghead-8-of-rx
  (equal (loghead 8 (gacc::rx 16 a ram))
         (gacc::rx 8 a ram))
  :hints (("Goal" :in-theory (enable gacc::rx gacc::open-rx-rec))))

(defthm wx-of-rx-special-case
  (equal (gacc::wx size ad (gacc::rx size ad ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable gacc::wx-of-rx))))
(encapsulate
 ()
 
 (local
  (defthm rd-over-wx-rec-crock
    (implies (bag::disjoint (gacc::sblk 8 x)
                            (gacc::sblk size addr))
             (equal (gacc::rd x
                              (gacc::wx-rec addr 0 (+ 1 (gacc::max-offset size))
                                            val ram))
                    (gacc::rd x ram)))
    :hints (("Goal" :in-theory (e/d (ifix gacc::sblk gacc::blk) (GACC::WX-REC-TO-WR-LIST-REDUCTION))
             :expand ((GACC::BLK-REC X 0 1))
             :use (:instance gacc::rd-over-wx-rec-instance
                             (GACC::RPTR x) (gacc::wptr addr) (gacc::woff 0)
                             (gacc::wmax (+ 1 (gacc::max-offset size))) (gacc::value val) (gacc::ram
                                                                                           ram))))))

 ;; ;i don't like how this uses addresses-disjoint -ews
 ;;  (defthm rd-over-wx
 ;;    (implies (addresses-disjoint x 8 addr size)
 ;;             (equal (gacc::rd x (gacc::wx size addr val ram))
 ;;                    (gacc::rd x ram)))
 ;;    :hints (("Goal" :use rd-over-wx-rec-crock 
 ;;             :in-theory (enable addresses-disjoint gacc::wx))
 ;;            ))

 (defthm rd-over-wx-2
   (implies (not (bag::memberp (ifix x) (gacc::sblk size addr)))
            (equal (gacc::rd x (gacc::wx size addr val ram))
                   (gacc::rd x ram)))
   :hints (("Goal" :use rd-over-wx-rec-crock 
            :in-theory (enable ;addresses-disjoint
                        gacc::wx GACC::SBLK-8-REWRITE))
           ))
 
 ) ;; end encapsulate




(defthm rw-wx-8-16-lemma
  (implies (and (integerp ad2) (integerp ad))
           (equal (GACC::RX 8 ad (GACC::WX 16 ad2 VALUE RAM))
                  (if (equal ad ad2)
                      (loghead 8 value)
                    (if (equal ad (+ 1 ad2))
                        (loghead 8 (logtail 8 value))
                      (GACC::RX 8 ad RAM)))))
  :hints (("Goal" :expand ((GACC::ADDR-RANGE AD2 2)
                           (GACC::ADDR-RANGE AD 2)
                           (GACC::ENLISTW 2 VALUE))
           :in-theory (enable gacc::wx gacc::rx  gacc::open-wx-rec gacc::open-rx-rec))))


;this one has a loop-stopper....
(defthm my-wx-over-wx
  (implies (bag::disjoint (gacc::sblk size  ptr)
                          (gacc::sblk wsize wptr))
           (equal (gacc::wx size ptr value (gacc::wx wsize wptr wvalue ram))
                  (gacc::wx wsize wptr wvalue (gacc::wx size ptr value ram))))
  :rule-classes ((:rewrite :loop-stopper ((ptr wptr gacc::wx)))))

(in-theory (disable gacc::wx-over-wx))

(defthm rx-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (gacc::rx numbits ad ram)
                  (gacc::rx numbits 0 ram)))
  :hints (("Goal" :in-theory (enable gacc::rx))))

(defthm wx-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (gacc::wx numbits ad val ram)
                  (gacc::wx numbits 0 val ram)))
  :hints (("Goal" :in-theory (enable gacc::wx))))

;; 
;; (defthm my-wx-over-wx-both
;;   (equal (gacc::wx size ptr value (gacc::wx wsize wptr wvalue ram))
;;          (if (bag::disjoint (gacc::sblk size  ptr)
;;                             (gacc::sblk wsize wptr))
;;              (gacc::wx wsize wptr wvalue (gacc::wx size ptr value ram))
;;            (gacc::wx size ptr value ram)
;;            ))
;;   :rule-classes ((:rewrite :loop-stopper ((ptr wptr gacc::wx))))) ;bzo eric changed loop-stopper


;(local (in-theory (enable WFIXW-REDUCTION)))

;;
;; WFIXN
;;

;; ;b should be always be (word-size).
;; ;Chop v down to fit in as many chunks as it takes to represent an N-bit value.
;; ;what if N is 0?
;; (defund wfixn (b n v)
;;   (declare (type t b n v))
;;   (wfixw b (1+ (max-offset n)) v))

;; (defthm integerp-wfixn
;;   (integerp (wfixn b n value)))

;; (defthm wfixn-0
;;   (equal (wfixn b n 0) 
;;          0)
;;   :hints (("Goal" :in-theory (enable wfixn))))

;; ;consider t-p rules!
;; (defthm wfixn-non-negative
;;   (<= 0 (wfixn b n v))
;;   :hints (("Goal" :in-theory (enable wfixn))))

;; (defthm wfixn-of-nfix
;;   (equal (wfixn b (nfix n) v)
;;          (wfixn b n v))
;;   :hints (("Goal" :in-theory (enable wfixn nfix))))

;; (defthm non-integer-size-wfixn
;;   (implies (and (syntaxp (not (quotep n)))
;;                 (not (equal n (nfix n))))
;;            (equal (wfixn b n v)
;;                   (wfixn b 0 v)))
;;   :hints (("goal" :in-theory (enable wfixn max-offset))))

;; (defthm wfixn-arith-reduction
;;   (implies (and (integerp a)
;;                 (integerp x))
;;            (equal (wfixn b n (+ a (wfixn b n x)))
;;                   (wfixn b n (+ a x))))
;;   :hints (("goal" :in-theory (enable wfixn wfixw-reduction))))
 
;; (defthm wfixn-ifix
;;   (equal (wfixn b n (ifix x)) 
;;          (wfixn b n x))
;;   :hints (("goal" :in-theory (enable wfixn wfixw-reduction))))

;; (defthmd zp-wfixn
;;   (implies (and (syntaxp (not (quotep n)))
;;                 (zp n))
;;            (equal (wfixn b n v)
;;                   (wfixn b 0 v)))
;;   :hints (("goal" :in-theory (enable wfixn))))

;; ;bbzo. Strange, why the second 8 in the lhs?
;; (defthmd wfixn-unsigned-byte-p
;;   (implies (and (integerp size)
;;                 (<= 8 size))
;;            (acl2::unsigned-byte-p size (wfixn 8 size 8)))
;;   :hints (("Goal" :in-theory (e/d (wfixn) ()))))

;; ;I think n in calls to wfixn will usually be a constant and will usually be either 8(?), 16, or 32.
;; ;similar rule fro wfixw?
;; (defthm wfixn-rewrite-to-loghead
;;   (equal (wfixn 8 n v)
;;          (acl2::loghead (fix-size n) v))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable fix-size-rewrite
;;                               acl2::imod ;bzo
;;                               max-offset-rewrites-to-floor
;;                               WFIXW-REDUCTION
;;                               WFIXN 
;;                               acl2::LOGHEAD))))

;; ;bzo
;; (local (in-theory (disable wfixn-rewrite-to-loghead)))

;; ;bzo
;; (defthm wfixn-unsigned-byte-p-better
;;   (implies (<= (fix-size n) m)
;;            (equal (acl2::unsigned-byte-p m (wfixn 8 n x))
;;                   (integerp m)))
;;   :hints(("goal" :in-theory (e/d (wfixn-rewrite-to-loghead) ()))))


;bzo consider killing this
;; (defthm wfixn-unsigned-byte-p
;;   (implies
;;     (or
;;      (equal size 8)
;;      (equal size 16)
;;      (equal size 32))
;;    (unsigned-byte-p size (wfixn 8 size x)))
;;   :hints(("goal" :in-theory (e/d nil (wfixw)))))

;; jsut rewrite wfixn to wcar?
;; ;trying disabled
;; (defthmd wcar-reduction
;;   (equal (equal (wcar b v) (wfixn b 1 v))
;;          t)
;;   :hints (("goal" :in-theory (enable open-wfixw wfixn))))


;; ;can this loop?
;; (defthmd unfixed-size-wfixn
;;   (implies (syntaxp (syntax-unfixed-size s))
;;            (equal (wfixn b s v)
;;                   (wfixn b (fix-size s) v)))
;;   :hints (("goal" :in-theory (enable wfixn))))


;; ;this one shouldn't loop
;; (defthm unfixed-size-wfixn-constant-version
;;   (implies (syntaxp (and (quotep s)
;;                          (not (equal (fix-size (cadr s)) (cadr s)))))
;;            (equal (wfixn b s v)
;;                   (wfixn b (fix-size s) v)))
;;   :hints (("goal" :use unfixed-size-wfixn)))

;; (defthm signed-byte-p-of-wfixn
;;   (implies (< (fix-size n) m) 
;;            (equal (acl2::signed-byte-p m (wfixn 8 n x))
;;                   (integerp m)))
;;   :hints (("Goal" :in-theory (enable wfixn-rewrite-to-loghead))))


;;
;; WINTN
;;

;; ;; b should equal (wordsize).
;; ;; Test whether V is an integer which can fit in as many words as it takes to represent an N-bit value.
;; (defund wintn (b n v)
;;   (declare (type t n))
;;   (wintw b (1+ (max-offset n)) v))

;; make a fw-chaining rule?
;; (defthmd wintn-integerp
;;   (implies (wintn a b x)
;;            (integerp x))
;;   :hints (("goal" :in-theory (enable wintn wintw))))

;; (defthm wintn-wfixn
;;   (implies (wintn s n x)
;;            (equal (wfixn s n x) 
;;                   x))
;;   :hints (("Goal" :in-theory (enable wintn wfixn))))

;; (encapsulate
;;  ()
;;  (local (defthm wintn-unsigned-byte-p-helper
;;           (implies (and (multiple-of-8 size)
;;                         (< 0 size)
;;                         (wintn 8 size x))
;;                    (acl2::unsigned-byte-p size x))
;;           :hints(("goal" 
;;                   :cases ((acl2-numberp size))
;;                   :in-theory (e/d (wintn 
;;                                    wintw 
;; ;multiple-of-8
;;                                    wfixw-unsigned-byte-p
;;                                    max-offset
;;                                    wfixw)
;;                                   ( WINTW-WFIXW
;; ;UNFIXED-SIZE-MAX-OFFSET ;looped!
;;                                    ))))))

;;  (defthm wintn-unsigned-byte-p
;;    (implies (and (multiple-of-8 size)
;;                  (wintn 8 size x))
;;             (equal (acl2::unsigned-byte-p size x)
;;                    (or (< 0 size)
;;                        (and (equal size 0)
;;                             (equal 0 x)))))
;;    :otf-flg t
;;    :hints (("Goal" :in-theory (e/d (acl2::unsigned-byte-p)( wintn-unsigned-byte-p-helper))
;;             :use ( wintn-unsigned-byte-p-helper)))))

;; ;replace the other one?
;; (defthm unsigned-byte-p-wintn-eric
;;   (implies (acl2::unsigned-byte-p size x)
;;            (equal (wintn 8 size x)
;;                   (if (integerp size)
;;                       t
;;                     (wintn 8 8 x)  ;simplify this?
;;                     )))
;;   :hints (("Goal" :in-theory (enable wintn 
;;                                      wintw 
;;                                      WFIXW-REDUCTION
;;                                      MAX-OFFSET-REWRITES-TO-FLOOR))))


;; (defthm unsigned-byte-p-wintn
;;   (implies (and (or (equal size 8)
;;                     (equal size 16)
;;                     (equal size 32))
;;                 (acl2::unsigned-byte-p size x))
;;            (wintn 8 size x))
;;   :hints (("Goal" :in-theory (enable wintn wintw WFIXW-REDUCTION))))

;; ;Eric turned this rule around, to rewrite to unsigned-byte-p when possible

;; (defthm unsigned-byte-p-wintn-equality
;;   (implies (or (equal size 8)
;;                (equal size 16)
;;                (equal size 32))
;;            (equal (wintn 8 size x)
;;                   (acl2::unsigned-byte-p size x)))
;;   :hints (("Goal" :in-theory (disable wintn))))

;; (defthm unsigned-byte-p-wfixn
;;   (implies (and (acl2::unsigned-byte-p n x)
;;                 (multiple-of-8 n))
;;            (equal (wfixn 8 n x)
;;                   x))
;;   :hints (("Goal" :use (:instance wintn-wfixn (s 8))
;;            :in-theory (disable wfixn 
;;                                wintn-wfixn
;;                                wintn))))

;; (defthm wintn-0
;;   (wintn b s 0)
;;   :hints (("goal" :in-theory (enable wintn wintw))))

;; (defthm wintn-wfixn-2
;;   (wintn b s (wfixn b s v))
;;   :hints (("goal" :in-theory (enable wintn wfixn wintw))))

;; can be expensive? 
;; (defthmd wintn-+
;;   (implies (wintn b w y)
;;            (<= 0 y))
;;   :hints (("goal" :in-theory (enable wintn wintw))))

;; (defthm wfixn-does-nothing-rewrite
;;   (equal (equal (wfixn b n v) v)
;;          (wintn b n v))
;;   :hints (("Goal" :in-theory (enable wintn wfixn wfixw wintw))))

;; (defthm wfixn-wfixn
;;    (equal (wfixn b n (wfixn b m v))
;;           (wfixn b (min (nfix n) (nfix m)) v))
;;    :hints (("Goal" :in-theory (enable wfixn))))

;; (defthm wfixn-when-n-is-zero
;;   (equal (wfixn b 0 v)
;;          (wfixn b 8 v)))

;; ;I've seen this loop.
;; (defthmd unfixed-size-wintn
;;   (implies (syntaxp (syntax-unfixed-size s))
;;            (equal (wintn b s v)
;;                   (wintn b (fix-size s) v)))
;;   :hints (("goal" :in-theory (enable wintn))))

;; ;this one shouldn't loop
;; (defthm unfixed-size-wintn-constant-version
;;   (implies (syntaxp (and (quotep s)
;;                          (not (equal (fix-size (cadr s)) (cadr s)))))
;;            (equal (wintn b s v)
;;                   (wintn b (fix-size s) v)))
;;   :hints (("goal" :use unfixed-size-wintn)))


;; (encapsulate
;;  ()

;;  (local
;;   (defun cnt (n)
;;     (if (zp n) 0
;;       (cnt (1- n)))))

;;  (local
;;   (defthm linear-product
;;     (implies
;;      (and
;;       (not (zp n))
;;       (integerp b)
;;       (<= 0 b))
;;      (<= 0 (+ (- B) (* B N))))
;;     :rule-classes (:linear :rewrite)
;;     :hints (("goal" :induct (cnt b)))))

;;  (local
;;   (defthm wfixw-arith-reduction
;;     (implies
;;      (and
;;       (integerp a)
;;       (integerp x))
;;      (equal (wfixw b n (+ a (wfixw b n x)))
;;             (wfixw b n (+ a (ifix x)))))
;;     :hints (("Goal" :in-theory (enable wfixw-reduction)))))
;;  )




;; ;not quite right
;; (defthm max-offset-reduce
;;   (implies (and (integerp x)
;;                 (<= 0 8))
;;            (equal (max-offset (+ -8 x))
;;                   (+ -1 (max-offset x))))
;;   :hints (("Goal" :in-theory (enable max-offset))))
         


;bbzo
;; (defthm wintn-8-rewrite
;;   (equal (wintn 8 n v)
;;          (acl2::unsigned-byte-p (+ 8 (* 8 (MAX-OFFSET N))) v))
;;   :hints (("Goal" :in-theory (e/d (wintn MAX-OFFSET-FIX-SIZE) ( ;UNFIXED-SIZE-MAX-OFFSET
;;                                                                       )))))
        

;; ;generalized above
;; (defthm wintn-unsigned-byte-p
;;   (implies (and (or (equal size 8)
;;                     (equal size 16)
;;                     (equal size 32))
;;                 (wintn 8 size x))
;;            (acl2::unsigned-byte-p size x))
;;   :hints(("goal" :in-theory (e/d (wintn 
;;                                   wintw 
;;                                   wfixw-unsigned-byte-p)
;;                                  (wfixw)))))


;; (thm
;;  (implies (and (natp n))
;;           (equal (EQUAL (WFIXW 8 n X) X)
;;                  (acl2::unsigned-byte-p (* 8 n) x))))




                 
;; adapt?
;; (defthm wx-rec-wfixw
;;   (implies
;;    (and
;;     (integerp size)
;;     (integerp off)
;;     (< off size)
;;     (<= 0 off))
;;    (equal (wx-rec ptr off size (wfixw 8 (- size off) value) ram)
;;           (wx-rec ptr off size value ram)))
;;   :hints (("goal"
;;            :in-theory (enable ifix wx-rec))))



;; (DEFTHM RD-OVER-WX-REC-eric
;;   (IMPLIES (AND (NOT (MEMBERP RPTR (BLK-REC WPTR WOFF WMAX)))
;; ;                (<= (IFIX WMAX) (IFIX BWMAX))
;;                 (<= 0 (IFIX WOFF))
;;                 (<= 0 (IFIX WMAX)))
;;            (EQUAL (RD RPTR (WX-REC WPTR WOFF WMAX VALUE RAM))
;;                   (RD RPTR RAM))))




;;adapt?
;; (defthm wintw-rx-rec
;;   (implies
;;    (and
;;     (integerp off)
;;     (integerp max)
;;     (<= 0 off)
;;     (<= off max)
;;     (equal words (- max off)))
;;    (wintw 8 words (rx-rec ptr off max ram)))
;;   :hints (("Goal" :in-theory (enable rx-rec))))

;; ;;adapt?
;; (defthm wfixw-rx-rec
;;   (implies
;;    (and
;;     (integerp off)
;;     (integerp max)
;;     (<= 0 off)
;;     (<= off max)
;;     (equal words (- max off)))
;;    (equal (wfixw 8 words (rx-rec ptr off max ram))
;;           (rx-rec ptr off max ram))))


;; (defthm wintn-rx
;;   (wintn 8 size (rx size ptr ram))
;;   :hints (("Goal" :in-theory (enable wintn rx))))

;; (defthm wfixn-rx
;;   (implies (equal fsize size) ;this is odd...
;;            (equal (wfixn 8 fsize (rx size ptr ram))
;;                   (rx size ptr ram)))
;;   :hints (("Goal" :in-theory (enable rx wfixn))))

