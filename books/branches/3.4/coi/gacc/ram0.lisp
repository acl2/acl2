#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;This book introduces the functions RD, WR, RX, and WX for reading and writing to a memory, and proves basic theorems about them.
;For more theorems about RX and WX, see ram.lisp.

;bzo there are just a few mentions of wcons, wcar, and wcdr below.  i'd like to replace them with logapp, loghead, and logtail
;and remove this inclue book.


;(include-book "defrecord" :dir :records)

(include-book "mem")

;drop
(local (in-theory (enable (force)))) ;unfortunate that i had to do this

;;
;;
;; Word size specification
;;
;;


(defun word-size () (declare (xargs :verify-guards t)) 8)

(defun max-offset (size)
  (declare (type t size))
  (if (<= (nfix size) (word-size))
      0
    (1+ (max-offset (- (nfix size) (word-size))))))

;Make sure max-offset's :type-prescription rule is as strong as we think.
(encapsulate
 ()
 (local (defthm max-offset-type-prescription-test
          (and (integerp (max-offset size))
               (<= 0 (max-offset size)))
          :hints (("Goal" :in-theory '((:type-prescription max-offset)))))))

(defthm non-negative-integerp-max-offset
  (and (integerp (max-offset size))
       (<= 0 (max-offset size))))

(defthm max-offset-of-non-positive
  (implies (<= x 0)
           (equal (max-offset x)
                  0))
  :hints (("Goal" :in-theory (enable max-offset))))


;;    (defthm max-offset-nfix
;;      (equal (max-offset (nfix size))
;;             (max-offset size)))

;;    (defthm min-max-offset
;;      (equal (max-offset (min (nfix n) (nfix m)))
;;             (min (max-offset n)
;;                  (max-offset m)))
;;      :hints (("goal" :induct (dual-induct n m))))

(defthm max-offset-of-non-integer
  (implies (not (integerp x))
           (equal (max-offset x)
                  0))
  :hints (("Goal" :in-theory (enable max-offset))))

(defthmd max-offset-rewrites-to-floor
  (equal (max-offset size)
         (if (and (integerp size)
                  (< 0 size))
             (floor (+ -1 size) 8)
           0))
  :hints (("Goal" :in-theory (e/d (max-offset)
                                  ( ;UNFIXED-SIZE-MAX-OFFSET ;looped
                                   ))
           :do-not '(generalize eliminate-destructors))))

(encapsulate
 ()

 (local (defun dual-induct (n m)
          (if (or (<= (nfix n) (word-size))
                  (<= (nfix m) (word-size))) (cons n m)
            (dual-induct (- (nfix n) (word-size)) (- (nfix m) (word-size))))))

;rephrase in terms of < 
;trying with this non local...
 (defthm <=max-offset
   (implies (and (<= n m)
                 (integerp n)
                 (integerp m)
                 )
            (<= (max-offset n) (max-offset m)))
   :hints (("goal" :induct (dual-induct n m)
            :expand ((max-offset n)
                     (max-offset m))))
   :rule-classes (:linear :rewrite)))

;rewrite as (INTEGERP (* 1/8 SIZE))?? no...
;replace with eric's divides function?

(defund multiple-of-8 (n)
   (integerp (* 1/8 n))
   ;(equal n (* 8 (floor n 8)))
   )

(defthm multiple-of-8-fw-to-integerp-of-*-1/8
  (implies (multiple-of-8 x)
           (integerp (* 1/8 x)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable multiple-of-8))))

;(local (in-theory (disable UNFIXED-SIZE-MAX-OFFSET)))

(defthm max-offset-when-multiple-of-8
  (implies (and (multiple-of-8 size)
                (< 0 SIZE)
                )
           (equal (max-offset size)
                  (+ -1 (/ size 8))))
  :hints (("Goal" :in-theory (enable MAX-OFFSET-REWRITES-TO-FLOOR
                                     multiple-of-8))))


;;
;; RX/WX specifications
;;

;;
;; RX-REC
;;


;Read data from RAM.  Return the bytes stored at addresses BASE+OFF through
;BASE+MAX-1, all concatenated together, with data from the lower addresses in
;the lower-order positions of the result.

;Changed this to use logapp instead of wcons. -ews
(defund rx-rec (base off max ram)
  (declare (type t base off max ram)
           (xargs :measure (nfix (- (ifix max) (ifix off)))))
  (let ((off (ifix off))
        (max (ifix max)))
    (if (<= max off) 0
      (let ((v (rd (+ off (ifix base)) ram)))
        (acl2::logapp 8 v (rx-rec (ifix base) (1+ off) max ram))))))

(defthm integerp-rx-rec
  (integerp (rx-rec base off max ram))
  :rule-classes (:rewrite :type-prescription))

(defthm rx-rec-non-negative
  (<= 0 (rx-rec base off max ram))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable rx-rec))))

(defthm rx-rec-non-integer-ptr
  (implies (not (integerp x))
           (equal (rx-rec x off max ram)
                  (rx-rec 0 off max ram)))
  :hints (("Goal" :in-theory (enable rx-rec))))

(defthm rx-rec-when-max-is-less-than-off
  (implies (and (< max off)
                (integerp off)
                (integerp max))
           (equal (rx-rec base off max ram)
                  0))
  :hints (("Goal" :in-theory (enable rx-rec))))

(defthm loghead8-of-rx-rec
  (equal (acl2::loghead 8 (rx-rec base off max ram))
         (if (<= (ifix MAX) (ifix OFF))
             0
           (rd (+ (ifix base) (ifix off)) ram)))
  :hints (("Goal" :expand (rx-rec base off max ram))))

(defthm rx-rec-non-integer-off
  (implies (not (integerp off))
           (equal (rx-rec ptr off max ram)
                  (rx-rec ptr 0 max ram)))
  :hints (("Goal" :in-theory (e/d (rx-rec) (;ACL2::EQUAL-LOGAPP-X-Y-Z ;bzo
                                            )))))



(encapsulate
 ()
 (local (defthm unsigned-byte-p-of-rx-rec-helper
          (implies (and (integerp off)
                        (integerp max)
                        ;;(integerp base)
                        (<= off max)
                        )
                   (acl2::unsigned-byte-p (* 8 (- (ifix max) off)) (rx-rec base off max ram)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable rx-rec ;wcons
                                      )))))

 (defthm unsigned-byte-p-of-rx-rec
   (implies (and (<= (* 8 (- max off)) k)
                 (integerp off)
                 (integerp max)
                 ;;(integerp base)
                 ;;(<= off max)
                 )
            (equal (acl2::unsigned-byte-p k (rx-rec base off max ram))
                   (and (integerp k)
                        (<= 0 k))))
   :hints (("Goal" :use (:instance unsigned-byte-p-of-rx-rec-helper)
            :do-not '(generalize eliminate-destructors)
            :do-not-induct t
            :in-theory (disable unsigned-byte-p-of-rx-rec-helper)))))
;;
;; RX
;;

;Read SIZE bits of data from RAM, starting at address A.  (RAM is byte-addressable.)
;If SIZE is not a multiple of 8, it gets rounded up to a multiple of 8.  Thus, we read whole bytes.
;If SIZE is 0, it gets treated as if it were 8.
;Data from the lower addresses goes into the lower-order positions of the result.
(defund rx (size a ram) 
  (declare (type t size a ram))
  (rx-rec a 0 (1+ (max-offset size)) ram))

(defthm integerp-rx
  (integerp (rx size a ram))
  :rule-classes (:rewrite :type-prescription))

;was called positive-rx
(defthm rx-non-negative-rewrite
  (<= 0 (rx size a ram)))

(defthm rx-non-negative-type-prescription
  (<= 0 (rx size a ram))
  :rule-classes :type-prescription)

(defthm rx-non-negative-linear
  (<= 0 (rx size a ram))
  :rule-classes :linear)

(defthm rx-when-size-is-not-an-integerp
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
; (syntaxp (not (quotep n)))
            (not (integerp size)))
           (equal (rx size ptr ram)
                  (rx 0 ptr ram)))
  :hints (("goal" :in-theory (enable rx max-offset))))

(defthm rx-when-size-is-not-positive
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
; (syntaxp (not (quotep n)))
            (<= size 0) ;(not (equal n (nfix n)))
            )
           (equal (rx size ptr ram)
                  (rx 0 ptr ram)))
  :hints (("goal" :in-theory (enable rx max-offset))))

(defthm unsigned-byte-p-of-rx
  (implies (and (<= size size1)
                (multiple-of-8 size) ;drop this?
                (< 0 size) ;drop?
                )
           (equal (acl2::unsigned-byte-p size1 (rx size a ram))
                  (integerp size1)))
  :hints (("Goal" :in-theory (e/d (rx) (;MAX-OFFSET-WHEN-MULTIPLE-OF-8
                                        )))))

(encapsulate
 ()
 ;maybe this lemma doesn't belong here?
 (local (include-book "byte-p" :dir :super-ihs)) ;bzo

 (defthm signed-byte-p-of-rx-gen
   (implies (and (< size size1)
                 (multiple-of-8 size)
                 (integerp size)
                 (< 0 size)
                 )
            (equal (acl2::signed-byte-p size1 (rx size a ram))
                   (integerp size1)))
   :hints (("Goal" :use (:instance unsigned-byte-p-of-rx (size1 (+ -1 size1)))
            :in-theory (e/d ( ;ACL2::SIGNED-BYTE-P-UNSIGNED-BYTE-P
                             SIGNED-BYTE-P
                             )
                            ( ;WINTN-UNSIGNED-BYTE-P
                             unsigned-byte-p-of-rx))))))
;;
;; WX-REC
;;

;I changed this to call logtail and loghead instead of wcar and wcdr. -ews 

;bzo - I believe the calls to ifix on value below could be dropped if the
;guards on the following functions were changed to not include (integerp i):
;ifloor, imod, loghead, and logtail.  The guards of those 4 functions (and
;perhaps others) seem needlessly strong.  Why require (integerp i) when it's
;not necessary?  But for now I'm refraining from making changes to functions
;from IHS, since doing so would require either changing files in the books/
;directory (a bad idea) or making out own copy of ihs and using it instead of
;the one in books/ (something we want to do eventually but not yet). -ews

(defund wx-rec (base off max value ram)
  (declare (type t base off max value ram)
           (xargs :measure (nfix (- (ifix max) (ifix off)))))
  (let ((off (ifix off))
        (max (ifix max)))
    (if (<= max off) ram
      (let ((ram (wx-rec (ifix base) (1+ off) max (acl2::logtail 8 (ifix value)) ram)))
        (wr (+ off (ifix base)) (acl2::loghead 8 (ifix value)) ram)))))


(defthm wx-rec-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (wx-rec base off max value ram)
                  (wx-rec 0    off max value ram)))
  :hints (("Goal" :in-theory (enable wx-rec))))

(defthm wx-rec-when-off-is-not-an-integerp
  (implies (not (integerp off))
           (equal (wx-rec base off max value ram)
                  (wx-rec base 0   max value ram)))
  :hints (("Goal" :in-theory (e/d (wx-rec) (wr==r!)))))

(defthm wx-rec-when-max-is-not-an-integerp
  (implies (not (integerp max))
           (equal (wx-rec base off max value ram)
                  (wx-rec base off 0   value ram)))
  :hints (("Goal" :in-theory (e/d (wx-rec) (wr==r!)))))

(defthm wx-rec-when-value-is-not-an-integerp
  (implies (not (integerp value))
           (equal (wx-rec base off max value ram)
                  (wx-rec base off max 0 ram)))
  :hints (("Goal"  :expand ( (wx-rec base off 0 value ram)
                             (wx-rec base 0 max value ram))
           :in-theory (e/d (wx-rec) (wr==r!)))))

(defthm wx-rec-when-max-<=-off
  (implies (<= (ifix max) (ifix off))
           (equal (wx-rec base off max value ram)
                  ram))
  :hints (("Goal" :in-theory (enable wx-rec))))

;;
;; WX
;;

(defund wx (size a v ram)
  (declare (type t size a v ram))
  (wx-rec a 0 (1+ (max-offset size)) v ram))

;bzo rename
(defthm wx-when-size-is-not-an-integerp
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
                (not (integerp size))
                )
           (equal (wx size a v ram)
                  (wx 0 a v ram)))
  :hints (("goal" :in-theory (enable wx max-offset))))

(defthm wx-when-size-is-not-positive
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
                (<= size 0)
                )
           (equal (wx size a v ram)
                  (wx 0 a v ram)))
  :hints (("goal" :in-theory (enable wx max-offset))))







