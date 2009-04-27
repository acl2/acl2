#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;bzo Can we just use IHS functions like logapp, loghead, and logcdr, etc. -- instead of wcons, wcar, and wcdr, etc.? 

;bzo take pains to ensure that expensive ihs/super-ihs rules that aren't
;needed don't slow down proofs for users of gacc?

;;
;; Word constructor/destructors
;;

;bzo we probably don't need this much of super-ihs...  for example, gacc probably doesn't need many theorems about logior, etc...

(include-book "../super-ihs/super-ihs")

;(local (include-book "../super-ihs/super-ihs"))
;(include-book "../super-ihs/unsigned-byte-p")
;(in-theory (disable ACL2::LOGHEAD*-BETTER))

;Attempt to include in this book redundant copies of just those events from
;super-ihs that we need for gacc (because having all the events can slow
;proofs down).  Alternatively, we could include everything and disable the
;rules we don't want to fire.  Or leave stuff enabled and see if we can make
;things fast enough.  It worries me a bit to deliberately exclude most
;super-ih rules from most of our books, since I'd like changes to super-ihs to
;be tested by the regression suite...

;; (DEFUN ACL2::IMOD (ACL2::I ACL2::J)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::I)
;;                               (INTEGERP ACL2::J)
;;                               (NOT (= 0 ACL2::J)))))
;;   (MOD (IFIX ACL2::I) (IFIX ACL2::J)))

;; (DEFUN ACL2::EXPT2 (ACL2::N)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::N)
;;                               (<= 0 ACL2::N))))
;;   (EXPT 2 (NFIX ACL2::N)))

;; (DEFUN ACL2::LOGHEAD (ACL2::SIZE ACL2::I)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::SIZE)
;;                               (>= ACL2::SIZE 0)
;;                               (INTEGERP ACL2::I))))
;;   (ACL2::IMOD ACL2::I (ACL2::EXPT2 ACL2::SIZE)))

;; (DEFUN ACL2::LOGAPP (ACL2::SIZE ACL2::I ACL2::J)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::SIZE)
;;                               (>= ACL2::SIZE 0)
;;                               (INTEGERP ACL2::I)
;;                               (INTEGERP ACL2::J))))
;;   (LET ((ACL2::J (IFIX ACL2::J)))
;;        (+ (ACL2::LOGHEAD ACL2::SIZE ACL2::I)
;;           (* ACL2::J (ACL2::EXPT2 ACL2::SIZE)))))

;; (in-theory (disable ACL2::UNSIGNED-BYTE-P))

;; (in-theory (disable ACL2::LOGHEAD))





;; ;; ;;
;; ;; ;; WCONS
;; ;; ;;

;; ;append Y onto the low B bits of X
;; ;trying enabled..
;; ;would like to remove this function in favor of logapp
;; (defun wcons (b x y)
;;   (declare (xargs :guard t))
;;   (acl2::logapp (nfix b) (ifix x) (ifix y)))

;; (defthm wcons-non-negative
;;   (implies (<= 0 (ifix z))
;;            (<= 0 (wcons b y z)))
;;   :hints (("goal" :in-theory (enable wcons))))

;; (defthm integerp-of-wcons
;;   (integerp (wcons b x y))
;;   :rule-classes (:rewrite :type-prescription))

;; (defthm wcons-unsigned-byte-p
;;   (implies (and (acl2::unsigned-byte-p n x)
;;                 (acl2::unsigned-byte-p b y)
;;                 (integerp b)
;;                 (< 0 b)
;;                 (integerp n)
;;                 (< 0 n)
;;                 )
;;            (acl2::unsigned-byte-p (+ n b) (wcons n x y)))
;;   :hints (("Goal" :in-theory (enable wcons))))

;; ;;
;; ;; WCAR
;; ;;

;; ;return the low B bits of X
;; ;trying enabled..
;; ;would like to remove this function in favor of loghead
;; (defun wcar (b x)
;;   (declare (xargs :guard t))
;;   (acl2::loghead (nfix b) (ifix x)))

;; (defthm integerp-of-wcar
;;   (integerp (wcar b x))
;;   :rule-classes (:rewrite :type-prescription))

;; (defthm wcar-unsigned-byte-p
;;   (implies (and (integerp b)
;;                 (< 0 b))
;;            (acl2::unsigned-byte-p b (wcar b v)))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-with-non-integerp-b
;;   (implies (not (integerp b))
;;            (equal (wcar b x)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-with-non-positive-b
;;   (implies (<= b 0)
;;            (equal (wcar b x)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-with-non-integerp-x
;;   (implies (not (integerp x))
;;            (equal (wcar b x)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-when-x-is-0
;;   (equal (wcar b 0)
;;          0)
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-of-wcar
;;   (equal (wcar b (wcar b x))
;;          (wcar b x))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-does-nothing
;;   (implies (acl2::unsigned-byte-p b x)
;;            (equal (wcar b x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; ;;
;; ;; WCDR
;; ;;

;; ;return everything except the low B bits of X.
;; ;That is, shift X to the right B places and truncate to an integer.
;; ;trying enabled..
;; ;would like to remove this function in favor of logtail
;; (defun wcdr (b x)
;;   (declare (xargs :guard t))
;;   (acl2::logtail (nfix b) (ifix x)))

;; (defthm integerp-of-wcdr
;;   (integerp (wcdr b x))
;;   :rule-classes (:rewrite :type-prescription))

;; (defthm wcdr-wcar-reduction
;;   (implies (equal (wcdr b x) 0)
;;            (equal (wcar b x)
;;                   (ifix x)))
;;   :hints (("Goal" :in-theory (enable wcar wcdr))))

;; (defthm wcdr-when-x-is-0
;;   (equal (wcdr b 0)
;;          0)
;;   :hints (("Goal" :in-theory (enable wcdr))))

;; (defthm wcdr-when-x-is-not-an-integerp
;;    (implies (not (integerp x))
;;             (equal (wcdr b x)
;;                    0))
;;    :hints (("Goal" :in-theory (enable wcdr))))

;; ;;
;; ;; Rules about (at least two of) WCONS, WCAR, and WCDR 
;; ;;

;; (defthm wcons-when-y-is-0
;;   (equal (wcons b x 0)
;;          (wcar b x))
;;   :hints (("Goal" :in-theory (enable wcons wcar))))

;; (defthm wcons-when-y-is-not-an-integerp
;;   (implies (not (integerp y))
;;            (equal (wcons b x y)
;;                   (wcar b x)))
;;   :hints (("Goal" :in-theory (enable wcons wcar))))

;; (defthm wcons-when-x-is-not-an-integerp
;;   (implies (not (integerp x))
;;            (equal (wcons b x y)
;;                   (wcons b 0 y)))
;;   :hints (("Goal" :in-theory (enable wcons wcar))))

;; (defthm wcar-of-wcons
;;   (equal (wcar b (wcons b x y))
;;          (wcar b x))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm wcdr-of-wcons
;;   (equal (wcdr b (wcons b x y))
;;          (ifix y))
;;   :hints (("Goal" :in-theory (enable wcdr wcons))))

;; (defthm wcons-equal-0-rewrite
;;   (equal (equal 0 (wcons b x y))
;;          (and (equal (wcar b x) 0)
;;               (equal (ifix y) 0)))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm equal-of-wcons-and-wcons-rewrite
;;   (equal (equal (wcons b v1 v2)
;;                 (wcons b v3 v4))
;;          (and (equal (wcar b v1) (wcar b v3))
;;               (equal (ifix v2) (ifix v4))))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm wcons-of-wcar
;;   (equal (wcons b (wcar b x) y)
;;          (wcons b x y))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))
  
;; (defthm wcdr-of-wcar
;;   (equal (wcdr b (wcar b x))
;;          0)
;;   :hints (("Goal" :in-theory (enable wcar wcdr))))

;; ;;
;; ;; WFIXW
;; ;;

;; ;Chop V down to fit in N B-bit chunks.
;; (defund wfixw (b n v)
;;   (declare (type (integer 0 *) n))
;;   (if (zp n) 0
;;     (acl2::logapp (nfix b) (acl2::loghead (nfix b) (ifix v)) (wfixw b (1- n) (acl2::logtail (nfix b) (ifix v))))))

;; ;; ;old
;; ;; (defund wfixw (b n v)
;; ;;   (declare (type (integer 0 *) n))
;; ;;   (if (zp n) 0
;; ;;     (wcons b (wcar b v) (wfixw b (1- n) (wcdr b v)))))

;; ;linear? ;-tp?
;; (defthm wfixw+
;;   (<= 0 (wfixw b s v))
;;   :hints (("goal" :in-theory (enable wfixw))))

;; (defthm wfixw-0
;;   (equal (wfixw b n 0) 
;;          0)
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-with-n-0
;;   (equal (wfixw b 0 v)
;;          0)
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm integerp-wfixw
;;   (integerp (wfixw b n value)))

;; (defthm wfixw-with-zp-n
;;   (implies (zp n)
;;            (equal (wfixw b n v)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-with-b-not-an-integerp
;;   (implies (not (integerp b))
;;            (equal (wfixw b n v)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-with-b-not-positive
;;   (implies (<= b 0)
;;            (equal (wfixw b n v)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-when-v-is-not-an-integerp
;;   (implies (not (integerp v))
;;            (equal (wfixw b n v)
;;                   (wfixw b n 0)))
;;   :hints (("Goal" :expand ((wfixw b n v)))))

;; (encapsulate
;;  ()
;;  (local (defthm wfixw-unsigned-byte-p-1
;;           (implies (and (integerp b)
;;                         (integerp n)
;;                         (<= 0 b) ;(< 0 b)
;;                         (<= 0 n) ;(< 0 n)
;;                         )
;;                    (acl2::unsigned-byte-p (* b n) (wfixw b n v)))
;;           :hints (("goal" :induct t
;;                    :in-theory (e/d (wfixw acl2::unsigned-byte-p ;wcar wcons
;;                                           ) ())))))

;;  (defthm wfixw-unsigned-byte-p ;new version..
;;    (implies (and (<= (* b n) size)
;;                  (integerp size)
;;                  (integerp b) ;could drop these hyps?
;;                  (integerp n)
;;                  (<= 0 b)
;;                  (<= 0 n)
;;                  )
;;             (acl2::unsigned-byte-p size (wfixw b n v)))
;;    :hints (("goal" :use  wfixw-unsigned-byte-p-1
;;             :in-theory (disable wfixw wfixw-unsigned-byte-p-1)))))

;; (defthmd wfixw-reduction
;;   (equal (wfixw b n v)
;;          (acl2::loghead (* (nfix b) (nfix n)) v))
;;   :hints (("goal" :induct (wfixw b n v)
;;            :in-theory (enable wfixw zp ;wcons wcar wcdr
;;                               ))))

;; ;yuck?
;; ;trying disabled.
;; (defthmd open-wfixw
;;   (implies (not (zp n))
;;            (equal (wfixw b n v)
;;                   (acl2::logapp (nfix b) (acl2::loghead (nfix b) (ifix v)) (wfixw b (1- n) (acl2::logtail (nfix b) (ifix v))))))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; ;; (defthmd open-wfixw
;; ;;   (implies (not (zp n))
;; ;;            (equal (wfixw b n v)
;; ;;                   (wcons b (wcar b v) (wfixw b (1- n) (wcdr b v)))))
;; ;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-wfixw
;;   (equal (wfixw b n (wfixw b m v))
;;          (wfixw b (min (nfix n) (nfix m)) v))
;;   :hints (("Goal" :in-theory (enable wfixw-reduction))))

;; ;rename
;; (defthm wcar-wcdr-wfixw
;;   (and (equal (acl2::loghead ;wcar
;;                b (wfixw b n value))
;;               (if (zp n) 
;;                   0 
;;                 (acl2::loghead ;wcar
;;                  b value)))
;;        (equal (acl2::logtail ;wcdr
;;                b (wfixw b n value))
;;               (if (zp n) 
;;                   0 
;;                 (wfixw b (1- n) (acl2::logtail ;wcdr
;;                                  b value)))))
;;   :hints (("Goal" :in-theory (enable open-wfixw))))

;;
;; WINTW
;;

;; ;test whether V is an integer which fits in N B-bit chunks.
;; ;could reduce to wint?
;; ;Eric would like to get rid of this function...
;; (defund wintw (b n v)
;;   (declare (type (integer 0 *) n))
;;   (and ;(integerp v) ;removed by Eric
;;        (equal (wfixw b n v) v)))

;; (defthmd wintw-unsigned-byte-p ;trying disabled...
;;   (implies (and (wintw b n v)
;;                 (equal (* b n) size)
;;                 (integerp b)
;;                 (integerp n)
;;                 (< 0 b)
;;                 (< 0 n)
;;                 )
;;            (acl2::unsigned-byte-p size v))
;;   :hints (("goal" :in-theory (enable wintw))))

;; (defthm wintw-rewrite-to-unsigned-byte-p
;;   (implies (and (integerp b)
;;                 (integerp n)
;;                 (<= 0 b)
;;                 (<= 0 n)
;;                 )
;;            (equal (wintw b n v)
;;                   (acl2::unsigned-byte-p (* b n) v)))
;;   :hints (("goal" :in-theory (enable wintw wfixw ;wcdr wcons
;;                                      ))))

;; (defthm wintw-when-n-is-zp
;;   (implies (and (zp n))
;;            (equal (wintw s n x)
;;                   (equal 0 x)))
;;   :hints (("Goal" :in-theory (enable wintw))))

;; ;;
;; ;; misc. word function properties
;; ;;

;; (defthm wintw-wfixw
;;   (implies (wintw s n x)
;;            (equal (wfixw s n x) 
;;                   x))
;;   :hints (("Goal" :in-theory (enable wfixw wintw))))



