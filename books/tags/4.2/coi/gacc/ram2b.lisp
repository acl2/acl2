#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;Bbzo replaces rams.lisp

(include-book "list-ops-fast")
(include-book "addr-range")

(include-book "ram3") ;bzo move common stuff into a third book

(local (include-book "rtl/rel4/arithmetic/fl" :dir :system))

;(local (include-book "../super-ihs/loglist")) ;bzo
(local (include-book "../super-ihs/super-ihs")) ;bzo

(local (in-theory (enable zp)))

;old:
;; For execution only.
;; We could reorder things to put the most common cases first..
;; Would the logapp nests be faster if they were expressed instead in terms of + and ash?
;; Add in type declarations (since the common cases fit in 32 bits).
;rename
;make tail recursive!
;; (defun rd-bytes-exec (numwords ad ram)
;;   (declare (type (integer 0 *) numwords)
;;            (type integer ad) ;weaken
;;            )
;;   (if (zp numwords)
;;       0
;;     (if (equal 1 numwords)
;;         (rd ad ram)
;;       (if (equal 2 numwords)
;;           (acl2::logapp 8 (rd ad ram) (rd (+ 1 ad) ram)) ;bzo
;;         (if (equal 4 numwords)
;;             (acl2::logapp 24
;;                           (acl2::logapp 16
;;                                         (acl2::logapp 8 (rd ad ram) (rd (+ 1 ad) ram))
;;                                         (rd (+ 2 ad) ram))
;;                           (rd (+ 3 ad) ram))
;;           (acl2::logapp 8 (rd ad ram) (rd-bytes-exec (+ -1 numwords) (+ 1 ad) ram)))))))
  

(defun addresses-of-data-word-univ (word-ad)
  (declare (type integer word-ad))
  (word-ad-to-byte-ads (loghead 31 word-ad) ;(logext 31 word-ad)
                       ))

(defthm CONSP-OF-CDR-OF-ADDRESSES-OF-DATA-WORD-univ
  (consp (cdr (ADDRESSES-OF-DATA-WORD-univ x))))

(defthm cddr-of-addresses-of-data-word-univ
  (equal (cddr (addresses-of-data-word-univ ad))
         nil))

(defthmd disjoint-of-addresses-of-data-word-univ-and-addresses-of-data-word-univ
  (equal (bag::disjoint (addresses-of-data-word-univ ad2)
                        (addresses-of-data-word-univ ad1))
         (not (equal (loghead 31 ad1) (loghead 31 ad2))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

;word-ad is a usb31?
(defund read-data-word-univ (word-ad ram)
  (declare (type integer word-ad)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (e/d (acl2::logext-logapp
                                                         read-data-word-exec
                                                         acl2::ash-as-logapp
                                                         word-ad-to-byte-ads
                                                         acl2::sum-with-shift-becomes-logapp-constant-version) 
                                                        (acl2::logapp-0-part-2-better))))))
;  (mbe :exec (read-data-word-exec denvr offset ram)
;      :logic
  (wintlist (rd-list (addresses-of-data-word-univ word-ad)
                     ram))
;)
  )

(defthm unsigned-byte-p-of-read-data-word-univ
  (unsigned-byte-p 16 (read-data-word-univ ad ram))
  :rule-classes ((:forward-chaining :trigger-terms ((read-data-word-univ ad ram))))
  :hints (("Goal" :in-theory (enable read-data-word-univ))))

(defthm unsigned-byte-p-of-read-data-word-univ-gen
  (implies (and (integerp n)
                (<= 16 n))
           (unsigned-byte-p n (read-data-word-univ ad ram))))

(defthm address-listp-of-word-ad-to-byte-ads
  (implies (and (equal (mem::size ram) 4294967296)
                (unsigned-byte-p 31 ad))
           (address-listp (word-ad-to-byte-ads ad) ram))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

;bzo check this?
(defund write-data-word-univ (word-ad value ram)
  (declare (type integer word-ad value)
           (xargs :guard (aamp-ramp ram))
           ;;            (xargs :guard-hints (("Goal" :in-theory (e/d (acl2::logext-logapp
           ;;                                                          read-data-word-exec
           ;;                                                          acl2::ash-as-logapp
           ;;                                                          word-ad-to-byte-ads
           ;;                                                          acl2::sum-with-shift-becomes-logapp-constant-version) 
           ;;                                                         (acl2::logapp-0-part-2-better)))))
           )
;  (mbe :exec (read-data-word-exec denvr offset ram)
;      :logic
  (wr-list (addresses-of-data-word-univ word-ad)
           (enlistw 2 value)
           ram)
;)
  )


;;
;; "read of write" lemmas
;;

(defthmd read-data-word-univ-of-write-data-word-univ-same
  (implies (equal (loghead 31 ad1) (loghead 31 ad2))
           (equal (read-data-word-univ ad1 (write-data-word-univ ad2 val ram))
                  (loghead 16 val)))
  :hints (("Goal" :in-theory
           (enable read-data-word-univ write-data-word-univ WORD-AD-TO-BYTE-ADS))))

(defthm read-data-word-univ-of-write-data-word-univ-same-cheap
  (equal (read-data-word-univ ad (write-data-word-univ ad val ram))
         (loghead 16 val))
  :hints (("Goal" :in-theory
           (enable read-data-word-univ write-data-word-univ WORD-AD-TO-BYTE-ADS))))

;rewrite the hyp to a claim about logheads?
(defthm read-data-word-univ-of-write-data-word-univ-diff
  (implies (bag::disjoint (addresses-of-data-word-univ ad2)
                          (addresses-of-data-word-univ ad1))
           (equal (read-data-word-univ ad1 (write-data-word-univ ad2 val ram))
                  (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory
           (enable read-data-word-univ write-data-word-univ WORD-AD-TO-BYTE-ADS))))

(in-theory (disable disjoint-of-word-ad-to-byte-ads)) ;bzo

(defthmd read-data-word-univ-of-write-data-word-univ-both
  (equal (read-data-word-univ ad1 (write-data-word-univ ad2 val ram))
         (if (equal (loghead 31 ad1) (loghead 31 ad2))
             (loghead 16 val)
           (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory (enable read-data-word-univ write-data-word-univ))))

;;
;; "write of write" lemmas
;;

(defthmd write-data-word-univ-of-write-data-word-same
  (implies (equal (loghead 31 ad1) (loghead 31 ad2))
           (equal (write-data-word-univ ad1 val1 (write-data-word-univ ad2 val2 ram))
                  (write-data-word-univ ad1 val1 ram)))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV))))

(defthm write-data-word-univ-of-write-data-word-same-cheap
  (equal (write-data-word-univ ad val1 (write-data-word-univ ad val2 ram))
         (write-data-word-univ ad val1 ram))
  :hints (("Goal" :in-theory (enable write-data-word-univ))))

;bzo How do we want to sort the writes?
(defthm write-data-word-univ-of-write-data-word-univ-diff
  (implies (bag::disjoint (addresses-of-data-word-univ ad2)
                          (addresses-of-data-word-univ ad1))
           (equal (write-data-word-univ ad1 val1 (write-data-word-univ ad2 val2 ram))
                  (write-data-word-univ ad2 val2 (write-data-word-univ ad1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((ad2 ad1))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV))))

(defthmd write-data-word-univ-of-write-data-word-univ-both
  (equal (write-data-word-univ ad1 val1 (write-data-word-univ ad2 val2 ram))
         (if (equal (loghead 31 ad1) (loghead 31 ad2))
             (write-data-word-univ ad1 val1 ram)
           (write-data-word-univ ad2 val2 (write-data-word-univ ad1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((ad2 ad1))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV))))
        
(defund clear-data-word-univ (word-ad ram)
  (declare (type integer word-ad)
           (xargs :guard (aamp-ramp ram))
           )
  (write-data-word-univ word-ad 0 ram))

(defthm write-data-word-univ-equal-rewrite
  (equal (equal (write-data-word-univ ad value ram1) ram2)
         (and (equal (loghead 16 value) (read-data-word-univ ad ram2))
              (equal (clear-data-word-univ ad ram1)
                     (clear-data-word-univ ad ram2))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV 
                                     READ-DATA-WORD-UNIV 
                                     WORD-AD-TO-BYTE-ADS
                                     ACL2::EQUAL-LOGAPP-X-Y-Z
                                     WR==R!
                                     clear-data-word-univ
                                     ))))


;;
;; Multiple word ops
;;


(defun addresses-of-data-words-univ (numwords word-ad)
  (declare (type integer word-ad)
           (type (integer 0 *) numwords))
  (word-ads-to-byte-ads ;;(logext-list 31 (offset-range-wrap 31 word-ad numwords))
   (loghead-list 31 (offset-range-wrap 31 word-ad numwords)) ;bzo drop the loghead-list 31 call? and similar stuff elsewhere!
   )
  )

(defthm address-listp-of-append
  (equal (address-listp (append x y) ram)
         (and (address-listp x ram)
              (address-listp y ram))))

(defthm address-listp-of-word-ads-to-byte-ads
  (implies (and (equal (mem::size ram) 4294967296)
                (unsigned-byte-p-list 31 word-ads))
           (address-listp (WORD-ADS-TO-BYTE-ADS word-ads) ram))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

;; Read NUMWORDS words of data from RAM, starting at word address AD.  (RAM is
;; byte-addressable, so we have to shift WORD-AD to the left one bit.)  Data
;; from the lower addresses goes into the lower-order positions of the result.
;; No wrapping is done.
;;

;word-ad is a usb31?
(defund read-data-words-univ (numwords word-ad ram)
  (declare (type (integer 0 *) numwords) ;trying...;(type (integer 0 *) numwords); (type (integer 0 *) numwords)
           (type integer word-ad)
           (xargs :guard (aamp-ramp ram))
;           (type (unsigned-byte 31) word-ad)
           ;;            (xargs :guard-hints (("Goal" :expand  ((offset-range-wrap offset 2)
           ;;                                                   (offset-range-wrap offset numwords))
           ;;                                  :induct t
           ;;                                  :do-not '(generalize eliminate-destructors)
           ;;                                  :in-theory (e/d (word-ad-to-byte-ads
           ;;                                                   ACL2::SUM-WITH-SHIFT-BECOMES-LOGAPP-CONSTANT-VERSION
           ;;                                                   read-data-word-exec
           ;;                                                   acl2::logext-logapp
           ;;                                                   acl2::ash-as-logapp
           ;;                                                   read-data-words-exec) 
           ;;                                                  (acl2::logapp-0-part-2-better
           ;;                                                   acl2::loghead-sum-split-into-2-when-i-is-a-constant)))))
           )
;  (mbe :exec (read-data-words-exec numwords denvr offset ram)
;      :logic
  (wintlist (rd-list (addresses-of-data-words-univ numwords word-ad)
                     ram))
;)
  )

;bzo move
(defthm read-data-words-univ-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (read-data-words-univ numwords ad ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

(defthm read-data-words-univ-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (read-data-words-univ numwords ad ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))
       
(defthm read-data-words-univ-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (read-data-words-univ numwords ad ram)
                  (read-data-words-univ numwords 0 ram)))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

;; (defthm read-data-words-univ-of-1
;;   (equal (read-data-words-univ 1 ad ram)
;;          (rd (ifix ad) ram))
;;   :hints (("Goal" :in-theory (enable read-data-words-univ))))

;bzo instead open to multiple calls of read-data-word-univ
(defthmd read-data-words-univ-constant-opener
  (implies (syntaxp (quotep numwords))
           (equal (read-data-words-univ numwords word-ad ram)
                  (wintlist (rd-list (addresses-of-data-words-univ numwords word-ad)
                                     ram))))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

(defthm unsigned-byte-p-of-read-data-words-univ
  (implies (and (integerp numwords)
                (<= 0 numwords)
                )
           (unsigned-byte-p (* 16 numwords) (read-data-words-univ numwords ad ram)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ( (read-data-words-univ numwords ad ram))))
  :hints (("Goal" ; :cases ((integerp numwords))
           :in-theory (enable read-data-words-univ))))

(defthm unsigned-byte-p-of-read-data-words-univ-gen
  (implies (and (<= (* 16 numwords) n)
                (integerp n)
                (<= 0 n)
                (integerp numwords)
                (<= 0 numwords)
                )
           (unsigned-byte-p n (read-data-words-univ numwords ad ram))))

;bzo put these back!
;; ;bzo gen the 8
;; (defthm loghead8-of-read-data-words-univ
;;   (implies (integerp ad) ;bzo
;;            (equal (LOGHEAD 8 (READ-DATA-WORDS-UNIV numwords ad ram))
;;                   (if (and (integerp numwords)
;;                            (< 0 numwords))
;;                       (rd ad ram)
;;                     0)))
;;   :hints (("Goal" :in-theory (enable READ-DATA-WORDS-UNIV))))

;; (defthm logtail8-of-read-data-words-univ
;;   (implies (integerp ad) ;bzo use ifix!
;;            (equal (LOGtail 8 (READ-DATA-WORDS-UNIV numwords ad ram))
;;                   (if (and (integerp numwords)
;;                            (< 0 numwords))
;;                        (READ-DATA-WORDS-UNIV (+ -1 numwords) (+ 1 ad) ram)
;;                     0)))
;;   :hints (("Goal" :in-theory (enable READ-DATA-WORDS-UNIV))))


;; (defthm read-data-words-univ-when-numwords-is-non-negative
;;   (implies (<= numwords 0)
;;            (equal (read-data-words-univ numwords ad ram)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable read-data-words-univ))))







;;
;; WR-BYTES
;;
;;bzo add mbe          

(defund write-data-words-univ (numwords word-ad value ram)
  (declare (type integer word-ad value)
           (type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram))
           )
  (wr-list (addresses-of-data-words-univ numwords word-ad) 
           ;;(logext-list 32 (word-ads-to-byte-ads (addr-range word-ad numwords)))
;           (word-list-to-byte-list (split-into-words numwords value))
           (enlistw (* 2 numwords) value)
           ram))

(defthm write-data-words-univ-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (write-data-words-univ numwords ad value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (write-data-words-univ numwords ad v ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (write-data-words-univ numwords ad v ram)
                  (write-data-words-univ numwords 0 v ram)))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-of-write-data-words-univ-same
  (equal (write-data-words-univ numwords ad v1 (write-data-words-univ numwords ad v2 ram))
         (write-data-words-univ numwords ad v1 ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

;is this the best way to phrase the hyp?
;use offset-range-wrap with a size of 32?
;say that the 2 starting ads are usb 31s?
;bzo hyp
(defthm write-data-words-univ-of-write-data-words-univ-diff
  (implies (disjoint (offset-range-wrap 31 (ifix ad1) numwords1)
                     (offset-range-wrap 31 (ifix ad2) numwords2))
           (equal (write-data-words-univ numwords1 ad1 v1 (write-data-words-univ numwords2 ad2 v2 ram))
                  (write-data-words-univ numwords2 ad2 v2 (write-data-words-univ numwords1 ad1 v1 ram))))
  :hints (("Goal" :in-theory (e/d (write-data-words-univ) 
                                  (DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                    disjoint-of-word-ads-to-byte-ads
                                    disjoint-of-two-addr-ranges)))))


;;
;; lemmas about READ-DATA-WORDS-UNIV and WRITE-DATA-WORDS-UNIV together
;;

(local (in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))

(DEFTHMd ACL2::ASH-LOGHEAD
  (IMPLIES (AND (< 0 ACL2::M)
                (INTEGERP ACL2::N)
                (INTEGERP ACL2::X)
                (INTEGERP ACL2::M)
                (< 0 ACL2::N)
                (< 0 (+ ACL2::N ACL2::M)))
           (EQUAL (ASH (LOGHEAD ACL2::N ACL2::X) ACL2::M)
                  (LOGhead (+ ACL2::N ACL2::M)
                          (ASH ACL2::X ACL2::M))))
  :HINTS (("goal" :IN-THEORY (ENABLE ACL2::LRDT))))

(theory-invariant (incompatible (:rewrite ACL2::LOGHEAD-ASH-POS-REWRITE) (:rewrite ACL2::ASH-LOGHEAD)))

(encapsulate
 ()

 (local (defun induct-fun (ad numwords v)
          (if (zp numwords)
              (list ad numwords v)
            (induct-fun (+ 1 ad) (+ -1 numwords) (acl2::logtail 16 v)))))

 (local (defthm read-data-words-univ-of-write-data-words-univ-same-helper
          (implies (and (integerp ad)
                        (<= NUMWORDS 2147483648))
                   (equal (read-data-words-univ numwords ad (write-data-words-univ numwords ad v ram))
                          (acl2::loghead (* 16 (ifix numwords)) v)))
          :hints (("Goal" :expand (OFFSET-RANGE-WRAP 31 AD NUMWORDS)
                   :do-not '(generalize eliminate-destructors)
                   :in-theory (e/d (ENLISTW read-data-words-univ write-data-words-univ 
                                      WORD-AD-TO-BYTE-ADS
                                      rd-list ;bzo
                                      LOGHEAD-LIST-32-OF-WORD-ADS-TO-BYTE-ADS
                                             
                                      ) (WORD-ADS-TO-BYTE-ADS-OF-LOGHEAD-LIST))
;                   :induct (induct-fun ad numwords v)
                   ))))

;variations on this...
 (defthm read-data-words-univ-of-write-data-words-univ-same
   (implies (<= NUMWORDS 2147483648)
            (equal (read-data-words-univ numwords ad (write-data-words-univ numwords ad v ram))
                   (acl2::loghead (* 16 (ifix numwords)) v)))
   :hints (("Goal" :use (:instance read-data-words-univ-of-write-data-words-univ-same-helper (ad (ifix ad)))
            :in-theory (e/d (;LOGHEAD-LIST-32-OF-WORD-ADS-TO-BYTE-ADS
                             )
                            (read-data-words-univ-of-write-data-words-univ-same-helper))))))

;; ;bzo generalize  to subbagp?
;; (defthm write-data-words-univ-of-write-data-words-univ-same
;;   (implies (bag::subbagp (addr-range ad2 numwords2) (addr-range ad1 numwords1))
;;            (equal (write-data-words-univ numwords1 ad1 v1 (write-data-words-univ numwords2 ad2 v2 ram))
;;                   (write-data-words-univ numwords1 ad1 v1 ram)))
;;   :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-of-what-was-already-there
  (implies (and (equal (loghead (* 16 numwords) v) (read-data-words-univ numwords ad ram))
;                (integerp ad)
                (integerp numwords)
                (<= 0 numwords)
                )
           (equal (write-data-words-univ numwords ad v ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ read-data-words-univ))))

(defthm write-data-words-univ-of-what-was-already-there-cheap
  (implies (and (integerp numwords)
                (<= 0 numwords))
           (equal (write-data-words-univ numwords ad (read-data-words-univ numwords ad ram) ram)
                  ram))
  :otf-flg t
  :hints (("Goal" :use (:instance  write-data-words-univ-of-what-was-already-there (v  (read-data-words-univ numwords ad ram)))
           :in-theory (disable  write-data-words-univ-of-what-was-already-there))))

(defthm read-data-words-univ-of-write-data-words-univ-diff
  (implies (bag::disjoint (offset-range-wrap 31 ad1 numwords1)
                          (offset-range-wrap 31 ad2 numwords2))
           (equal (read-data-words-univ numwords1 ad1 (write-data-words-univ numwords2 ad2 v2 ram))
                  (read-data-words-univ numwords1 ad1 ram)))
  :hints (("Goal" :in-theory (e/d (write-data-words-univ read-data-words-univ) 
                                  (disjoint-of-word-ads-to-byte-ads
                                   DISJOINT-OF-TWO-ADDR-RANGES)))))

;make a clear-data-word-univ
;;
;; CLEAR-DATA-WORDS-UNIV
;;

(defund clear-data-words-univ (numwords word-ad ram)
  (declare (type integer word-ad)
           (type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram)))
  (write-data-words-univ numwords word-ad 0 ram))

;; (defthm clear-data-words-univ-of-1
;;   (equal (clear-data-words-univ 1 ad ram)
;;          (clr (ifix ad) ram))
;;   :hints (("Goal" :in-theory (enable clear-data-words-univ))))

(defthm write-data-words-univ-equal-rewrite
  (implies (<= NUMWORDS 2147483648)
           (equal (equal (write-data-words-univ numwords ad v ram1) ram2)
                  (if (integerp numwords)
                      (and (equal (loghead (* 16 numwords) v) 
                                  (read-data-words-univ numwords ad ram2))
                           (equal (clear-data-words-univ numwords ad ram1)
                                  (clear-data-words-univ numwords ad ram2)))
                    (equal ram1 ram2))))
  :hints (("Goal" :in-theory (enable write-data-words-univ read-data-words-univ clear-data-words-univ))))
                 
;; (defthm clear-data-words-univ-of-wr-cover
;;   (implies (list::memberp ad (addr-range ad2 numwords))
;;            (equal (clear-data-words-univ numwords ad2 (wr ad val ram))
;;                   (clear-data-words-univ numwords ad2 ram)))
;;   :hints (("Goal" :in-theory (enable clear-data-words-univ))))

  
;; ;replacement for rx, except when numwords is 0?
;; (defun rx2 (size a ram)
;;   (read-data-words-univ (* 1/8 (fix-size numwords) ad ram)))


;; (defthm helper
;;   (implies (equal (wr-list ads vals ram1) ram2)
;;            (equal (clr-list ads ram1)
;;                   (clr-list ads ram2))))

;; (defthmd helper2
;;   (implies (equal (wr-list ads vals2 ram1) ram2)
;;            (equal (wr-list ads vals ram1)
;;                   (wr-list ads vals ram2))))

;; (defthmd helper3
;;   (implies (and (equal (wr-list ads0 vals2 ram1) ram2)
;;                 (subbagp ads0 ads))
;;            (equal (wr-list ads vals ram1)
;;                   (wr-list ads vals ram2))))

;; (defthmd helper-blah
;;   (implies (and (equal ram3 ram4)
;;                 (equal (rd ad ram1) (rd ad ram3))
;;                 (equal (rd ad ram2) (rd ad ram4))
;;                 )
;;            (equal (rd ad ram1) (rd ad ram2))))

;; (defthmd helper-blah2
;;   (implies (and (equal ram3 ram4)
;;                 (equal (rd ad ram1) (rd ad ram3))
;;                 (equal (rd ad ram2) (rd ad ram3))
;;                 )
;;            (equal (rd ad ram1) (rd ad ram2))))

;; (defthm memberp-hacl
;;   (IMPLIES (AND (CONSP ADS)
;;                 (NOT (MEMBERP AD ADS)))
;;            (not (equal ad (car ads)))
;;            ))

;; (defthm memberp-hacl2
;;   (IMPLIES (AND (CONSP ADS)
;;                 (NOT (MEMBERP AD ADS)))
;;            (not (memberp ad (cdr ads)))
;;            ))

;; (defthm fw2
;;   (implies t ;(unique ads)
;;            (implies (equal (wr-list ads vals ram1) ram2)
;;                     (equal (clr-list ads ram1)
;;                            (clr-list ads ram2))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (CLR-LIST ADS RAM1)
;;            :in-theory (enable wfixlist WR==R!))))



;; ;not true if list of ads isn't unique!
;; (defthm fw1
;;  (implies (unique ads)
;;           (implies (equal (wr-list ads vals ram1) ram2)
;;                    (equal (my-wfixlist (len ads) vals) (rd-list ads ram2))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;          :expand (CLR-LIST ADS RAM1)
;;           :in-theory (enable wfixlist WR==R!))))


;; (defthm wr-list-when-ads-is-not-a-consp
;;   (implies (not (consp ads))
;;            (equal (wr-list ads vals ram)
;;                   ram)))


;; (defun ind (ads v1 v2 ram1 ram2)
;;   (if (endp ads)
;;       (list ads v1 v2 ram1 ram2)
;;     (ind (cdr ads) (cdr v1) (cdr v2) (wr (car ads) (car v1) ram1) (wr (car ads) (car v2) ram2))))


;; bk;
;; (thm
;;  (implies (unique ads) ;necessary?
;;           (implies (and (equal (my-wfixlist (len ads) vals) (rd-list ads ram2))
;;                         (equal (clr-list ads ram1)
;;                                (clr-list ads ram2)))
;;                    (equal (wr-list ads vals ram1) ram2)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :expand (CLR-LIST ADS RAM1)
;;           :do-not-induct t
;; ;          :induct  (wr-list ads vals ram1)
;;           :in-theory (enable wfixlist WR==R!))))


;; (thm
;;  (implies (not (integerp ad))
;;           (equal (RD AD RAM)
;;                  (RD 0 RAM)))
;;  :hints (("Goal" :in-theory (enable rd))))

(defthmd write-data-words-univ-opener
  (implies (and (syntaxp (quotep numwords))
                (not (zp numwords)))
           (equal (write-data-words-univ numwords ad value ram)
                  (write-data-word-univ ad (loghead 16 value)
                                   (write-data-words-univ (+ -1 numwords) (+ 1 (ifix ad)) (logtail 16 value)
                                                          ram))))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 31 ad NUMWORDS)
                           (OFFSET-RANGE-WRAP 31 0 NUMWORDS))
           :in-theory (e/d (write-data-words-univ write-data-word-univ
                                             WORD-AD-TO-BYTE-ADS) 
                           ( ;makeaddr-of-+-loghead
                            )))))

(defthmd read-data-words-univ-opener
  (implies (and (syntaxp (quotep numwords))
                (not (zp numwords)))
           (equal (read-data-words-univ numwords ad ram)
                  (logapp 16 
                          (read-data-word-univ ad ram)
                          (read-data-words-univ (+ -1 numwords)
                                                (+ 1 (ifix ad))
                                           ram))))
  :hints
  (("Goal" :expand ((OFFSET-RANGE-WRAP 31 ad NUMWORDS)
                    (OFFSET-RANGE-WRAP 31 0 NUMWORDS))
    :in-theory
    (e/d (READ-DATA-WORD-univ
          read-data-words-univ
          WORD-AD-TO-BYTE-ADS
          OFFSET-RANGE-WRAP-CONST-OPENER
          ACL2::ASH-AS-LOGAPP
          ACL2::LOGEXT-LOGAPP)
         ( ;makeaddr-of-+-loghead
          ACL2::LOGAPP-0-PART-2-BETTER
          ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
          )))))


;; Lemmas mixing the ram3 primitives and the ram2 primitives (where should these go?):

;; Primitives (assuming we split all multi-word operations into repeated calls to single word operations):

;; "reads":
;; read-data-word
;; read-data-word-univ
;; fetch-code-byte

;; "writes":
;; write-data-word
;; write-data-word-univ

;; "clears":
;; clear-data-word
;; clear-data-word-univ


(theory-invariant (incompatible (:rewrite ACL2::LOGHEAD-LOGCDR) (:rewrite ACL2::LOGCDR-loghead)))

;rephrase hyp?
(defthm fetch-code-byte-of-write-data-word-univ
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word-univ ad)))
           ;;(not (equal (acl2::logcdr (loghead 16 cenvr)) (logtail 16 (loghead 31 ad))))
           (equal (fetch-code-byte cenvr offset (write-data-word-univ ad val ram))
                  (fetch-code-byte cenvr offset ram)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word 
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash) 
                           (addresses-of-data-word-univ
                            make-code-addr
                            acl2::logcdr-loghead)))))

;rephrase hyp?
(defthm read-data-word-of-write-data-word-univ
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word denvr offset (write-data-word-univ ad val ram))
                  (read-data-word denvr offset ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word 
                            read-data-word
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash) 
                           (addresses-of-data-word-univ
                            addresses-of-data-word
                            make-code-addr
                            acl2::logcdr-loghead)))))

;rephrase hyp?
(defthm read-data-word-univ-of-write-data-word
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word-univ ad (write-data-word denvr offset val ram))
                  (read-data-word-univ ad ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word 
                            read-data-word-univ
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash) 
                           (addresses-of-data-word-univ
                            addresses-of-data-word
                            make-code-addr
                            acl2::logcdr-loghead)))))


;; We move the universal writes inside the regular writes (since regular
;; writes include writes to the stack and locals, we expect them to be more
;; common than universal writes, so we want to make the more "exposed" by
;; brining them to the outside of the nest of writes.
;;
;;rephrase hyp?
(defthm write-data-word-univ-of-write-data-word
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (write-data-word-univ ad val1 (write-data-word denvr offset val2 ram))
                  (write-data-word denvr offset val2 (write-data-word-univ ad val1 ram))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word 
                            read-data-word-univ
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash) 
                           (addresses-of-data-word-univ
                            addresses-of-data-word
                            make-code-addr
                            acl2::logcdr-loghead)))))

;; We leave this disabled, in favor of write-data-word-univ-of-write-data-word.
;;
;;rephrase hyp?
(defthmd write-data-word-of-write-data-word-univ
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (write-data-word denvr offset val2 (write-data-word-univ ad val1 ram))
                  (write-data-word-univ ad val1 (write-data-word denvr offset val2 ram))))
  :hints (("Goal" :use (:instance write-data-word-univ-of-write-data-word)
           :in-theory (disable write-data-word-univ-of-write-data-word))))

(theory-invariant (incompatible (:rewrite write-data-word-univ-of-write-data-word) 
                                (:rewrite write-data-word-of-write-data-word-univ)))


;; "read of clear" lemmas

(defthmd read-data-word-univ-of-clear-data-word-univ-same
  (implies (equal (loghead 31 ad1) (loghead 31 ad2))
           (equal (read-data-word-univ ad1 (clear-data-word-univ ad2 ram))
                  0))
  :hints (("Goal" :in-theory (enable clear-data-word-univ
                                     READ-DATA-WORD-UNIV-OF-WRITE-DATA-WORD-UNIV-SAME ;bzo
                                     ))))

(defthm read-data-word-univ-of-clear-data-word-univ-same-cheap
  (equal (read-data-word-univ ad (clear-data-word-univ ad ram))
         0)
  :hints (("Goal" :in-theory (enable clear-data-word-univ
                                     READ-DATA-WORD-UNIV-OF-WRITE-DATA-WORD-UNIV-SAME ;bzo
                                     ))))

;rewrite the hyp to a claim about logheads?
(defthm read-data-word-univ-of-clear-data-word-univ-diff
  (implies (bag::disjoint (addresses-of-data-word-univ ad2)
                          (addresses-of-data-word-univ ad1))
           (equal (read-data-word-univ ad1 (clear-data-word-univ ad2 ram))
                  (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-word-univ))))

(defthmd read-data-word-univ-of-clear-data-word-univ-both
  (equal (read-data-word-univ ad1 (clear-data-word-univ ad2 ram))
         (if (equal (loghead 31 ad1) (loghead 31 ad2))
             0
           (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-word-univ
                                     read-data-word-univ-of-write-data-word-univ-both))))



;;lemmas about clear-data-word-univ

(defthm fetch-code-byte-of-clear-data-word-univ
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word-univ ad)))
           ;;(not (equal (acl2::logcdr (loghead 16 cenvr)) (logtail 16 (loghead 31 ad))))
           (equal (fetch-code-byte cenvr offset (clear-data-word-univ ad ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (enable clear-data-word-univ))))

;rephrase hyp?
(defthm read-data-word-of-clear-data-word-univ
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word denvr offset (clear-data-word-univ ad ram))
                  (read-data-word denvr offset ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word-univ) 
                                  (DISJOINT-OF-TWO-WORD-AD-TO-BYTE-ADS ;bzo
                                   )))))

(defthm read-data-word-univ-of-clear-data-word
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word-univ ad (clear-data-word denvr offset ram))
                  (read-data-word-univ ad ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) 
                                  (DISJOINT-OF-TWO-WORD-AD-TO-BYTE-ADS ;bzo
                                   WRITE-DATA-WORD-EQUAL-REWRITE)
                                   ))))

(defthm read-data-words-univ-of-logext-special-case 
  (equal (gacc::read-data-words-univ 2 (logext 32 x) ram)
         (gacc::read-data-words-univ 2 x ram))
  :hints (("Goal" :in-theory (enable gacc::read-data-words-univ))))

(defthm read-data-word-univ-of-logext
  (equal (gacc::read-data-word-univ (logext 32 word-ad) ram)
         (gacc::read-data-word-univ word-ad ram))
  :hints (("Goal" :in-theory (enable gacc::read-data-word-univ))))

(defthm write-data-word-univ-of-logext
  (equal (gacc::write-data-word-univ (logext 32 word-ad) val ram)
         (gacc::write-data-word-univ word-ad val ram))
  :hints (("Goal" :in-theory (enable gacc::write-data-word-univ))))

(defthmd addresses-of-data-words-univ-constant-opener
  (implies (and (syntaxp (quotep numwords))
                (integerp numwords)
                (< 0 numwords)
                (integerp word-ad))
           (equal (gacc::addresses-of-data-words-univ numwords word-ad)
                  (append (gacc::addresses-of-data-word-univ word-ad)
                          (gacc::addresses-of-data-words-univ (+ -1 numwords) (+ 1 word-ad)))))
  :hints (("Goal" :expand (gacc::word-ads-to-byte-ads (gacc::offset-range-wrap 31 word-ad numwords))
           :in-theory (enable gacc::word-ads-to-byte-ads))))

;bzo gen
(defthm write-data-words-univ-2-of-logext
 (equal (gacc::write-data-words-univ 2 (logext 32 ad) val ram)
        (gacc::write-data-words-univ 2 ad val ram))
 :hints (("Goal" :in-theory (enable gacc::write-data-words-univ))))

;bzo gen
(defthm write-data-words-univ-2-of-logext-around-vale
 (equal (gacc::write-data-words-univ 2 ad (logext 32 val) ram)
        (gacc::write-data-words-univ 2 ad val ram))
 :hints (("Goal" :in-theory (enable gacc::write-data-words-univ))))

(defthm addresses-of-data-words-univ-of-0
  (equal (gacc::addresses-of-data-words-univ 0 word-ad)
         nil))

(defthm read-data-words-univ-of-1
  (equal (gacc::read-data-words-univ 1 gacc::word-ad gacc::ram)
         (gacc::read-data-word-univ gacc::word-ad gacc::ram))
  :hints (("Goal" :in-theory (enable gacc::read-data-words-univ-opener))))
