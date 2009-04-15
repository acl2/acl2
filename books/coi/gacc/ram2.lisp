#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

(include-book "list-ops-fast")
(include-book "addr-range") ;bzo drop?
(include-book "wrap")
(local (include-book "rtl/rel4/arithmetic/fl" :dir :system))

;(local (include-book "loglist" :dir :super-ihs)) ;bzo
(local (include-book "super-ihs" :dir :super-ihs)) ;bzo

(local (in-theory (enable zp)))

;bzo move
(defthm nthcdr-of-1
  (equal (nthcdr 1 x)
         (cdr x)))

;bbzo dup
(defun aamp-ramp (ram)
  (declare (type t ram))
  (and (ramp ram)
       (equal (mem::size ram) (expt 2 32))))


;; For execution only.
;; We could reorder things to put the most common cases first..
;; Would the logapp nests be faster if they were expressed instead in terms of + and ash?
;; Add in type declarations (since the common cases fit in 32 bits).
;rename
;make tail recursive!
;does this wrap?
(defun rd-bytes-exec (numbytes ad ram)
  (declare (type (integer 0 *) numbytes)
           (type integer ad) ;weaken
           (xargs :guard (and (aamp-ramp ram)
                              ;(address-listp (addr-range ad numbytes) ram)
                              )
                  :guard-hints (("Goal" :in-theory (enable ADDR-RANGE-EXPAND-WHEN-K-IS-A-CONSTANT)))
                  )
           )
  (if (zp numbytes)
      0
    (if (equal 1 numbytes)
        (rd (loghead 32 ad) ram)
      (if (equal 2 numbytes)
          (acl2::logapp 8 
                        (rd (loghead 32 ad) ;bzo i added these logheads...
                            ram) 
                        (rd (loghead 32 (+ 1 ad)) ram)
                        ) ;bzo
        (if (equal 4 numbytes)
            ;bzo reassociate the logapp?
            (acl2::logapp 24
                          (acl2::logapp 16
                                        (acl2::logapp 8 
                                                      (rd (loghead 32 ad) ram) 
                                                      (rd (loghead 32 (+ 1 ad)) ram))
                                        (rd (loghead 32 (+ 2 ad)) ram))
                          (rd (loghead 32 (+ 3 ad)) ram))
          (acl2::logapp 8 (rd (loghead 32 ad) ram) (rd-bytes-exec (+ -1 numbytes) (+ 1 ad) ram)))))))
  

;; Read NUMBYTES bytes of data from RAM, starting at address AD.  (RAM is
;; byte-addressable.)  Data from the lower addresses goes into the lower-order
;; positions of the result.
;;

(defund rd-bytes (numbytes ad ram)
  (declare (type integer ad)
           (type (integer 0 *) numbytes)
           (xargs  :guard (and (aamp-ramp ram)
                               ;(address-listp (addr-range ad numbytes) ram)
                               )
                   :guard-hints (("Goal" :in-theory (enable OFFSET-RANGE-WRAP-CONST-OPENER
                                                            ADDR-RANGE-EXPAND-WHEN-K-IS-A-CONSTANT))))
           )
  (mbe :exec (rd-bytes-exec numbytes ad ram)
       :logic (wintlist (rd-list ;;(addr-range ad numbytes)
                         (offset-range-wrap 32 ad numbytes) ;Bbzo eric made these changes - are they ok?
                         ram))))

(defthm rd-bytes-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (rd-bytes numbytes ad ram)
                  (rd-bytes numbytes 0 ram)))
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthm rd-bytes-of-1
  (equal (rd-bytes 1 ad ram)
         ;;(rd (ifix ad) ram)
         (rd (loghead 32 ad) ram)
         )
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthmd rd-bytes-constant-opener
  (implies (syntaxp (quotep numbytes))
           (equal (rd-bytes numbytes ad ram)
                  (wintlist
                   (rd-list (offset-range-wrap 32 ad numbytes) ;;(addr-range ad numbytes)
                            ram))))
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthm unsigned-byte-p-of-rd-bytes
  (implies (and (integerp numbytes)
                (<= 0 numbytes)
                )
           (unsigned-byte-p (* 8 numbytes) (rd-bytes numbytes ad ram)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ( (rd-bytes numbytes ad ram))))
  :hints (("Goal" ; :cases ((integerp numbytes))
           :in-theory (enable rd-bytes))))

(defthm unsigned-byte-p-if-rd-bytes-gen
  (implies (and (<= (* 8 numbytes) n)
                (integerp n)
                (<= 0 n)
                (integerp numbytes)
                (<= 0 numbytes)
                )
           (unsigned-byte-p n (rd-bytes numbytes ad ram))))

;bzo gen the 8
(defthm loghead8-of-rd-bytes
  (implies (integerp ad) ;bzo
           (equal (loghead 8 (rd-bytes numbytes ad ram))
                  (if (and (integerp numbytes)
                           (< 0 numbytes))
                      (rd (loghead 32 ad)
                          ram)
                    0)))
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthm logtail8-of-rd-bytes
  (implies (integerp ad) ;bzo use ifix!
           (equal (LOGtail 8 (RD-BYTES numbytes ad ram))
                  (if (and (integerp numbytes)
                           (< 0 numbytes))
                       (RD-BYTES (+ -1 numbytes) (+ 1 ad) ram)
                    0)))
  :hints (("Goal" :in-theory (enable RD-BYTES))))


;; (defthm rd-bytes-when-numbytes-is-non-negative
;;   (implies (<= numbytes 0)
;;            (equal (rd-bytes numbytes ad ram)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable rd-bytes))))

(defun unsigned-byte-p-list (size vals)
  (if (endp vals)
      t
    (and (unsigned-byte-p size (car vals))
         (unsigned-byte-p-list size (cdr vals)))))

(defthm address-listp-rewrite
  (implies (and (mem::memory-p ram)
                (equal (mem::size ram) 4294967296))
           (equal (address-listp ad-list ram)
                  (unsigned-byte-p-list 32 ad-list))))

(defthm unsigned-byte-p-list-of-offset-range-wrap
  (implies (natp n)
           (unsigned-byte-p-list n (offset-range-wrap n ad numbytes)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-list offset-range-wrap))))


;;
;; WR-BYTES
;;
;;bzo add mbe          

(defund wr-bytes (numbytes ad v ram)
  (declare (type t ad ram)
           (type integer v)
           (type (integer 0 *) numbytes)
           (xargs  :guard (and (aamp-ramp ram)
                               (integerp ad) ;bzo did i really need this?
                               ;(address-listp (addr-range ad numbytes) ram)
                               )
                   :guard-hints (("Goal" :in-theory (enable OFFSET-RANGE-WRAP-CONST-OPENER
                                                            ADDR-RANGE-EXPAND-WHEN-K-IS-A-CONSTANT)))))
  (wr-list (offset-range-wrap 32 ad numbytes) ;(addr-range ad numbytes) 
           (enlistw numbytes v) ram))

(defthm wr-bytes-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (wr-bytes numbytes ad v ram)
                  (wr-bytes numbytes 0 v ram)))
  :hints (("Goal" :in-theory (enable wr-bytes))))

(defthm wr-bytes-of-wr-bytes-same
  (equal (wr-bytes numbytes ad v1 (wr-bytes numbytes ad v2 ram))
         (wr-bytes numbytes ad v1 ram))
  :hints (("Goal" :in-theory (enable wr-bytes))))

;is this the best way to phrase the hyp?
(defthm wr-bytes-of-wr-bytes-diff
  (implies (bag::disjoint (offset-range-wrap 32 ad1 numbytes1) ;;(addr-range ad1 numbytes1)
                          (offset-range-wrap 32 ad2 numbytes2) ;;(addr-range ad2 numbytes2)
                          )
           (equal (wr-bytes numbytes1 ad1 v1 (wr-bytes numbytes2 ad2 v2 ram))
                  (wr-bytes numbytes2 ad2 v2 (wr-bytes numbytes1 ad1 v1 ram))))
  :hints (("Goal" :in-theory (e/d (wr-bytes) (DISJOINT-OF-TWO-ADDR-RANGES)))))


;;
;; lemmas about RD-BYTES and WR-BYTES together
;;

;; (encapsulate
;;  ()

;; ;;  (local (defun induct-fun (ad numbytes v)
;; ;;           (if (zp numbytes)
;; ;;               (list ad numbytes v)
;; ;;             (induct-fun (+ 1 ad) (+ -1 numbytes) (acl2::logtail 8 v)))))

;;  (local (defun induct-fun (ad numbytes v)
;;           (if (zp numbytes)
;;               (list ad numbytes v)
;;             (induct-fun (loghead 32 (+ 1 ad)) (+ -1 numbytes) (acl2::logtail 8 v)))))


;;  (local (defthm rd-bytes-of-wr-bytes-same-helper
;;           (implies (integerp ad)
;;                    (equal (rd-bytes numbytes ad (wr-bytes numbytes ad v ram))
;;                           (acl2::loghead (* 8 (ifix numbytes)) v)))
;;           :hints (("Goal" :in-theory (enable ENLISTW rd-bytes wr-bytes 
;;                                              rd-list ;bzo
;;                                              )
;;                    ;:induct (induct-fun ad numbytes v)
;;                    ))))

;;  ;; variations on this...
;;  (defthm rd-bytes-of-wr-bytes-same
;;    (implies (force (< numbytes (expt 2 32))) ;bzo added this for convenience when changing to fast-memories (could possibly be dropped...)
;;             (equal (rd-bytes numbytes ad (wr-bytes numbytes ad v ram))
;;                    (acl2::loghead (* 8 (ifix numbytes)) v)))
;;    :hints (("Goal" :use (:instance rd-bytes-of-wr-bytes-same-helper (ad (ifix ad)))
;;             :in-theory (disable rd-bytes-of-wr-bytes-same-helper)))))


(defthm rd-bytes-of-wr-bytes-same
  (implies (force (< numbytes (expt 2 32))) ;bzo added this when changing to fast-memories
           (equal (rd-bytes numbytes ad (wr-bytes numbytes ad v ram))
                  (acl2::loghead (* 8 (ifix numbytes)) v)))
  :hints (("Goal" :in-theory (enable RD-BYTES wr-bytes))))

;; ;bzo generalize  to subbagp?
;; (defthm wr-bytes-of-wr-bytes-same
;;   (implies (bag::subbagp (addr-range ad2 numbytes2) (addr-range ad1 numbytes1))
;;            (equal (wr-bytes numbytes1 ad1 v1 (wr-bytes numbytes2 ad2 v2 ram))
;;                   (wr-bytes numbytes1 ad1 v1 ram)))
;;   :hints (("Goal" :in-theory (enable wr-bytes))))

(defthm wr-bytes-of-what-was-already-there
  (implies (and (equal (loghead (* 8 numbytes) v) (rd-bytes numbytes ad ram))
;                (integerp ad)
                (integerp numbytes)
                (<= 0 numbytes)
                )
           (equal (wr-bytes numbytes ad v ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-bytes rd-bytes))))

(defthm wr-bytes-of-what-was-already-there-cheap
  (implies (force (< numbytes (expt 2 32))) ;bzo added this when changing to fast-memories
           (equal (wr-bytes numbytes ad (rd-bytes numbytes ad ram) ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-bytes rd-bytes))))

(defthm rd-bytes-of-wr-bytes-diff
  (implies (bag::disjoint (offset-range-wrap 32 ad1 numbytes1) ;;(addr-range ad1 numbytes1)
                          (offset-range-wrap 32 ad2 numbytes2) ;;(addr-range ad2 numbytes2)
                          )
           ;; (bag::disjoint (addr-range ad1 numbytes1)
;;                           (addr-range ad2 numbytes2)
;;                           )
           (equal (rd-bytes numbytes1 ad1 (wr-bytes numbytes2 ad2 v2 ram))
                  (rd-bytes numbytes1 ad1 ram)))
  :hints (("Goal" :in-theory (e/d (wr-bytes rd-bytes) (DISJOINT-OF-TWO-ADDR-RANGES)))))

;;
;; CLR-BYTES
;;

;or should this call wr-bytes with 0?
(defund clr-bytes (numbytes ad ram)
  (clr-list ;;(addr-range ad numbytes)
   (offset-range-wrap 32 ad numbytes)
   ram))

(defthm clr-bytes-of-1
  (equal (clr-bytes 1 ad ram)
         (memory-clr ;(ifix ad)
          (loghead 32 ad)
          ram))
  :hints (("Goal" :in-theory (enable clr-bytes))))

(defthm wr-bytes-equal-rewrite
  (implies (force (< numbytes (expt 2 32))) ;bzo added this when changing to fast-memories
           (equal (equal (wr-bytes numbytes ad v ram1) ram2)
                  (if (integerp numbytes)
                      (and (equal (loghead (* 8 numbytes) v) 
                                  (rd-bytes numbytes ad ram2))
                           (equal (clr-bytes numbytes ad ram1)
                                  (clr-bytes numbytes ad ram2)))
                    (equal ram1 ram2))))
  :hints (("Goal" :in-theory (enable wr-bytes rd-bytes clr-bytes))))

;kill?
;; (defthm clr-list-of-wr-cover
;;   (implies (list::memberp ad ads)
;;            (equal (clr-list ads (wr ad val ram))
;;                   (clr-list ads ram)))
;;   :hints (("Goal" :in-theory (enable clr-list))))
                 
(defthm clr-bytes-of-wr-cover
  (implies (list::memberp ad (offset-range-wrap 32 ad2 numbytes) ;;(addr-range ad2 numbytes)
                          )
           (equal (clr-bytes numbytes ad2 (wr ad val ram))
                  (clr-bytes numbytes ad2 ram)))
  :hints (("Goal" :in-theory (enable clr-bytes))))

  
;; ;replacement for rx, except when numbytes is 0?
;; (defun rx2 (size a ram)
;;   (rd-bytes (* 1/8 (fix-size numbytes) ad ram)))


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

