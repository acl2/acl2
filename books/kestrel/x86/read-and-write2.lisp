; More rules about reading and writing
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; The rules in this book use the functions in disjoint.lisp, which can be
;; opened up to BV terms.

(include-book "read-and-write")
(include-book "read-bytes-and-write-bytes") ; could separate out
(include-book "kestrel/x86/regions" :dir :system)

(defthm read-byte-of-write-byte-when-disjoint-1
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (in-regionp ad1 len1 start1)
                (in-regionp ad2 len2 start2))
           (equal (read-byte ad1 (write-byte ad2 val x86))
                  (read-byte ad1 x86))))

(defthm read-byte-of-write-byte-when-disjoint-2
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (in-regionp ad2 len1 start1)
                (in-regionp ad1 len2 start2))
           (equal (read-byte ad1 (write-byte ad2 val x86))
                  (read-byte ad1 x86))))

(defthm read-byte-of-write-when-disjoint
  (implies (and (disjoint-regionsp 1 ad1 n2 ad2)
                (< n2 (expt 2 48)) ; what if = ?
                (integerp n2)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n2 ad2 val x86))
                  (read-byte ad1 x86)))
  :hints (("Goal" :in-theory (enable disjoint-regionsp bvlt))))

(defthm read-byte-of-write-when-disjoint-alt
  (implies (and (disjoint-regionsp n2 ad2 1 ad1)
                (< n2 (expt 2 48)) ; what if = ?
                (integerp n2)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n2 ad2 val x86))
                  (read-byte ad1 x86)))
  :hints (("Goal" :use (:instance read-byte-of-write-when-disjoint)
           :in-theory (e/d (disjoint-regionsp-symmetric)
                           (read-byte-of-write-when-disjoint
                            READ-BYTE-OF-WRITE-BOTH ; for speed
                            )))))

;todo: make an alt verion
(defthm read-byte-of-write-when-disjoint-gen
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (subregionp 1 ad1 len1 start1) ; or use in-regionp?
                (subregionp n2 ad2 len2 start2)
;                (< n2 (expt 2 48)) ; what if = ?
 ;               (integerp n2)
                ;; (integerp ad1)
                ;; (integerp ad2)
                (UNSIGNED-BYTE-P '48 LEN1)
                (UNSIGNED-BYTE-P '48 LEN2)
                (UNSIGNED-BYTE-P '48 n1)
                (UNSIGNED-BYTE-P '48 n2)
                )
           (equal (read-byte ad1 (write n2 ad2 val x86))
                  (read-byte ad1 x86)))
  :hints (("Goal" :use (:instance read-byte-of-write-when-disjoint)
           :in-theory (disable read-byte-of-write-when-disjoint))))

(DEFTHM READ-BYTE-OF-WRITE-BOTH-new
  (IMPLIES (AND ;(<= N (EXPT 2 48))
                (unsigned-byte-p 48 n)
                (INTEGERP N)
                ;; (INTEGERP AD1)
                ;; (INTEGERP AD2)
                )
           (EQUAL (READ-BYTE AD1 (WRITE N AD2 VAL X86))
                  (IF (in-regionp ad1 n ad2)
                      (SLICE (+ 7 (* 8 (BVMINUS 48 AD1 AD2)))
                             (* 8 (BVMINUS 48 AD1 AD2))
                             VAL)
                    (READ-BYTE AD1 X86))))
  :hints (("Goal" :in-theory (enable in-regionp bvlt))))

(in-theory (disable READ-BYTE-OF-WRITE-BOTH))

;todo: in-regionp is subregionp of size 1

;slow
(defthm not-in-regionp-when-disjoint-regionsp
  (implies (and (disjoint-regionsp len1 start1 len2 start2)
                (in-regionp ad1 len1 start1)
                (subregionp rlen rad len2 start2)
                ;; (integerp ad1)
                ;; (integerp rad)
                ;; (integerp start1)
                ;; (integerp start2)
                (unsigned-byte-p '48 len1)
                (unsigned-byte-p '48 len2)
                (unsigned-byte-p '48 rlen))
           (not (in-regionp ad1 rlen rad)))
  :hints (("Goal" :in-theory (enable disjoint-regionsp
                                     subregionp
                                     in-regionp
                                     bvlt bvminus BVUMINUS bvplus
                                     acl2::bvchop-of-sum-cases))))

;move
(defthm subregionp-one-smaller
  (implies (and (subregionp len1 ad1 len2 ad2)
                (unsigned-byte-p 48 len1)
                (integerp ad1) ; drop?
  ;              (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 len2)
                ;(unsigned-byte-p 48 ad2)
                (integerp ad2) ; drop?
                )
           (subregionp (+ -1 len1) (+ 1 ad1) len2 ad2))
  :hints (("Goal" :in-theory (enable subregionp in-regionp
                                     bvlt bvminus BVUMINUS bvplus
                                     acl2::bvchop-of-sum-cases))))

(defthm read-of-write-when-disjoint-regionsp
  (implies (and (disjoint-regionsp n1 ad1 n2 ad2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :in-theory (enable read write))))

(defthm read-of-write-when-disjoint-regionsp-gen
  (implies (and (disjoint-regionsp len1 start1 len2 start2) ; free vars
                (subregionp n1 ad1 len1 start1)
                (subregionp n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p '48 len1)
                (unsigned-byte-p '48 len2)
                (unsigned-byte-p '48 n1)
                (unsigned-byte-p '48 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :in-theory (enable read write))))

(defthm read-of-write-when-disjoint-regionsp-gen-alt
  (implies (and (disjoint-regionsp len2 start2 len1 start1)
                (subregionp n1 ad1 len1 start1)
                (subregionp n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p '48 len1)
                (unsigned-byte-p '48 len2)
                (unsigned-byte-p '48 n1)
                (unsigned-byte-p '48 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :use (:instance read-of-write-when-disjoint-regionsp-gen)
           :in-theory '(disjoint-regionsp-symmetric))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  ;rename
  (defun double-read-induct-two-ads-two-sizes (n1 n2 ad1 ad2 x86)
    (if (zp n1)
        (list n1 n2 ad1 ad2 x86)
      (double-read-induct-two-ads-two-sizes (+ -1 n1)
                                            (+ -1 n2)
                                            (+ 1 ad1)
                                            (+ 1 ad2)
                                            x86))))


(local
  ;rename
  (defun read-induct-two-sizes (n1; n2
                                ad1 ad2 x86)
    (if (zp n1)
        (list n1 ; n2
              ad1 ad2 x86)
      (read-induct-two-sizes (+ -1 n1)
;        (+ -1 n2)
                             (+ 1 ad1)
                             (+ 1 ad2)
                             x86))))

;move
(defthm bvchop-of-+-of-bvuminus-48-arg3
  (implies (and (integerp ad3)
                (integerp ad1)
                (integerp ad2))
           (equal (bvchop 48 (+ ad1 ad2 (bvuminus 48 ad3)))
                  (bvchop 48 (+ ad1 ad2 (- ad3)))))
  :hints (("Goal" :in-theory (enable bvuminus))))

;move
(defthm bvchop-of-+-of-bvuminus-48-arg2
  (implies (and (integerp ad1)
                (integerp ad2))
           (equal (bvchop 48 (+ ad1 (bvuminus 48 ad2)))
                  (bvchop 48 (+ ad1 (- ad2)))))
  :hints (("Goal" :in-theory (enable bvuminus))))

;move
(defthm read-byte-of-+-of-bvuminus-48-arg3
  (implies (and (integerp ad3)
                (integerp ad1)
                (integerp ad2))
           (equal (read-byte (+ ad1 ad2 (bvuminus 48 ad3)) x86)
                  (read-byte (+ ad1 ad2 (- ad3)) x86)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ ad1 ad2 (bvuminus 48 ad3))))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ ad1 ad2 (- ad3)))))
           :in-theory (disable read-byte-of-bvchop-arg1
                               read-byte-equal-when-bvchops-equal))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(defthm read-of-+-of-bvuminus-2
  (implies (integerp ad1)
           (equal (read n (+ ad1 (bvuminus 48 ad2)) x86)
                  (read n (+ ad1 (- (ifix ad2))) x86)))
  :hints (("Goal" :use ((:instance read-of-bvchop-48 (addr (+ ad1 (bvuminus 48 ad2))))
                        (:instance read-of-bvchop-48 (addr (+ ad1 (- (ifix ad2))))))
           :in-theory (e/d (ifix) (read-of-bvchop-48)))))

(defthm read-of-+-of-bvchop-2
  (implies (and (integerp ad1)
                ;(integerp x)
                )
           (equal (read n (+ ad1 x (bvchop 48 ad2)) x86)
                  (read n (+ ad1 x (ifix ad2)) x86)))
  :hints (("Goal" :use ((:instance read-of-bvchop-48 (addr (+ ad1 x (bvchop 48 ad2))))
                        (:instance read-of-bvchop-48 (addr (+ ad1 x ad2))))
           :in-theory (e/d (ifix) (read-of-bvchop-48)))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; similar to the rule about program-at
;; maybe it's better to use read-bytes since that one takes a list of bytes whereas this one takes a huge chunk (BV)
(defthmd read-when-equal-of-read-and-subregionp
  (implies (and (equal freeval (read n2 ad2 x86)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregionp n1 ad1 n2 ad2)
                ;; (syntaxp (quotep freeval)) ; maybe uncomment
;                (unsigned-byte-p 48 n1)
                (natp n1)
                (< n1 (expt 2 48)) ; allow equal?
                (unsigned-byte-p 48 n2) ; allow 2^48?
;                (integerp ad1)
                (integerp ad2) ; todo
                )
           (equal (read n1 ad1 x86)
                  ;; or go to bv-array-read, in case the indexing can't be resolved?
                  (let ((diff (bvminus 48 ad1 ad2)))
                    (acl2::slice (+ 7 (* 8 (+ -1 n1)) (* 8 diff))
                                 (* 8 diff)
                                 freeval))))
  :hints (;; ("subgoal *1/2"
          ;;  :use ((:instance slice-of-read (high  (+ -1 (* 8 (expt 2 48))
          ;;                                          (* 8 n1)
          ;;                                          (* 8 (bvchop 48 ad1))
          ;;                                          (- (* 8 (bvchop 48 ad2)))))
          ;;                  (low (+ (* 8 (expt 2 48))
          ;;                          (* 8 (bvchop 48 ad1))
          ;;                          (- (* 8 (bvchop 48 ad2)))))
          ;;                  (n n2)
          ;;                  (addr ad2))
          ;;        (:instance slice-of-read
          ;;                   (high (+ 7 (* 8 (bvplus 48 ad1 (bvuminus 48 ad2)))))
          ;;                   (low (* 8 (bvplus 48 ad1 (bvuminus 48 ad2))))
          ;;                   (n n2)
          ;;                   (addr ad2)))
          ;;  :in-theory (e/d (bvuminus) (slice-of-read)))
          ("Goal"
           :expand (read n1 ad1 x86)
           :induct (read n1 ad1 x86)
           ;(read-induct-two-sizes n1 ad1 ad2 x86)
           :in-theory (e/d ((:i read)
                            bvplus ;bvuminus acl2::bvchop-of-sum-cases
                            subregionp
                            bvlt
                            in-regionp read-becomes-read-byte
                            ifix)
                           (;distributivity
                            acl2::+-of-minus-constant-version ; fixme disable
                            (:e expt)
                            )))))

;; commutes the first hyp (freeval may not be a constant)
(defthmd read-when-equal-of-read-and-subregionp-alt
  (implies (and (equal (read n2 ad2 x86) freeval) ; lots of free vars here ; note that refine-assumptions...
                (subregionp n1 ad1 n2 ad2)
                ;; (syntaxp (quotep freeval)) ; maybe uncomment
;                (unsigned-byte-p 48 n1)
                (natp n1)
                (< n1 (expt 2 48)) ; allow equal?
                (unsigned-byte-p 48 n2) ; allow 2^48?
;                (integerp ad1)
                (integerp ad2) ; todo
                )
           (equal (read n1 ad1 x86)
                  ;; or go to bv-array-read, in case the indexing can't be resolved?
                  (let ((diff (bvminus 48 ad1 ad2)))
                    (acl2::slice (+ 7 (* 8 (+ -1 n1)) (* 8 diff))
                                 (* 8 diff)
                                 freeval))))
  :hints (("Goal" :use (read-when-equal-of-read-and-subregionp)
           :in-theory (disable read-when-equal-of-read-and-subregionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: split out:

(include-book "read-bytes-and-write-bytes")

(local
  ;rename
  (defun indf (n1 ad1 ad2 x86)
    (if (zp n1)
        (list n1 ad1 ad2 x86)
      (indf (+ -1 n1)
            (+ -1 ad1)
            (+ 1 ad2)
            x86))))

(defthm bv-array-read-of-read-bytes
  (implies (and (< ad1 len)
                (natp ad1)
                (natp len)
                (integerp ad2))
           (equal (bv-array-read 8 len ad1 (read-bytes ad2 len x86))
                  (read-byte (bvplus 48 ad1 ad2) x86)))
  :hints (("Goal" :induct (indf len ad1 ad2 x86) ; (read-bytes ad2 len x86)
           ;(read-induct-two-sizes len ad1 ad2 x86)
           :in-theory (enable read-bytes))))

(defthm read-when-equal-of-read-bytes-and-subregionp
  (implies (and (equal bytes (read-bytes ad2 n2 x86)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregionp n1 ad1 n2 ad2)
                ;; (syntaxp (quotep bytes)) ; maybe uncomment
;                (unsigned-byte-p 48 n1)
                (natp n1)
                (< n1 (expt 2 48)) ; allow equal?
                (unsigned-byte-p 48 n2) ; allow 2^48?
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                )
           (equal (read n1 ad1 x86)
                  (bv-array-read-chunk-little n1 8 (len bytes) (bvminus 48 ad1 ad2) bytes)))
  :hints (;; ("subgoal *1/2"
          ;;  :use ((:instance slice-of-read (high  (+ -1 (* 8 (expt 2 48))
          ;;                                          (* 8 n1)
          ;;                                          (* 8 (bvchop 48 ad1))
          ;;                                          (- (* 8 (bvchop 48 ad2)))))
          ;;                  (low (+ (* 8 (expt 2 48))
          ;;                          (* 8 (bvchop 48 ad1))
          ;;                          (- (* 8 (bvchop 48 ad2)))))
          ;;                  (n n2)
          ;;                  (addr ad2))
          ;;        (:instance slice-of-read
          ;;                   (high (+ 7 (* 8 (bvplus 48 ad1 (bvuminus 48 ad2)))))
          ;;                   (low (* 8 (bvplus 48 ad1 (bvuminus 48 ad2))))
          ;;                   (n n2)
          ;;                   (addr ad2)))
          ;;  :in-theory (e/d (bvuminus) (slice-of-read)))
          ("Goal"
           :do-not '(generalize eliminate-destructors)
;           :expand (read n1 ad1 x86)
           :induct (read n1 ad1 x86)
           ;(read-induct-two-sizes n1 ad1 ad2 x86)
           :in-theory (e/d ((:i read)
                            bvplus ;bvuminus acl2::bvchop-of-sum-cases
                            subregionp
                            bvlt
                            in-regionp read-becomes-read-byte
                            ifix
                            acl2::bvchop-of-sum-cases
                            )
                           (;distributivity
                            acl2::+-of-minus-constant-version ; fixme disable
;                            (:e expt)
                            ))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; could prove by turning read-bytes into unpack of read?
(defthm read-bytes-of-write-when-disjoint-regionsp
  (implies (and (disjoint-regionsp n1 ad1 n2 ad2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read-bytes ad1 n1 (write n2 ad2 val x86))
                  (read-bytes ad1 n1 x86)))
  :hints (("Goal" :in-theory (enable read-bytes write))))

(defthm read-bytes-of-write-when-disjoint-regionsp-alt
  (implies (and (disjoint-regionsp n2 ad2 n1 ad1)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read-bytes ad1 n1 (write n2 ad2 val x86))
                  (read-bytes ad1 n1 x86)))
  :hints (("Goal" :in-theory (enable read-bytes write))))

(defthm read-bytes-of-write-when-disjoint-regionsp-gen
  (implies (and (disjoint-regionsp len1 start1 len2 start2) ; free vars
                (subregionp n1 ad1 len1 start1)
                (subregionp n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p '48 len1)
                (unsigned-byte-p '48 len2)
                (unsigned-byte-p '48 n1)
                (unsigned-byte-p '48 n2))
           (equal (read-bytes ad1 n1 (write n2 ad2 val x86))
                  (read-bytes ad1 n1 x86))))

(defthm read-bytes-of-write-when-disjoint-regionsp-gen-alt
  (implies (and (disjoint-regionsp len2 start2 len1 start1) ; free vars
                (subregionp n1 ad1 len1 start1)
                (subregionp n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p '48 len1)
                (unsigned-byte-p '48 len2)
                (unsigned-byte-p '48 n1)
                (unsigned-byte-p '48 n2))
           (equal (read-bytes ad1 n1 (write n2 ad2 val x86))
                  (read-bytes ad1 n1 x86))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; (defthm read-of-write-when-subregionp
;;   (implies (and (subregionp n1 ad1 n2 ad2)
;;                 (unsigned-byte-p 48 n2)
;;                 (integerp n1)
;;                 (integerp ad1)
;;                 (integerp ad2))
;;            (equal (read n1 ad1 (write n2 ad2 val x86))
;;                   (slice (+ -1 (* 8 (+ n1 (bvminus 48 ad1 ad2))))
;;                          (* 8 (bvminus 48 ad1 ad2))
;;                          val)))
;;   :hints (("Goal" :in-theory (enable subregionp in-regionp bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases)))
;; )
