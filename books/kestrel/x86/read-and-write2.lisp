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
(include-book "kestrel/memory/memory48" :dir :system)

(defthm read-byte-of-write-byte-when-disjoint-1
  (implies (and (disjoint-regions48p len1 start1 len2 start2)
                (in-region48p ad1 len1 start1)
                (in-region48p ad2 len2 start2))
           (equal (read-byte ad1 (write-byte ad2 val x86))
                  (read-byte ad1 x86))))

(defthm read-byte-of-write-byte-when-disjoint-2
  (implies (and (disjoint-regions48p len1 start1 len2 start2)
                (in-region48p ad2 len1 start1)
                (in-region48p ad1 len2 start2))
           (equal (read-byte ad1 (write-byte ad2 val x86))
                  (read-byte ad1 x86))))

(defthm read-byte-of-write-when-disjoint
  (implies (and (disjoint-regions48p 1 ad1 n2 ad2)
                (< n2 (expt 2 48)) ; what if = ?
                (integerp n2)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n2 ad2 val x86))
                  (read-byte ad1 x86)))
  :hints (("Goal" :in-theory (enable disjoint-regions48p bvlt))))

(defthm read-byte-of-write-when-disjoint-alt
  (implies (and (disjoint-regions48p n2 ad2 1 ad1)
                (< n2 (expt 2 48)) ; what if = ?
                (integerp n2)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n2 ad2 val x86))
                  (read-byte ad1 x86)))
  :hints (("Goal" :use (:instance read-byte-of-write-when-disjoint)
           :in-theory (e/d (disjoint-regions48p-symmetric)
                           (read-byte-of-write-when-disjoint
                            READ-BYTE-OF-WRITE-BOTH ; for speed
                            )))))

;todo: make an alt verion
(defthm read-byte-of-write-when-disjoint-gen
  (implies (and (disjoint-regions48p len1 start1 len2 start2)
                (subregion48p 1 ad1 len1 start1) ; or use in-region48p?
                (subregion48p n2 ad2 len2 start2)
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
                  (IF (in-region48p ad1 n ad2)
                      (SLICE (+ 7 (* 8 (BVMINUS 48 AD1 AD2)))
                             (* 8 (BVMINUS 48 AD1 AD2))
                             VAL)
                    (READ-BYTE AD1 X86))))
  :hints (("Goal" :in-theory (enable in-region48p bvlt))))

(in-theory (disable READ-BYTE-OF-WRITE-BOTH))

;todo: in-region48p is subregion48p of size 1

;slow
(defthm not-in-regionp-when-disjoint-regions48p
  (implies (and (disjoint-regions48p len1 start1 len2 start2)
                (in-region48p ad1 len1 start1)
                (subregion48p rlen rad len2 start2)
                ;; (integerp ad1)
                ;; (integerp rad)
                ;; (integerp start1)
                ;; (integerp start2)
                (unsigned-byte-p '48 len1)
                (unsigned-byte-p '48 len2)
                (unsigned-byte-p '48 rlen))
           (not (in-region48p ad1 rlen rad)))
  :hints (("Goal" :in-theory (enable disjoint-regions48p
                                     subregion48p
                                     in-region48p
                                     bvlt bvminus BVUMINUS bvplus
                                     acl2::bvchop-of-sum-cases))))

;move
(defthm subregion48p-one-smaller
  (implies (and (subregion48p len1 ad1 len2 ad2)
                (unsigned-byte-p 48 len1)
                (integerp ad1) ; drop?
  ;              (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 len2)
                ;(unsigned-byte-p 48 ad2)
                (integerp ad2) ; drop?
                )
           (subregion48p (+ -1 len1) (+ 1 ad1) len2 ad2))
  :hints (("Goal" :in-theory (enable subregion48p in-region48p
                                     bvlt bvminus BVUMINUS bvplus
                                     acl2::bvchop-of-sum-cases))))

(defthm read-of-write-when-disjoint-regions48p
  (implies (and (disjoint-regions48p n1 ad1 n2 ad2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :in-theory (enable read write))))

(defthm subregion48p-when-not-unsigned-byte-p
  (implies (and (not (unsigned-byte-p 48 len1))
                (integerp len1))
           (equal (subregion48p len1 ad1 len2 ad2)
                  (if (zp len1)
                      t
                    (if (zp len2)
                        nil
                      (if (<= (expt 2 48) len2)
                          t
                        nil)))))
  :hints (("Goal" :in-theory (enable subregion48p unsigned-byte-p))))

;; (defthm subregion48p-when-not-unsigned-byte-p-2
;;   (implies (and (not (unsigned-byte-p 48 len2))
;;                 (integerp len2))
;;            (equal (subregion48p len1 ad1 len2 ad2)
;;                   (if (zp len1)
;;                       t
;;                     (if (zp len2)
;;                         nil
;;                       t))))
;;   :hints (("Goal" :in-theory (enable subregion48p unsigned-byte-p))))

(defthm read-of-write-when-disjoint-regions48p-gen
  (implies (and (disjoint-regions48p len1 start1 len2 start2) ; free vars
                (subregion48p n1 ad1 len1 start1)
                (subregion48p n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :in-theory (enable read write))))

(defthm read-of-write-when-disjoint-regions48p-gen-alt
  (implies (and (disjoint-regions48p len2 start2 len1 start1) ; todo: rename vars
                (subregion48p n1 ad1 len1 start1)
                (subregion48p n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (read n1 ad1 x86)))
  :hints (("Goal" :use (:instance read-of-write-when-disjoint-regions48p-gen)
           :in-theory '(disjoint-regions48p-symmetric))))

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
(defthmd read-when-equal-of-read-and-subregion48p
  (implies (and (equal freeval (read n2 ad2 x86)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregion48p n1 ad1 n2 ad2)
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
                            subregion48p
                            bvlt
                            in-region48p read-becomes-read-byte
                            ifix)
                           (;distributivity
                            acl2::+-of-minus-constant-version ; fixme disable
                            (:e expt)
                            )))))

;; commutes the first hyp (freeval may not be a constant)
(defthmd read-when-equal-of-read-and-subregion48p-alt
  (implies (and (equal (read n2 ad2 x86) freeval) ; lots of free vars here ; note that refine-assumptions...
                (subregion48p n1 ad1 n2 ad2)
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
  :hints (("Goal" :use (read-when-equal-of-read-and-subregion48p)
           :in-theory (disable read-when-equal-of-read-and-subregion48p))))

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

(defthm read-when-equal-of-read-bytes-and-subregion48p
  (implies (and (equal bytes (read-bytes ad2 n2 x86)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregion48p n1 ad1 n2 ad2)
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
                            subregion48p
                            bvlt
                            in-region48p read-becomes-read-byte
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
(defthm read-bytes-of-write-when-disjoint-regions48p
  (implies (and (disjoint-regions48p n1 ad1 n2 ad2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read-bytes ad1 n1 (write n2 ad2 val x86))
                  (read-bytes ad1 n1 x86)))
  :hints (("Goal" :in-theory (enable read-bytes write))))

(defthm read-bytes-of-write-when-disjoint-regions48p-alt
  (implies (and (disjoint-regions48p n2 ad2 n1 ad1)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read-bytes ad1 n1 (write n2 ad2 val x86))
                  (read-bytes ad1 n1 x86)))
  :hints (("Goal" :in-theory (enable read-bytes write))))

(defthm read-bytes-of-write-when-disjoint-regions48p-gen
  (implies (and (disjoint-regions48p len1 start1 len2 start2) ; free vars
                (subregion48p n1 ad1 len1 start1)
                (subregion48p n2 ad2 len2 start2)
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

(defthm read-bytes-of-write-when-disjoint-regions48p-gen-alt
  (implies (and (disjoint-regions48p len2 start2 len1 start1) ; free vars
                (subregion48p n1 ad1 len1 start1)
                (subregion48p n2 ad2 len2 start2)
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


;; (defthm read-of-write-when-subregion48p
;;   (implies (and (subregion48p n1 ad1 n2 ad2)
;;                 (unsigned-byte-p 48 n2)
;;                 (integerp n1)
;;                 (integerp ad1)
;;                 (integerp ad2))
;;            (equal (read n1 ad1 (write n2 ad2 val x86))
;;                   (slice (+ -1 (* 8 (+ n1 (bvminus 48 ad1 ad2))))
;;                          (* 8 (bvminus 48 ad1 ad2))
;;                          val)))
;;   :hints (("Goal" :in-theory (enable subregion48p in-region48p bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases)))
;; )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: move these to better places:

;; or we could tigthen the inner size, but removing it seems good to allow the pluses to possibly combine
(defthmd acl2::bvchop-of-+-of-bvplus
  (implies (and (<= size size2)
                (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                (integerp size2))
           (equal (bvchop size (+ x (bvplus size2 y z)))
                  (bvchop size (+ x y z))))
  :hints (("Goal" :in-theory (enable bvplus))))

;; or we could tigthen the inner size, but removing it seems good to allow the pluses to possibly combine
(defthm acl2::logext-of-+-of-bvplus
  (implies (and (<= size size2)
                (integerp x)
                (integerp y)
                (integerp z)
                (posp size)
                (integerp size2))
           (equal (logext size (+ x (bvplus size2 y z)))
                  (logext size (+ x y z))))
  :hints (("Goal" :use ((:instance acl2::logext-of-bvchop-same (x (+ x (bvplus size2 y z))))
                        (:instance acl2::logext-of-bvchop-same (x (+ x y z))))
           :in-theory (e/d (acl2::bvchop-of-bvplus
                            acl2::bvchop-of-+-of-bvplus)
                           (acl2::logext-of-bvchop-same
                            acl2::logext-of-bvchop-smaller
                            acl2::getbit-0-of-plus)))))

(include-book "readers-and-writers64") ; todo
;; or we could tigthen the inner size, but removing it seems good to allow the pluses to possibly combine
(defthm set-rip-of-+-of-bvplus
  (implies (and (<= 48 size)
                (integerp size)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (set-rip (+ x (bvplus size y z)) x86)
                  (set-rip (+ x y z) x86)))
  :hints (("Goal" :use ((:instance set-rip-of-logext (rip (+ x (bvplus size y z))))
                        (:instance set-rip-of-logext (rip (+ x y z))))
           :in-theory (disable set-rip-of-logext))))

(include-book "canonical-unsigned")
(local (include-book "kestrel/axe/rules3" :dir :system)) ; todo: for acl2::getbit-when-<-of-constant-high
(defthm equal-of-bvsx-64-48-becomes-unsigned-canonical-address-p
  (equal (equal (bvsx 64 48 x) x)
         (and (unsigned-byte-p 64 x)
              (unsigned-canonical-address-p x)))
  :hints (("Goal"
           :use (:instance acl2::split-bv
                           (n 64)
                           (m 48))
           :in-theory (e/d (unsigned-canonical-address-p
                            acl2::bvsx-alt-def-2
                            bvlt)
                           (acl2::bvcat-equal-rewrite-alt
                            acl2::bvcat-equal-rewrite
                            bvcat logapp
                            acl2::bvcat-of-slice-and-x-adjacent
                            acl2::bvcat-of-slice-and-slice-adjacent
                            acl2::rewrite-unsigned-byte-p-when-term-size-is-larger)))))

(defthm bvsx-64-48-of-bvplyus-48-when-unsigned-canonical-address-p
  (implies (and ;(canonical-regionp len base)
                ;(in-region64p ad len base)
                ;(in-region64p (bvplus 64 offset ad) len base)
                (unsigned-canonical-address-p (bvplus 64 offset ad))
                (integerp offset)
                (integerp ad)
                (integerp base)
                )
           (equal (bvsx 64 48 (bvplus 48 offset ad))
                  (bvplus 64 offset ad)))
  :hints (("Goal" :use (:instance equal-of-bvsx-64-48-becomes-unsigned-canonical-address-p
                                  (x (bvplus 64 offset ad)))
           :in-theory (disable equal-of-bvsx-64-48-becomes-unsigned-canonical-address-p))))

;; can help clarify failures
(defthm read-of-write-of-write-irrel-inner-bv
  (implies (and (disjoint-regions48p n1 addr1 n2 addr2)
                (integerp addr1)
                (integerp addr2)
                (integerp outer-n)
                (integerp outer-addr)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 addr1 (write outer-n outer-addr outer-val (write n2 addr2 val x86)))
                  (read n1 addr1 (write outer-n outer-addr outer-val x86))))
  :hints (("Goal" :use (:instance read-of-write-of-write-irrel-inner)
           :in-theory (e/d (disjoint-regions48p bvlt)
                           (read-of-write-of-write-irrel-inner)))))

;; can help clarify failures
(defthm read-of-write-of-write-of-write-same-middle-bv
  (implies (and ;(disjoint-regions48p n1 addr1 n2 addr2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2)
                (integerp n4))
           (equal (read n1 ad1 (write n2 ad2 val2 (write n1 ad1 val1-inner (write n4 ad4 val4 x86))))
                  (read n1 ad1 (write n2 ad2 val2 (write n1 ad1 val1-inner x86)))
                  ))
  :hints (("Goal" :in-theory (enable read write acl2::bvminus-of-+-arg2
                                     in-region48p ; why?
                                     bvlt
                                     ))))
