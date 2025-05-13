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
