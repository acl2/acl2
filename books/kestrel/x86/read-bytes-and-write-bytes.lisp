; Simpler functions for reading and writing memory
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "read-and-write")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable ;(:linear x86isa::n08p-xr-mem)
                    acl2::unsigned-byte-p-from-bounds
                    bigmem::nth-pgp
                    acl2-number-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read N bytes, starting at ADDR.  Unlike read, this returns a list.
;; TODO: Consider putting the N parameter first
(defund read-bytes (addr n x86)
  (declare (xargs :guard (and (integerp addr)
                              (natp n))
                  :stobjs x86))
  (if (zp n)
      nil
    (cons (read-byte addr x86)
          (read-bytes (+ 1 (mbe :logic (ifix addr) :exec addr)) (+ -1 n) x86))))

(defthm car-of-read-bytes
  (implies (and (posp n)
                (integerp addr))
           (equal (car (read-bytes addr n x86))
                  (read-byte addr x86)))
  :hints (("Goal" :expand
           (read-bytes addr n x86))))

(local
 (defun inc-dec-dec-induct (x y z)
   (if (zp y)
       (list x y z)
     (inc-dec-dec-induct (+ 1 x) (+ -1 y) (+ -1 z)))))

(defthm nth-of-read-bytes
  (implies (and (natp n1)
                (< n1 n2)
                (natp n2)
                (integerp addr))
           (equal (nth n1 (read-bytes addr n2 x86))
                  (read-byte (+ addr n1) x86)))
  :hints (("Goal" :induct (inc-dec-dec-induct addr n1 n2)
           :in-theory (enable read-bytes))))

(defthm len-of-read-bytes
  (equal (len (read-bytes addr n x86))
         (nfix n))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm consp-of-read-bytes
  (equal (consp (read-bytes addr n x86))
         (posp n))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm read-bytes-iff
  (iff (read-bytes addr n x86)
       (posp n))
  :hints (("Goal" :in-theory (enable read-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund write-bytes (addr bytes x86)
  (declare (xargs :stobjs x86
                  :guard (and (acl2::all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (integerp addr))))
  (if (endp bytes)
      x86
    (let ((x86 (write-byte addr (first bytes) X86)))
      (write-bytes (+ 1 (mbe :logic (ifix addr) :exec addr))
                   (rest bytes)
                   x86))))

(defthm write-bytes-of-nil
  (equal (write-bytes addr nil x86)
         x86)
  :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo turn only writes of >1 byte into write-bytes..
(defthm write-bytes-when-length-is-1
  (implies (equal 1 (len bytes))
           (equal (write-bytes addr bytes x86)
                  (write-byte addr (first bytes) x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm write-bytes-of-read-bytes-same
  (equal (write-bytes addr (read-bytes addr n x86) x86)
         x86)
  :hints (("Goal" :in-theory (enable read-bytes write-bytes))))

(defthm write-bytes-of-write-byte-irrel
  (implies (and (<= (len bytes) (bvminus 48 addr2 addr1))
                (integerp addr2)
                (integerp addr1))
           (equal (write-bytes addr1 bytes (write-byte addr2 byte x86))
                  (write-byte addr2 byte (write-bytes addr1 bytes x86))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write-bytes addr1 bytes x86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus write-bytes write-byte)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::bvcat-of-+-high
                                                    ACL2::BVCHOP-IDENTITY ;for speed
                                                    )))))

(defthm read-byte-of-write-bytes-irrel
  (implies (and (<= (len bytes) (bvminus 48 addr1 addr2))
                (integerp addr2)
                (integerp addr1))
           (equal (read-byte addr1 (write-bytes addr2 bytes x86))
                  (read-byte addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-BYTES ADDR2 BYTES X86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus write-bytes ;ACL2::NTH-WHEN-N-IS-ZP
                                   )
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::bvcat-of-+-high
;                                                    ACL2::NTH-OF-CDR
                                                    )))))

(defthm read-of-write-bytes-irrel
  (implies (and (<= (len vals) (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                ;(natp n1)
                (integerp addr2)
                (integerp addr1))
           (equal (read n1 addr1 (write-bytes addr2 vals x86))
                  (read n1 addr1 x86)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (e/d (read bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus ;read-byte
                                   )
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    ACL2::BVCAT-OF-+-HIGH
                                                    )))))

(local
 (defthm <-of-if-arg2
   (equal (< x (if test y z))
          (if test
              (< x y)
            (< x z)))))

(defthm read-byte-of-write-bytes-not-irrel
  (implies (and (< (bvminus 48 addr1 addr2) (len bytes))
                (integerp addr2)
                (integerp addr1)
                (<= (len bytes) (expt 2 48)))
           (equal (read-byte addr1 (write-bytes addr2 bytes x86))
                  (bvchop 8 (nth (bvminus 48 addr1 addr2) bytes))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-BYTES ADDR2 BYTES X86)
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus write-bytes)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::bvcat-of-+-high
;                                                    ACL2::NTH-OF-CDR
                                                    )))))

(local
  (defthm move-neg-addend
    (implies (acl2-numberp y)
             (equal (equal 1 (+ (- x) y))
                    (equal (+ 1 x) y)))))

;; Introduces write-bytes.
;; inner write is at lower address
(defthmd write-byte-of-write-byte-adjacent-1
  (implies (and (equal 1 (bvminus 48 k+1 k))
                (integerp k)
                (integerp k+1))
           (equal (write-byte k+1 byte1 (write-byte k byte2 x86))
                  (write-bytes k (list byte2 byte1) x86)))
  :hints (("Goal" :in-theory (enable write-byte write-bytes bvminus acl2::bvchop-of-sum-cases))))

;; Introduces write-bytes.
;; outer write is at lower addresses
(defthmd write-byte-of-write-byte-adjacent-2
  (implies (and (equal 1 (bvminus 48 k+1 k))
                (integerp k)
                (integerp k+1))
           (equal (write-byte k byte1 (write-byte k+1 byte2 x86))
                  (write-bytes k (list byte1 byte2) x86)))
  :hints (("Goal" :in-theory (enable write-byte write-bytes bvminus acl2::bvchop-of-sum-cases))))

;; Introduces write-bytes.
;todo: avoid the reverse?
(defthmd write-becomes-write-bytes
  (equal (write n addr val x86)
         (write-bytes addr (reverse (acl2::unpackbv n 8 val)) x86))
  :hints (("Goal" :in-theory (e/d (write
                                   ;;list::cdr-append
                                   write-byte)
                                  (;ACL2::LEN-CONS-META-RULE
                                   ;;ACL2::TAKE-OF-CONS
                                   last
                                   ACL2::UNPACKBV-OPENER
                                   write-bytes))
           :induct (WRITE N ADDR VAL X86)
           :expand ((WRITE 1 ADDR VAL X86)
                    (WRITE-BYTES ADDR
                                (ACL2::REVERSE-LIST (ACL2::UNPACKBV N 8 VAL))
                                X86)))))

(defthmd write-bytes-becomes-write
  (equal (write-bytes addr vals x86)
         (write (len vals) addr (acl2::packbv (len vals) 8 (acl2::reverse-list vals)) x86))
  :hints (("Goal" :in-theory (e/d (;list::cdr-append
                                   write-bytes
                                   write-byte)
                                  (;ACL2::LEN-CONS-META-RULE
                                   ;;ACL2::TAKE-OF-CONS
                                   last
                                   ACL2::UNPACKBV-OPENER
                                   ;;write-bytes
                                   ;ACL2::NTH-WHEN-ZP
                                   ))
           :expand (WRITE (LEN VALS)
                          ADDR
                          (ACL2::PACKBV (LEN VALS)
                                        8 (acl2::reverse-list VALS))
                          X86)
           :induct (WRITE-BYTES ADDR VALS X86))))


(local
  (defun-nx double-write-bytes-induct-two-addrs (addr addr2 vals x86)
    (if (endp vals)
        (list addr addr2 vals x86)
      (double-write-bytes-induct-two-addrs (+ 1 addr)
                                           (+ 1 addr2)
                                           (cdr vals)
                                           (WRITE-BYTE addr (CAR VALS) X86)))))

(defthmd write-bytes-of-bvchop-arg1-helper
  (implies (and (equal (bvchop 48 ad1)
                       (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (write-bytes ad1 vals x86)
                  (write-bytes ad2 vals x86)))
  :hints (("Goal" ;:expand ((WRITE-BYTES AD2 VALS X86))
           :induct (double-write-bytes-induct-two-addrs ad1 ad2 vals x86)
           :expand ((WRITE-BYTES AD1 VALS X86)
                    (WRITE-BYTES AD2 VALS X86))
           :in-theory (enable bvplus write-bytes WRITE-BYTE)
           )))

(defthm write-bytes-of-bvchop-arg1
  (implies (integerp addr)
           (equal (write-bytes (bvchop 48 addr) vals x86)
                  (write-bytes addr vals x86)))
  :hints (("Goal" :use (:instance write-bytes-of-bvchop-arg1-helper (ad1  (bvchop 48 addr)) (ad2 addr))
           :in-theory (disable write-bytes-of-bvchop-arg1-helper))))

;; inner write is at lower addresses
(defthmd write-bytes-of-write-bytes-adjacent-1
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2))
           (equal (write-bytes addr1 vals1 (write-bytes addr2 vals2 x86))
                  (write-bytes addr2 (append vals2 vals1) x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

;rename, since this doesn't use the function disjoint
(defthm write-bytes-of-write-bytes-disjoint
  (implies (and (syntaxp (acl2::smaller-termp addr1 addr2))
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (len vals1) (bvminus 48 addr2 addr1))
                (integerp addr2)
                (integerp addr1))
           (equal (write-bytes addr2 vals2 (write-bytes addr1 vals1 x86))
                  (write-bytes addr1 vals1 (write-bytes addr2 vals2 x86))))
  :hints (("Goal"
           :induct (WRITE-BYTES ADDR1 VALS1 X86)
           :in-theory (e/d (write-bytes bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::bvcat-of-+-high)))))

(defthm write-bytes-of-append
  (implies (and (integerp ad)
                (<= (+ (len vals1) (len vals2)) (expt 2 48)))
           (equal (write-bytes ad (append vals1 vals2) x86)
                  (write-bytes ad vals1 (write-bytes (+ ad (len vals1)) vals2 x86))))
  :hints (("Goal" :in-theory (enable write-bytes append acl2::bvminus-of-+-arg3))))

;; outer write is at lower addresses
(defthmd write-bytes-of-write-bytes-adjacent-2
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2)
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (+ (len vals1) (len vals2)) (expt 2 48)))
           (equal (write-bytes addr2 vals2 (write-bytes addr1 vals1 x86))
                  (write-bytes addr2 (append vals2 vals1) x86)))
  :hints (("Goal" :in-theory (enable BVPLUS))))

;; outer write is at lower addresses
(defthmd write-byte-of-write-bytes-adjacent
  (implies (and (equal addr1 (bvplus 48 addr2 1))
                (integerp addr2)
                (<= 1 (bvminus 48 addr1 addr2))
                (<= (+ (len vals1) 1) (expt 2 48)))
           (equal (write-byte addr2 val (write-bytes addr1 vals1 x86))
                  (write-bytes addr2 (cons val vals1) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-2 (vals2 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-2))))

;; outer write is at lower addresses
(defthmd write-bytes-of-write-byte-adjacent
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2)
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (+ 1 (len vals2)) (expt 2 48)))
           (equal (write-bytes addr2 vals2 (write-byte addr1 val x86))
                  (write-bytes addr2 (append vals2 (list val)) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-2 (vals1 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-2))))

   ;kill
;; (defthm write-bytes-of-write-bytes-adjacent-1
;;   (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
;;                 (integerp addr2))
;;            (equal (write-bytes addr1 vals1 (write-bytes addr2 vals2 x86))
;;                   (write-bytes addr2 (append vals2 vals1) x86))))

;; inner write is at lower addresses
(defthmd write-bytes-of-write-byte-adjacent-2
  (implies (and (equal addr2 (bvplus 48 1 addr1))
                (integerp addr1)
                (<= (len vals2) (bvminus 48 addr1 addr2))
                (<= (+ 1 (len vals2)) (expt 2 48)))
           (equal (write-bytes addr2 vals2 (write-byte addr1 val x86))
                  (write-bytes addr1 (cons val vals2) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-1
                                  (addr1 addr2)
                                  (vals1 vals2)
                                  (addr2 addr1)
                                  (vals2 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-1))))

;; inner write is at lower addresses
(defthmd write-byte-of-write-bytes-adjacent-1
  (implies (and (equal addr1 (bvplus 48 addr2 (len vals2)))
                (integerp addr2))
           (equal (write-byte addr1 val (write-bytes addr2 vals2 x86))
                  (write-bytes addr2 (append vals2 (list val)) x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-adjacent-1 (vals1 (list val)))
           :in-theory (disable write-bytes-of-write-bytes-adjacent-1))))

;;                   ;; (WRITE-BYTES
;;                   ;;  4198450 '(5 156 131 196 8 137)
;;                   ;;  (WRITE-BYTES
;;                   ;;   4198442
;;                   ;;   '(232 253 255 255 82 232 2 0 0 141)


;; (thm
;;  (implies (and (integerp ad1)
;;                (integerp ad2)

;;                )
;;           (equal (WRITE-BYTES ad1 vals1 (WRITE-BYTES ad2 vals2 x86))
;;                  (WRITE-BYTES ad1 vals1 (WRITE-BYTES ad2 (butlast vals2 (- (len vals2) (- ad1 ad2))) x86))))


(defthm write-bytes-subst-constant-arg1
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad))
           (equal (write-bytes ad bytes x86)
                  (write-bytes freek bytes x86))))

;;todo: why isn't the non-alt rule sufficient?
(defthm write-bytes-subst-constant-arg1-alt
  (implies (and (equal freek (bvchop 48 ad))
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad))
           (equal (write-bytes ad bytes x86)
                  (write-bytes freek bytes x86))))

(defthm write-bytes-of-write-byte-same
  (implies (integerp ad)
           (equal (write-bytes ad bytes (write-byte ad byte x86))
                  (if (consp bytes)
                      (write-bytes ad bytes x86)
                    (write-byte ad byte x86))))
  :hints (("Goal" :expand ((WRITE-BYTES AD BYTES X86)
                           (WRITE-BYTES AD BYTES (WRITE-BYTE AD BYTE X86))))))

(defthm write-bytes-when-not-consp
  (implies (not (consp bytes))
           (equal (write-bytes ad bytes x86)
                  x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm write-byte-of-write-bytes-same
  (implies (and (integerp ad)
                (<= (len bytes) (expt 2 48)) ;gen
                )
           (equal (write-byte ad byte (write-bytes ad bytes x86))
                  (write-byte ad byte (write-bytes (+ 1 ad) (cdr bytes) x86))))
  :hints (("Goal" :expand ((write-bytes ad bytes x86)))))

(local
  (defun-nx double-write-bytes-induct-two-lists (addr vals1 vals2 x86)
    (if (endp vals1)
        (list addr vals1 vals2 x86)
      (double-write-bytes-induct-two-lists (+ 1 addr)
                                           (cdr vals1)
                                           (cdr vals2)
                                           (WRITE-BYTE addr (CAR VALS1) X86)))))

(defthm write-bytes-of-write-bytes-same
  (implies (and (<= (len vals2) (len vals1))
                (<= (len vals2) (expt 2 48))
                (integerp ad))
           (equal (write-bytes ad vals1 (write-bytes ad vals2 x86))
                  (write-bytes ad vals1 x86)))
  :hints (("Goal"
           :induct (double-write-bytes-induct-two-lists ad vals1 vals2 x86)
           :in-theory (enable write-bytes))))

(defthm write-bytes-equal-when-bvchops-equal
  (implies (and (equal (bvchop 48 ad1) (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (equal (write-bytes ad1 bytes x86) (write-bytes ad2 bytes x86))
                  t))
  :hints (("Goal" :use ((:instance write-bytes-of-bvchop-arg1
                                   (addr ad1)
                                   (vals bytes))
                        (:instance write-bytes-of-bvchop-arg1
                                   (addr ad2)
                                   (vals bytes)))
           :in-theory (disable WRITE-BYTES-OF-BVCHOP-ARG1))))

(defthm write-bytes-subst-term-arg1
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad))
                (integerp ad)
                (integerp free))
           (equal (write-bytes ad bytes x86)
                  (write-bytes free bytes x86))))

(defthm write-bytes-subst-term-arg1-plus-version
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (quotep freek))
                (integerp ad)
                (integerp free))
           (equal (write-bytes (+ 1 ad) bytes x86)
                  (write-bytes (+ 1 freek) bytes x86))))

(defthm write-bytes-subst-term-arg1-plus-version-alt
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad))
                (integerp ad)
                (integerp free))
           (equal (write-bytes (+ 1 ad) bytes x86)
                  (write-bytes (+ 1 free) bytes x86))))

;todo: nested induction
(defthm write-bytes-of-write-byte-same-gen
  (implies (and (< (bvminus 48 ad2 ad1) (len bytes))
                (integerp ad1)
                (integerp ad2))
           (equal (write-bytes ad1 bytes (write-byte ad2 byte x86))
                  (write-bytes ad1 bytes x86)))
  :hints (("Goal"
           :induct (WRITE-BYTES AD1 BYTES X86)
           :in-theory (e/d (write-bytes bvplus acl2::bvchop-of-sum-cases bvuminus bvminus) (acl2::bvminus-becomes-bvplus-of-bvuminus))
           )))

(defthm write-bytes-of-write-byte-too-many
  (implies (and (>= (len bytes) (expt 2 48))
                (integerp ad)
                (integerp ad2))
           (equal (write-bytes ad bytes (write-byte ad2 byte x86))
                  (write-bytes ad bytes x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm write-bytes-of-write-byte-gen
  (implies (and (integerp ad1)
                (integerp ad2)
   ;                (<= (len bytes) (expt 2 48))
                )
           (equal (write-bytes ad1 bytes (write-byte ad2 byte x86))
                  (if (< (bvminus 48 ad2 ad1) (len bytes))
                      (write-bytes ad1 bytes x86)
                    (write-byte ad2 byte (write-bytes ad1 bytes x86)))))
  :hints (("Goal" :in-theory (enable write-bytes))))


(local
  (defun-nx double-write-bytes-induct-two-ads-two-lists (ad1 ad2 vals1 vals2 x86)
    (if (endp vals1)
        (list ad1 ad2 vals1 vals2 x86)
      (double-write-bytes-induct-two-ads-two-lists (+ 1 ad1)
                                                   (+ 1 ad2)
                                                   (cdr vals1)
                                                   (cdr vals2)
                                                   x86))))

;nested induction.  expand more?
(defthm write-bytes-of-write-bytes-same-gen
  (implies (and (<= (+ (bvminus 48 ad2 ad1) (len vals2)) (len vals1))
;                (<= (len vals2) (expt 2 48)) ;gen?
 ;               (<= (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2))
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad1 vals1 x86)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :expand ((WRITE-BYTES 0 VALS1 (WRITE-BYTES AD2 VALS2 X86))
                    (WRITE-BYTES AD1 VALS1 (WRITE-BYTES AD2 VALS2 X86))
                    (WRITE-BYTES AD2 VALS2 X86)
                    (WRITE-BYTES 0 VALS2 X86)
                    (WRITE-BYTES AD1 VALS1 X86)
                    (WRITE-BYTES 0 VALS1 X86)
                    (WRITE-BYTES 0 VALS1
                            (WRITE-BYTES (+ 1 AD2) (CDR VALS2) X86)))
           :induct ;(write-bytes ad2 vals2 x86)
           (double-write-bytes-induct-two-ads-two-lists ad1 ad2 vals1 vals2 x86)
           :in-theory (e/d (write-bytes bvplus bvuminus bvminus)
                           (;(:e ash) ;blows out the memory
                            ;(:e expt)
                            acl2::bvminus-becomes-bvplus-of-bvuminus)))))

;;cut down vals2 when it contains values that will be overwritten
(defthm write-bytes-of-write-bytes-chop-inner
  (implies (and (< (bvminus 48 ad1 ad2) (len vals2))
                (<= (len vals2) (+ (len vals1) (bvminus 48 ad1 ad2)))
                (syntaxp (and (quotep vals2)
                              (quotep ad1)
                              (quotep ad2)))
                (<= (len vals2) (expt 2 48))
                (integerp ad1)
                (integerp ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad1 vals1 (write-bytes ad2 (acl2::firstn (bvminus 48 ad1 ad2) vals2) x86))))
  :hints (("Goal"
           :induct (write-bytes ad2 vals2 x86)
           :expand ((:free (vals x86) (write-bytes ad2 vals x86))
                    (WRITE-BYTES 0
                                (ACL2::TAKE (BVCHOP 48 AD1) VALS2)
                                X86)
                    (WRITE-BYTES 2 VALS1 X86)
                    ;(ACL2::SUBRANGE 1 (+ -1 (BVCHOP 48 AD1))
                                                  ;;VALS2)
                    ;; (WRITE-BYTES 0
                    ;;             (CONS (CAR VALS2)
                    ;;                   (ACL2::SUBRANGE 1 (+ -1 (BVCHOP 48 AD1))
                    ;;                                   VALS2))
                    ;;             X86)
                    (WRITE-BYTES 0 (ACL2::TAKE (BVCHOP 48 AD1) VALS2) X86))
           :in-theory (e/d (WRITE-BYTES bvplus acl2::bvchop-of-sum-cases bvuminus bvminus
                                        )
                           (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                            ACL2::BVCAT-OF-+-LOW ;looped
                            ;;ACL2::TAKE-OF-CDR-BECOMES-SUBRANGE
                            ;;for speed:
                            ;acl2::IMPOSSIBLE-VALUE-1
                            acl2::CONSP-FROM-LEN-CHEAP
                            ;acl2::<-OF-BVCHOP-AND-BVCHOP-WHEN-TOP-BITS-EQUAL
                            ACL2::BVCHOP-IDENTITY
                            ACL2::BVCHOP-PLUS-1-SPLIT)))))

(defthm write-bytes-of-append-gen
  (implies (integerp ad)
           (equal (write-bytes ad (append vals1 vals2) x86)
                  (write-bytes (+ ad (len vals1)) vals2 (write-bytes ad vals1 x86))))
  :hints (("Goal" :in-theory (enable append WRITE-BYTES))))

(defthm write-bytes-of-append-of-finalcdr
  (equal (write-bytes ad (append vals (acl2::finalcdr vals2)) x86)
         (write-bytes ad vals x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

(local
  (defthm <-of-if-arg1
    (equal (< (if test x y) z)
           (if test (< x z) (< y z)))))

(defthmd write-bytes-of-write-bytes-same-contained-helper2
  (implies (and (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (integerp ad1)
                (integerp ad2))
           (equal (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                          (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
                          (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                  vals2))
  :hints (("Goal" :in-theory (enable acl2::equal-of-append))))

(defthm write-bytes-of-+-of-2^48
  (implies (integerp ad)
           (equal (write-bytes (+ 281474976710656 ad) vals x86)
                  (write-bytes ad vals x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm write-bytes-of-write-bytes-of-write-bytes-inner-irrel
  (implies (and (integerp ad1)
                (integerp ad2)
                (<= (len vals11) (len vals1)))
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 (write-bytes ad1 vals11 x86)))
                  (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))))
  :hints (("Goal"
           :induct t
           :expand ((:free (vals x86) (write-bytes ad1 vals x86)))
           :in-theory (e/d (write-bytes bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
;                            append-take-nthcdr
                            ;acl2::append-of-take-and-nthcdr-2 ;compare to  list::append-take-nthcdr
    ;write-bytes-of-append-gen write-bytes-of-append
    ;list::equal-append-reduction!
                            ;; for speed:
                            acl2::DISTRIBUTIVITY-OF-MINUS-OVER-+
                            WRITE-BYTES-OF-WRITE-BYTES-SAME-GEN)))))

(local ; dup
  (DEFTHM ACL2::BVCHOP-IDENTITY-WHEN-<
                (IMPLIES (AND (< X ACL2::FREE)
                              (SYNTAXP (AND (QUOTEP ACL2::FREE) (QUOTEP N)))
                              (<= ACL2::FREE (EXPT 2 N))
                              (NATP N)
                              (NATP X))
                         (EQUAL (BVCHOP N X) X))
))

;todo: very slow
;; to state this, we manually put in an append for vals2. next we'll replace it with just vals2 (using helper2 above)
;slow
(defthm write-bytes-of-write-bytes-same-contained-helper
  (implies (and (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (< (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (true-listp vals1)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2
                                                      ;;vals2
                                                      (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                                              (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
                                                              (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                                                      x86))
                  (write-bytes ad2 (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                           vals1
                                           (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                               x86)))
  :hints (("Goal"
           ;; :cases ((equal VALS2
           ;;                (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
           ;;                        (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
           ;;                        (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))))
           :use ( ;; (:instance write-bytes-of-append-gen
                 ;;            (ad ad1)
                 ;;            (vals1 (acl2::firstn (bvminus 48 ad1 ad2) vals2))
                 ;;            (vals2 (append (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2))
                 ;;                           (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))))
                 ;; (:instance write-bytes-of-append-gen
                 ;;            (ad (+ ad1 (bvminus 48 ad1 ad2)))
                 ;;            (vals1 (acl2::firstn (len vals1) (nthcdr (bvminus 48 ad1 ad2) vals2)))
                 ;;            (vals2 (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2)))
                 (:instance WRITE-BYTES-OF-WRITE-BYTES-DISJOINT
                            (X86 (WRITE-BYTES
                                  AD2
                                  (ACL2::TAKE (bvminus 48 ad1 ad2)
                                                  VALS2)
                                  X86))
                            (VALS1 (NTHCDR (+ (len vals1) (bvminus 48 ad1 ad2))
                                           VALS2))
                            (ADDR1 (+ AD1 (LEN VALS1)))
                            (VALS2 VALS1)
                            (ADDR2 AD1))
                 )
           :do-not-induct t
           :in-theory (e/d (WRITE-BYTES bvplus acl2::bvchop-of-sum-cases bvuminus bvminus ;ACL2::<-OF-IF-ARG1 ACL2::<-OF-IF-ARG2
                                        unsigned-byte-p
                                        )
                           (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                            ;APPEND-TAKE-NTHCDR
                            ;ACL2::APPEND-OF-TAKE-AND-NTHCDR-2 ;compare to  LIST::APPEND-TAKE-NTHCDR
     ;write-bytes-of-append-gen write-bytes-of-append
                            ;LIST::EQUAL-APPEND-REDUCTION!
                            WRITE-BYTES-OF-WRITE-BYTES-DISJOINT
                            ;ACL2::TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                            ;; for speed:
                            acl2::BVCHOP-IDENTITY
                            ;acl2::LEN-OF-IF
                            WRITE-BYTES-OF-WRITE-BYTES-SAME-GEN
                            )))))

(defthmd write-bytes-of-write-bytes-same-contained
  (implies (and (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (< (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (true-listp vals1)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad2 (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                          vals1
                                          (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                              x86)))
  :hints (("Goal" :use (write-bytes-of-write-bytes-same-contained-helper
                        write-bytes-of-write-bytes-same-contained-helper2)
           :in-theory nil)))

(defthmd write-bytes-of-write-bytes-same-contained-constants
  (implies (and (syntaxp (and (quotep ad1)
                              (quotep ad2)
                              (quotep vals1)
                              (quotep vals2)))
                (<= (+ (bvminus 48 ad1 ad2) (len vals1)) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (< (len vals1) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (true-listp vals1)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-bytes ad1 vals1 (write-bytes ad2 vals2 x86))
                  (write-bytes ad2
                              ;; this whole thing gets computed:
                              (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                          vals1
                                          (nthcdr (+ (len vals1) (bvminus 48 ad1 ad2)) vals2))
                              x86)))
  :hints (("Goal" :use (write-bytes-of-write-bytes-same-contained-helper
                        write-bytes-of-write-bytes-same-contained-helper2)
           :in-theory nil)))

(defthmd write-byte-of-write-bytes-same-contained-constants
  (implies (and (syntaxp (and (quotep ad1)
                              (quotep ad2)
                              (quotep byte)
                              (quotep vals2)))
                (<= (+ (bvminus 48 ad1 ad2) 1) (len vals2))
                (< (len vals2) (expt 2 48)) ;gen?
                (integerp ad1)
                (integerp ad2)
                (true-listp vals2)
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                )
           (equal (write-byte ad1 byte (write-bytes ad2 vals2 x86))
                  (write-bytes ad2
                              ;; this whole thing gets computed:
                              (append (acl2::firstn (bvminus 48 ad1 ad2) vals2)
                                          (list byte)
                                          (nthcdr (+ 1 (bvminus 48 ad1 ad2)) vals2))
                              x86)))
  :hints (("Goal" :use (:instance write-bytes-of-write-bytes-same-contained-constants (vals1 (list byte)))
           :in-theory (disable write-bytes-of-write-bytes-same-contained-constants))))


;; (thm
;;  (implies (and (equal 1 (len vals2))
;;                (equal k+1 (bvplus 1 k)))
;;           (equal (write-bytes k+1 vals1 (write-bytes k vals2 x86))
;;                  (write-bytes k+1 (cons (first vals2s)) x86))))

;; (defthm read-of-write-bytes-not-irrel
;;   (implies (and (< (bvminus 48 addr1 addr2) (len vals))
;;                 (<= n1 (bvminus 48 addr2 addr1))
;;                 (natp n1)
;;                 (integerp addr2)
;;                 (integerp addr1))
;;            (equal (read n1 addr1 (write-bytes addr2 vals x86))
;;                   (read n1 addr1 x86)))
;;   :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct (read n1 addr1 x86)
;;            :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus)
;;                            (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
;;                                                     ACL2::BVCAT-OF-+-HIGH
;;                                                     )))))

;; (defthm write-bytes-of-281474976710656
;;   (equal (write-bytes 281474976710656 vals x86)
;;          (write-bytes 0 vals x86))
;;   )
