; Unsigned machinery for canonical addresses
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "portcullis")
(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ; for canonical-address-p
(include-book "regions")

;; Make the machinery for the full 64-bit x86 address space, to support
;; reasoning about canonical addresses:
(local (in-theory (e/d (zp) (acl2::ifix-when-integerp acl2::natp-when-gte-0))))
(make-memory-region-machinery 64)

;(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

;; note that the canonical region wraps around the end of the 64-bit address space
(defconst *base-of-canonical* (acl2::bvchop 64 (- (expt 2 47))))
(defconst *len-of-canonical* (expt 2 48))

;; note that, for unsigned, the canonical region is not contiguous
;; Note that this is amenable to BV-based SMT solving
(defund unsigned-canonical-address-p (ad)
  (declare (xargs :guard (unsigned-byte-p 64 ad)))
  (acl2::bvlt 64 (acl2::bvminus 64 ad *base-of-canonical*) *len-of-canonical*))

(defthm unsigned-canonical-address-p-of-bvif
  (equal (unsigned-canonical-address-p (bvif 64 test x y))
         (if test
             (unsigned-canonical-address-p (bvchop 64 x))
           (unsigned-canonical-address-p (bvchop 64 y)))))

(defthm unsigned-canonical-address-p-of-if
  (equal (unsigned-canonical-address-p (if test x y))
         (if test
             (unsigned-canonical-address-p x)
           (unsigned-canonical-address-p y))))

(defthm unsigned-canonical-address-p-of-bvsx-64-48
  (unsigned-canonical-address-p (bvsx 64 48 x))
  :hints (("Goal" :cases ((equal 0 (getbit 47 x)))
           :in-theory (enable bvsx unsigned-canonical-address-p bvlt bvcat logapp))))

(defthm unsigned-canonical-address-p-of-bvchop
  (equal (unsigned-canonical-address-p (bvchop 64 x))
         (unsigned-canonical-address-p x))
  :hints (("Goal" :in-theory (enable unsigned-canonical-address-p))))

;; also shows that unsigned-canonical-address-p means what we intend it to mean
(defthmd canonical-address-p-of-logext-64-becomes-unsigned-canonical-address-p
  (implies (unsigned-byte-p 64 ad)
           (equal (canonical-address-p (logext 64 ad))
                  (unsigned-canonical-address-p ad)))
  :hints (("Goal" :in-theory (e/d (unsigned-canonical-address-p acl2::bvlt signed-byte-p acl2::logext-cases acl2::bvcat logapp)
                                  (acl2::bvcat-of-getbit-and-x-adjacent
                                   acl2::bvcat-equal-rewrite
                                   acl2::bvcat-equal-rewrite-alt))
           :use (:instance acl2::split-bv-top (size 64) (x ad)))))

(defthmd canonical-address-p-becomes-unsigned-canonical-address-p-of-bvchop
  (implies (signed-byte-p 64 ad)
           (equal (canonical-address-p ad)
                  (unsigned-canonical-address-p (bvchop 64 ad))))
  :hints (("Goal" :in-theory (enable unsigned-canonical-address-p
                                     acl2::bvlt signed-byte-p acl2::logext-cases acl2::bvcat logapp
                                     acl2::bvchop-when-negative-lemma)
           :cases ((< ad 0)))))

(defthmd canonical-address-p-becomes-unsigned-canonical-address-p-of-bvchop-strong
  (equal (canonical-address-p ad)
         (and (signed-byte-p 64 ad)
              (unsigned-canonical-address-p (bvchop 64 ad))))
  :hints (("Goal" :in-theory (enable canonical-address-p
                                     unsigned-canonical-address-p
                                     acl2::bvlt signed-byte-p acl2::logext-cases acl2::bvcat logapp
                                     acl2::bvchop-when-negative-lemma)
           :cases ((< ad 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Make the machinery for the full 64-bit x86 address space:
;; ;(make-memory-region-machinery 64) ; todo: name clashes.  fix and avoid repeated (special case 64) machinery below
;; (defund in-regionp64 (ad len start-ad)
;;   (declare (xargs :guard (and (unsigned-byte-p 64 ad)
;;                               (natp len) ; note that len >= 2^64 covers the whole region
;;                               (unsigned-byte-p 64 start-ad))))
;;   (and (natp len) ; len=0 falsifies the bvlt below
;;        (if (<= (expt 2 64) len) ; we handle (expt 2 64) here, since the len gets chopped to 64 bits below
;;            t ; the region covers the whole address space
;;          (bvlt 64 (bvminus 64 ad start-ad) len))))

;; Checks that the region from AD to AD+LEN-1 (modulo 2^64) is all canonical.
(defund canonical-regionp (len ad)
  (declare (xargs :guard (and (natp len)
                              (unsigned-byte-p 64 ad))))
  (if (= 0 len)
      t ; empty region
    (and (<= len *len-of-canonical*)
         (in-region64p ad *len-of-canonical* *base-of-canonical*)
         (in-region64p (bvplus 64 (bvplus 64 -1 len) ad) *len-of-canonical* *base-of-canonical*))))

;; anything in a canonical region is canonical
(defthm unsigned-canonical-address-p-when-canonical-regionp-and-in-region64p
  (implies (and (canonical-regionp len ad2) ;free vars
                (in-region64p ad len ad2)
                (integerp ad)
                (integerp ad2))
           (unsigned-canonical-address-p ad))
  :hints (("Goal" :in-theory (enable in-region64p
                                     canonical-regionp
                                     unsigned-canonical-address-p
                                     bvlt bvuminus bvplus
                                     acl2::bvchop-of-sum-cases))))

(defthm canonical-regionp-of-+-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (canonical-regionp len (+ x y))
                  (canonical-regionp len (bvplus 64 x y))))
  :hints (("Goal" :in-theory (enable canonical-regionp
                                     in-region64p-of-+-arg1
                                     acl2::bvplus-of-+-arg3))))

(defthm unsigned-canonical-address-p-of-+-when-small
  (implies (and (unsigned-byte-p 46 x)
                (unsigned-byte-p 46 y))
           (unsigned-canonical-address-p (+ x y)))
  :hints (("Goal" :in-theory (enable unsigned-canonical-address-p bvlt))))

(defthm unsigned-canonical-address-p-of-bvplus-when-small
  (implies (and (unsigned-byte-p 46 x)
                (unsigned-byte-p 46 y))
           (unsigned-canonical-address-p (bvplus 64 x y)))
  :hints (("Goal" :in-theory (enable unsigned-canonical-address-p bvlt bvplus ifix))))
