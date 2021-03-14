; Support for proofs about R1CSes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; Proof support for R1CS proofs -- TODO: Move this material to libraries

(include-book "portcullis")
(include-book "proof-support") ;reduce
(include-book "kestrel/crypto/r1cs/fe-listp" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/bv-rules" :dir :system)
;(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system) ;drop?
(include-book "kestrel/arithmetic-light/lg" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm add-of-bvcat-and-add-of-bvcat-combine-interloper
  (implies (and (unsigned-byte-p lowsize lowval)
                (<= lowsize 31)
                (integerp extra)
                (natp highsize)
                )
           (equal (add (bvcat highsize highval lowsize 0)
                       ;; todo: why does the single bit here intercede?
                       (add (bvcat 1 bit 31 lowval)
                            extra
                            p)
                       p)
                  ;; why does this swap the order of the bvcats?:
                  (add (bvcat 1 bit 31 0)
                       (add (bvcat highsize highval lowsize lowval)
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable bvcat acl2::logapp add acl2::power-of-2p mul neg))))

;drop the other?
;; moves the lowval into the 0 of the other bvcat
(defthm add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
  (implies (and (syntaxp (not (quotep lowval))) ;prevent loops (really we just care about 0)
                (< lowsize lowsize2) ;todo: think about this, trying to make sure we make progress (we prefer the lowval to be in the first bvcat since there is extra space in the second cat)
                (unsigned-byte-p lowsize lowval)
                ;(<= lowsize 31) ;why?
                ;(integerp extra)
                (natp highsize)
                (natp lowsize2))
           (equal (add (bvcat highsize highval lowsize 0)
                       ;; todo: why does the highval2 here intercede in the blake proof?
                       (add (bvcat highsize2 highval2 lowsize2 lowval)
                            extra
                            p)
                       p)
                  (add (bvcat highsize highval lowsize lowval)
                       (add (bvcat highsize2 highval2 lowsize2 0)
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable bvcat acl2::logapp add power-of-2p mul neg))))

;; Try these rules after most rules (which have priority 0), since they have free vars:
;; todo: wrap this command into a nice wrapper that prevents accidentally giving the wrong table name:
(table acl2::axe-rule-priorities-table 'acl2::bitp-when-bit-listp-and-memberp 1)

;; todo: floating point gadgets?  strings (dan boneh alligator..)

(defthmd add-becomes-bvplus-33
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (posp p)
                (< 8589934592 ;;(expt 2 33) ; tighten?
                   p))
           (equal (add x y p)
                  (bvplus 33 x y)))
  :hints (("Goal" :in-theory (enable add BVPLUS))))

(defthmd add-becomes-bvplus-34
  (implies (and (unsigned-byte-p 33 x)
                (unsigned-byte-p 33 y)
                (posp p)
                (< 17179869184 ;;(expt 2 34) ; tighten?
                   p))
           (equal (add x y p)
                  (bvplus 34 x y)))
  :hints (("Goal" :in-theory (enable add ACL2::BVPLUS))))

;try the other one first
(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-34 1)

;move
(defthm <-of-expt-2-and-one-less-than-integer-length
  (implies (posp n)
           (equal (< (expt 2 (+ -1 (integer-length n))) n)
                  (not (power-of-2p n))))
  :hints (("Goal" :in-theory (e/d (integer-length power-of-2p expt) (acl2::expt-hack)))))

;move
(defthm <-of-expt-2-of-lg-same
  (implies (posp n)
           (equal (< (expt 2 (acl2::lg n)) n)
                  (not (power-of-2p n))))
  :hints (("Goal" :in-theory (enable acl2::lg))))

;move
(defthm <-of-expt-2-of-lg-same-linear
  (implies (and (not (power-of-2p n))
                (posp n))
           (< (expt 2 (acl2::lg n)) n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable acl2::lg))))

;move
(defthm not-power-of-2p-when-oddp
  (implies (and (oddp n)
                (< 1 n))
           (not (power-of-2p n)))
  :hints (("Goal" :in-theory (enable power-of-2p))))

;; ;; Turns add into a 32-bit sum (even if N is smaller than 31).
;; (defthmd getbit-of-add-becomes-getbit-of-bvplus-32
;;   (implies (and (< n 32)
;;                 ;; ensure the mod p does nothing:
;;                 (< ;34359738368 ;
;;                  (expt 2 35) ; tighten?
;;                    p)
;;                 (integerp p)
;;                 (unsigned-byte-p 34 x) ;gen?
;;                 (unsigned-byte-p 34 y) ; gen?
;;                 (natp n)
;;                 )
;;            (equal (getbit n (add x y p))
;;                   (getbit n (bvplus 32 x y))))
;;   :hints (("Goal" :in-theory (enable add acl2::bvplus unsigned-byte-p))))

;; Usually p will be a constant
(defthmd getbit-of-add-becomes-getbit-of-bvplus-32
  (implies (and (unsigned-byte-p (+ -1 (acl2::lg p)) x)
                (unsigned-byte-p (+ -1 (acl2::lg p)) y)
                (< n 32)
                (< 1 p)
                (oddp p)
                (integerp p)
                (natp n))
           (equal (getbit n (add x y p))
                  (getbit n (bvplus 32 x y))))
  :hints (("Goal"
           :use (:instance acl2::mod-when-< (x (+ x y)) (y p))
           :in-theory (e/d (add acl2::bvplus unsigned-byte-p)
                           (acl2::equal-of-mod-same-arg1 oddp)))))
