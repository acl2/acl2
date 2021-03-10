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
(include-book "kestrel/bv-lists/bits-to-bytes-little2" :dir :system) ;move?
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(local (in-theory (disable acl2::bvcat-recombine))) ;todo

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

(defthm equal-of-0-and-add-of-add-of-add-of-neg-lemma
  (implies (and (fep w p)
                (integerp x)
                (integerp y)
                (integerp z)
                (posp p))
           (equal (equal 0 (add x (add y (add z (neg w p) p) p) p))
                  (equal w (add x (add y z p) p)))))

(defthm equal-of-0-and-add-of-add-of-add-of-neg-lemma-alt
  (implies (and (fep w p)
                (integerp x)
                (integerp y)
                (integerp z)
                (posp p))
           (equal (equal 0 (add x (add y (add (neg w p) z p) p) p))
                  (equal w (add x (add y z p) p)))))

(defthm equal-of-0-and-add-of-add-of-neg-lemma
  (implies (and (fep w p)
                (integerp x)
                (integerp y)
                (posp p))
           (equal (equal 0 (add x (add (neg w p) y p) p))
                  (equal w (add x y p)))))

(defthm unsigned-byte-p-of-add
  (implies (and (unsigned-byte-p (+ -1 n) x)
                (unsigned-byte-p (+ -1 n) y)
                (posp p)
                (posp n)
                (< (expt 2 n) p) ; tighten?
                )
           (unsigned-byte-p n (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

;; todo: floating point gadgets?  strings (dan boneh alligator..)

(defthm add-becomes-bvplus-33
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (posp p)
                (< 8589934592 ;;(expt 2 33) ; tighten?
                   p))
           (equal (add x y p)
                  (bvplus 33 x y)))
  :hints (("Goal" :in-theory (enable add BVPLUS))))

(defthm add-becomes-bvplus-34
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

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defthm getbit-of-add-becomes-getbit-of-bvplus-32
  (implies (and (natp n)
                (< n 32)
                (< 34359738368 ;17179869184 ;;(expt 2 34) ; tighten?
                   p)
                (posp p)
                (unsigned-byte-p 34 x) ;gen?
                (unsigned-byte-p 34 y) ; gen?
                )
           (equal (getbit n (add x y p))
                  (getbit n (bvplus 32 x y))))
  :hints (("Goal" :in-theory (enable add ACL2::BVPLUS unsigned-byte-p))))




;mostly for axe
(DEFTHMd ACL2::EQUAL-OF-CONS-when-quotep
  (IMPLIES (SYNTAXP (QUOTEP k))
           (EQUAL (EQUAL k (CONS x y))
                  (AND (CONSP k)
                       (EQUAL x (CAR k))
                       (EQUAL y (CDR k))))))


(defthm equal-of-1-and-add-when-bitp-arg1
  (implies (and (bitp x)
                (fep y p)
                (posp p)
                (< 1 p))
           (equal (equal 1 (add x y p))
                  (equal y (bitnot x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

(defthm equal-of-1-and-add-when-bitp-arg2
  (implies (and (bitp x)
                (fep y p)
                (posp p)
                (< 1 p))
           (equal (equal 1 (add y x p))
                  (equal y (bitnot x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

;or just turn equals around?
;only needed for axe
(defthmd acl2::equal-of-cons-when-quotep-alt
  (implies (syntaxp (quotep k))
           (equal (equal (cons x y) k)
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))

(defthm equal-of-constant-and-add-of-neg-arg1
  (implies (and (syntaxp (quotep k))
                (fep k p)
                (fep x p)
                (fep y p)
                (posp p))
           (equal (equal k (add (neg x p) y p))
                  (equal x (add (- k) y p)))))

(defthm equal-of-constant-and-add-of-neg-arg2
  (implies (and (syntaxp (quotep k))
                (fep k p)
                (fep x p)
                (fep y p)
                (posp p))
           (equal (equal k (add y (neg x p) p))
                  (equal x (add (- k) y p)))))

(defthm acl2::consp-when-len-equal-alt
  (implies (and (equal acl2::free (len acl2::x))
                (syntaxp (quotep acl2::free)))
           (equal (consp acl2::x)
                  (< 0 acl2::free)))
  :hints (("Goal" :in-theory (e/d (len) ()))))
