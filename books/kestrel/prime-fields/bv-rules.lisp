; Prime field and BV rules
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; This book mixes prime-fields and BV operations.

(include-book "prime-fields")
(local (include-book "prime-fields-rules"))
(include-book "../bv/bvnot")
(include-book "../bv/bvchop")
(include-book "../bv/bvxor")
(include-book "../bv/bitxor")
(include-book "../bv/bitnot")
(include-book "../bv/bvcat")
(include-book "../bv/bvplus")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/bv/rules9" :dir :system))
(local (include-book "kestrel/bv/bitwise" :dir :system))

(defthm fep-of-bvchop
  (implies (and (< (expt 2 size) p)
                (integerp p))
           (fep (acl2::bvchop size x)
                p))
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-of-bvxor
  (implies (and (< (expt 2 size) p)
                (integerp p))
           (fep (acl2::bvxor size x y) p))
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-of-bvcat
  (implies (and (< (expt 2 (+ highsize lowsize)) p)
                (natp highsize)
                (natp lowsize)
                (integerp p))
           (fep (acl2::bvcat highsize highval lowsize lowval)
                p))
  :hints (("Goal" :cases ((natp highsize))
           :in-theory (enable fep))))

(defthm fep-of-bitxor
  (implies (<= 2 p)
           (fep (acl2::bitxor x y) p))
  :hints (("Goal" :in-theory (enable fep))))

(defthmd bvnot-becomes-add-of-neg
  (implies (and (< (expt 2 n) p)
                (posp n)
                (posp p))
           (equal (acl2::bvnot n x)
                  (add (+ -1 (expt 2 n))
                       (neg (acl2::bvchop n x)
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot
                                     acl2::bvchop-of-sum-cases neg add
                                     acl2::mod-sum-cases))))

(defthm add-of-bvnot-becomes-add-of-neg
  (implies (and (integerp y)
                (integerp x)
                (posp n)
                (posp p))
           (equal (add x (acl2::bvnot n y) p)
                  (add (+ -1 (expt 2 n)) (add x (neg (acl2::bvchop n y) p) p) p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot acl2::bvchop-of-sum-cases neg add))))

(defthm add-of-bvnot-becomes-add-of-neg-arg2
  (implies (and (integerp y)
                (integerp x)
                (posp n)
                (posp p))
           (equal (add (acl2::bvnot n y) x
                       p)
                  (add (+ -1 (expt 2 n))
                       (add (neg (acl2::bvchop n y)
                                 p)
                            x
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot acl2::bvchop-of-sum-cases neg add))))

(defthm unsigned-byte-p-of-add
  (implies (and (unsigned-byte-p (+ -1 n) x)
                (unsigned-byte-p (+ -1 n) y)
                (posp p)
                (posp n)
                (< (expt 2 n) p) ; tighten?
                )
           (unsigned-byte-p n (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm equal-of-1-and-add-when-bitp-arg1
  (implies (and (bitp x)
                (fep y p)
                (integerp p)
                (< 1 p))
           (equal (equal 1 (add x y p))
                  (equal y (acl2::bitnot x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

(defthm equal-of-1-and-add-when-bitp-arg2
  (implies (and (bitp x)
                (fep y p)
                (integerp p)
                (< 1 p))
           (equal (equal 1 (add y x p))
                  (equal y (acl2::bitnot x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))


;gen the 8
; Split off the sign bit (often not used?) and turn add into bvplus
(defthmd acl2::adding-8-idiom
  (implies (and (bitp x)
                (unsigned-byte-p 8 y)
                (unsigned-byte-p 8 w)
                (unsigned-byte-p 8 z)
                ;;(natp w)
                ;;(natp z)
                (posp p)
                (< 512 p) ;tight?
                )
           (equal (equal (acl2::bvcat 1 x 8 y) (add w z p))
                  (and (equal x (acl2::getbit 8 (acl2::bvplus 9 w z)))
                       (equal y (acl2::bvplus 8 w z)))))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

;gen the 8
(defthm acl2::adding-8-idiom-alt
  (implies (and (bitp x)
                (unsigned-byte-p 8 y)
                (unsigned-byte-p 8 w)
                (unsigned-byte-p 8 z)
                ;;(natp w)
                ;;(natp z)
                (posp p)
                (< 512 p) ;tight?
                )
           (equal (equal (add w z p) (acl2::bvcat 1 x 8 y))
                  (and (equal x (acl2::getbit 8 (acl2::bvplus 9 w z)))
                       (equal y (acl2::bvplus 8 w z)))))
  :hints (("Goal" :use (:instance acl2::adding-8-idiom))))

;drop?  does this improve things?
(defthmd add-of-bvcat-and-add-of-bvcat-combine-interloper
  (implies (and (unsigned-byte-p lowsize lowval)
                (<= lowsize 31)
                (integerp extra)
                (natp highsize)
                )
           (equal (add (acl2::bvcat highsize highval lowsize 0)
                       ;; todo: why does the single bit here intercede?
                       (add (acl2::bvcat 1 bit 31 lowval)
                            extra
                            p)
                       p)
                  ;; why does this swap the order of the bvcats?:
                  (add (acl2::bvcat 1 bit 31 0)
                       (add (acl2::bvcat highsize highval lowsize lowval)
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvcat acl2::logapp add acl2::power-of-2p mul neg))))

;drop the other?
;; moves the lowval into the 0 of the other bvcat
(defthmd add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
  (implies (and (syntaxp (not (quotep lowval))) ;prevent loops (really we just care about 0)
                (< lowsize lowsize2) ;todo: think about this, trying to make sure we make progress (we prefer the lowval to be in the first bvcat since there is extra space in the second cat)
                (unsigned-byte-p lowsize lowval)
                ;(<= lowsize 31) ;why?
                ;(integerp extra)
                (natp highsize)
                (natp lowsize2))
           (equal (add (acl2::bvcat highsize highval lowsize 0)
                       ;; todo: why does the highval2 here intercede in the blake proof?
                       (add (acl2::bvcat highsize2 highval2 lowsize2 lowval)
                            extra
                            p)
                       p)
                  (add (acl2::bvcat highsize highval lowsize lowval)
                       (add (acl2::bvcat highsize2 highval2 lowsize2 0)
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvcat acl2::logapp add mul neg))))

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
                  (acl2::bvplus 33 x y)))
  :hints (("Goal" :in-theory (enable add acl2::BVPLUS))))

(defthmd add-becomes-bvplus-34
  (implies (and (unsigned-byte-p 33 x)
                (unsigned-byte-p 33 y)
                (posp p)
                (< 17179869184 ;;(expt 2 34) ; tighten?
                   p))
           (equal (add x y p)
                  (acl2::bvplus 34 x y)))
  :hints (("Goal" :in-theory (enable add ACL2::BVPLUS))))

;todo: uncomment:
;(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-34 1) ;try this late

(defthmd add-becomes-bvplus-33-extra
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (posp p)
                (< 8589934592 p))
           (equal (add x (add y extra p) p)
                  (add (acl2::bvplus 33 x y) extra p)))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

(defthmd add-becomes-bvplus-34-extra
  (implies (and (unsigned-byte-p 33 x)
                (unsigned-byte-p 33 y)
                (posp p)
                (< 17179869184 p))
           (equal (add x (add y extra p) p)
                  (add (acl2::bvplus 34 x y) extra p)))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-34-extra 1) ;try this late

(defthmd add-becomes-bvplus-35
  (implies (and (unsigned-byte-p 34 x)
                (unsigned-byte-p 34 y)
                (posp p)
                (< (expt 2 35) p))
           (equal (add x y p)
                  (acl2::bvplus 35 x y)))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-35 2) ;try this late

(defthmd add-becomes-bvplus-36
  (implies (and (unsigned-byte-p 35 x)
                (unsigned-byte-p 35 y)
                (posp p)
                (< (expt 2 36) p))
           (equal (add x y p)
                  (acl2::bvplus 36 x y)))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-36 3) ;try this late

;; requires the first addend to be a bvplus33, so we don't use this when we could go to a 33 bit sum
(DEFTHMd ADD-BECOMES-BVPLUS-34-special
  (IMPLIES (AND (UNSIGNED-BYTE-P 33 Y)
                (POSP P)
                (< 17179869184 P))
           (EQUAL (ADD (acl2::bvplus 33 x1 x2) Y P)
                  (acl2::BVPLUS 34 (acl2::bvplus 33 x1 x2) Y)))
  :hints (("Goal" :use (:instance ADD-BECOMES-BVPLUS-34
                                  (x (acl2::bvplus 33 x1 x2)))
           :in-theory (disable ADD-BECOMES-BVPLUS-34))))

;; try this relatively late, so we get a chance to try add-becomes-bvplus-33 first:
(table acl2::axe-rule-priorities-table 'add-becomes-bvplus-34 1)

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
;;            (equal (acl2::getbit n (add x y p))
;;                   (acl2::getbit n (acl2::bvplus 32 x y))))
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
           (equal (acl2::getbit n (add x y p))
                  (acl2::getbit n (acl2::bvplus 32 x y))))
  :hints (("Goal"
           :use (:instance acl2::mod-when-< (x (+ x y)) (y p))
           :in-theory (e/d (add acl2::bvplus unsigned-byte-p
                                acl2::not-power-of-2p-when-oddp)
                           (acl2::equal-of-mod-same-arg1 oddp)))))

;; todo: handle all combinations of negated bits
;or see add-of-neg-of-mul-of-power-of-2-other
(defthmd add-of-add-of-neg-of-mul-of-2
  (implies (and (bitp bit1)
                (bitp bit2)
                (integerp extra)
                (< 2 p)
                (integerp p)
                )
           (equal (add bit1 (add (neg (mul 2 bit2 p) p) extra p) p)
                  (add -2 ;; from 2 times the 1 in 1-bit2, which comes from negating bit2
                       (add (acl2::bvxor 2
                                   2 ;== b10 because bit 1 is negated and bit 0 is not
                                   (acl2::bvcat 1 bit2 1 bit1))
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (e/d (mul
                                   ACL2::BVXOR-BLAST
                                   acl2::bvcat
                                   acl2::logapp
                                   pfield::add-of-+-arg1
                                   pfield::add-of-+-arg2
                                   acl2::bitxor-of-1-becomes-bitnot-arg1
                                   acl2::bitxor-of-1-becomes-bitnot-arg2
                                   acl2::bitnot-becomes-subtract)
                                  ( ;ACL2::BVCAT-OF-+-HIGH ;looped
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1)))))

;;extend the mask and the BVXOR by 1 bit
;todo: gen the 2 and the 4
(defthmd add-of-bvxor-of-add-of-neg-of-mul-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal k (expt 2 n))
                (bitp bit)
                (integerp extra)
                ;;(< 2 p)
                (posp n)
                (posp p))
           (equal (add (acl2::bvxor n mask bv) (add (neg (mul k bit p) p) extra p) p)
                  (add (- k) ;since the bit is negated
                       (add (acl2::bvxor (+ 1 n)
                                         ;; should often get computed:
                                         (acl2::bvcat 1 1 ;because the new bit is negated
                                                      n mask)
                                         (acl2::bvcat 1 bit n bv))
                            extra p)
                       p)))
  :hints (("Goal" :in-theory (e/d ( ;ACL2::BVXOR-BLAST
                                   acl2::bvcat
                                   mul
                                   acl2::logapp
                                   pfield::ADD-OF-+-ARG1
                                   pfield::ADD-OF-+-ARG2
                                   ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
                                   acl2::bitnot-becomes-subtract
                                   acl2::bvxor-of-+-of-1-split
                                   pfield::add-of---arg1-fixed)
                                  (;ACL2::BVCAT-OF-+-HIGH
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1
                                   ;ACL2::BVCAT-OF-*-LOW
                                   ;PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE ;looped
                                   )))))

;; in this one, the bit is not negated
(defthmd add-of-bvxor-of-add-of-of-mul-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal k (expt 2 n))
                (bitp bit)
                (integerp extra)
                ;;(< 2 p)
                (posp n)
                (posp p))
           (equal (add (acl2::bvxor n mask bv) (add (mul k bit p) extra p) p)
                  (add ;; no constant added since bit is not negated
                   (acl2::bvxor (+ 1 n)
                          ;; should often get computed:
                          (acl2::bvchop n mask) ; mask not extended by 0 since bit is not negated
                          (acl2::bvcat 1 bit n bv))
                   extra p)))
  :hints (("Goal" :in-theory (e/d ( ;ACL2::BVXOR-BLAST
                                   acl2::bvcat
                                   acl2::logapp
                                   pfield::ADD-OF-+-ARG1
                                   pfield::ADD-OF-+-ARG2
                                   ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
                                   acl2::bitnot-becomes-subtract
                                   acl2::bvxor-of-+-of-1-split
                                   mul)
                                  ( ;ACL2::BVCAT-OF-+-HIGH
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1
                                   ;;ACL2::BVCAT-OF-*-LOW
                                   ;;PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE ;looped
                                   )))))

;; todo: these may allow us to first go to bvcats of bitnots before introducing xor masks:

;; try this last?  here, the y does not fit into the bvcat
;rename?
;drop in favor of mul-of-power-of-2-when-bitp?
(defthmd add-of-mul-of-power-of-2-other
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p)
                (integerp y))
           (equal (add (mul k x p) y p)
                  (add (acl2::bvcat 1 x (+ -1 (integer-length k)) 0)
                       y
                       p)))
  :hints (("Goal" :in-theory (enable bitp acl2::bvcat
                                     acl2::logapp
                                     add acl2::power-of-2p
                                     mul))))

(defthmd mul-of-power-of-2-when-bitp
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p))
           (equal (mul k x p)
                  (mod (acl2::bvcat 1 x (+ -1 (integer-length k)) 0) p)))
  :hints (("Goal" :in-theory (enable bitp acl2::bvcat
                                     acl2::logapp
                                     add acl2::power-of-2p
                                     mul))))

;; try this last?  here, the y does not fit into the bvcat
(defthmd add-of-neg-of-mul-of-power-of-2-other
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p)
                (integerp y))
           (equal (add (neg (mul k x p) p) y p)
                  (add (- k)
                       (add (acl2::bvcat 1
                                   (acl2::bitnot x)
                                   (+ -1 (integer-length k))
                                   0)
                            y
                            p)
                       p)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

(defthmd neg-of-mul-of-power-of-2
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p))
           (equal (neg (mul k x p) p)
                  (add (- k)
                       (acl2::bvcat 1
                              (acl2::bitnot x)
                              (+ -1 (integer-length k))
                              0)
                       p)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))


;special case of add-of-neg-of-mul-of-power-of-2-other for k=1
(defthmd add-of-neg-of-when-bitp
  (implies (and (bitp x)
                (integerp y)
                (posp p))
           (equal (add (neg x p) y p)
                  (add (- 1)
                       (add (acl2::bitnot x)
                            y
                            p)
                       p)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;; Combine the BVCATs when possible
(defthmd add-of-bvcat-1-of-0-and-add-of-bvcat-1-of-0-extra
  (implies (and (natp n)
                ;;(bitp bit1)
                ;;(bitp bit2)
                )
           (equal (add (acl2::bvcat 1 bit1 n 0)
                       (add (acl2::bvcat 1 bit2 (+ 1 n) 0)
                            extra
                            p)
                       p)
                  (add (acl2::bvcat 1 bit2
                              (+ 1 n)
                              (acl2::bvcat 1 bit1
                                     n 0))
                       extra
                       p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;;; Bringing a low value into a BVCAT, with an extra added value:

(defthmd add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize))
           (equal (add lowval (add (acl2::bvcat highsize highval lowsize 0) extra p) p)
                  (add (acl2::bvcat highsize highval lowsize lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;todo: think about bitp vs unsigned-byte-p 1
(defthmd add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special
  (implies (and (bitp lowval)
                (natp highsize))
           (equal (add lowval (add (acl2::bvcat highsize highval 1 0) extra p) p)
                  (add (acl2::bvcat highsize highval 1 lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))


;swaps lowval and the bvcat
;rename
(defthmd add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize))
           (equal (add (acl2::bvcat highsize highval lowsize 0) (add lowval extra p) p)
                  (add (acl2::bvcat highsize highval lowsize lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;swaps lowval and the bvcat
;todo: think about bitp vs unsigned-byte-p 1
;rename
(defthmd add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
  (implies (and (bitp lowval)
                (natp highsize))
           (equal (add (acl2::bvcat highsize highval 1 0) (add lowval extra p) p)
                  (add (acl2::bvcat highsize highval 1 lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp acl2::bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))


;;; Bringing a low value into a BVCAT:

;swaps lowval and the bvcat
(defthmd add-of-bvcat-of-0-when-unsigned-byte-p-arg1
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize)
                (posp p))
           (equal (add (acl2::bvcat highsize highval lowsize 0) lowval p)
                  (mod (acl2::bvcat highsize highval lowsize lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                               acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite
                               ;;acl2::<-of-bvcat
                               ))))

(defthmd add-of-bvcat-of-0-when-unsigned-byte-p-arg2
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize)
                (posp p))
           (equal (add lowval (acl2::bvcat highsize highval lowsize 0) p)
                  (mod (acl2::bvcat highsize highval lowsize lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                               acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite
                               ;;acl2::<-of-bvcat
                               ))))

;; since for size 1 we'll have a bitp hyp
;; instead just rewrite (unsigned-byte-p 1 ..) to (bitp ..) ?
(defthmd add-of-bvcat-of-0-when-unsigned-byte-p-arg1-bitp
  (implies (and (bitp lowval)
                (natp highsize)
                (posp p))
           (equal (add (acl2::bvcat highsize highval 1 0) lowval p)
                  (mod (acl2::bvcat highsize highval 1 lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special))))

;; since for size 1 we'll have a bitp hyp
;; instead just rewrite (unsigned-byte-p 1 ..) to (bitp ..) ?
(defthmd add-of-bvcat-of-0-when-unsigned-byte-p-arg2-bitp
  (implies (and (bitp lowval)
                (natp highsize)
                (posp p))
           (equal (add lowval (acl2::bvcat highsize highval 1 0) p)
                  (mod (acl2::bvcat highsize highval 1 lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special))))

;; We negate the bit and add a constant on the outside to adjust
(defthmd neg-of-bvcat-of-0-when-bitp
  (implies (and (natp lowsize)
                (posp p))
           (equal (neg (acl2::bvcat 1 bit lowsize 0) p)
                  (add (- (expt 2 lowsize))
                       (acl2::bvcat 1 (acl2::bitnot bit) lowsize 0) p)))
  :hints (("Goal" :cases ((equal 0 (acl2::getbit 0 bit)))
           :in-theory (enable add neg acl2::bvcat acl2::bitnot))))

;; We have a bit times a negative power of 2.  We negate the bit and shift it into position.
(defthmd mul-of-negative-power-of-2-when-bitp
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (acl2::power-of-2p (- k))
                (bitp bit)
                (posp p))
           (equal (mul k bit p)
                  (add k ;; additive constant to likely be combined with others
                       (acl2::bvcat 1 (acl2::bitnot bit) (+ -1 (acl2::integer-length (- k))) 0) p)))
  :hints (("Goal" :cases ((equal 0 bit))
           :in-theory (enable add neg acl2::bvcat acl2::bitnot))))

;not true?
;; (DEFTHM PFIELD::MUL-WHEN-NOT-fep-ARG1-CHEAP
;;   (IMPLIES (NOT (fep PFIELD::X PFIELD::P))
;;            (EQUAL (MUL PFIELD::X PFIELD::Y PFIELD::P)
;;                   (MUL 0 PFIELD::Y PFIELD::P)))
;;   :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST (1)))
;;   :HINTS (("Goal"
;;            :use (:instance ACL2::MOD-OF-*-OF-MOD-2 (y pfield::x) (x pfield::y) (z pfield::p))
;;            :IN-THEORY (E/d (MUL fep) (ACL2::MOD-OF-*-OF-MOD-2
;;                                       ACL2::MOD-OF-*-OF-MOD)))))

;; (defthm equal-of-0-and-mul-of-add-of-1-and-neg-same-gen
;;   (implies (and ;(fep x prime)
;;                 (rtl::primep prime))
;;            (equal (equal 0 (mul x (add 1 (neg x prime) prime) prime))
;;                   (bitp (mod (ifix x) p))))
;;   :hints (("Goal" :use (:instance constrain-to-be-bit-correct)
;;            :in-theory (e/d ()
;;                            (constrain-to-be-bit-correct
;;                             PFIELD::NEG-OF-* ;looped
;;                             )))))
