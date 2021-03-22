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

(defthm add-becomes-bvplus-33-extra
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (posp p)
                (< 8589934592 p))
           (equal (add x (add y extra p) p)
                  (add (acl2::bvplus 33 x y) extra p)))
  :hints (("Goal" :in-theory (enable add acl2::bvplus))))

;; requires the first addend to be a bvplus33, so we don't use this when we could go to a 33 bit sum
(DEFTHM ADD-BECOMES-BVPLUS-34-special
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
