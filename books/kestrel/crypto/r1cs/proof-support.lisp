; Support for proofs about R1CSes
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "portcullis")
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(include-book "kestrel/prime-fields/rules2" :dir :system) ;reduce?
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(local (include-book "kestrel/bv/bitwise" :dir :system))
(local (include-book "kestrel/bv/bvxor" :dir :system))
(local (include-book "bv"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for  ACL2::GETBIT-OF-PLUS

;; TODO: Organize this material

(defthm acl2::bitp-when-bit-listp-and-memberp
  (implies (and (acl2::bit-listp free)
                (acl2::memberp x free))
           (acl2::bitp x)))

;; (defun gen-bit-listp-assumption (vars)
;;   (declare (xargs :guard (and (symbol-listp vars)
;;                               (consp vars))))
;;   `(acl2::bit-listp ,(acl2::make-append-with-key-nest vars)))

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

;; todo: handle all combinations of negated bits
;or see add-of-neg-of-mul-of-power-of-2-other
(defthm add-of-add-of-neg-of-mul-of-2
  (implies (and (bitp bit1)
                (bitp bit2)
                (integerp extra)
                (< 2 p)
                (integerp p)
                )
           (equal (add bit1 (add (neg (mul 2 bit2 p) p) extra p) p)
                  (add -2 ;; from 2 times the 1 in 1-bit2, which comes from negating bit2
                       (add (bvxor 2
                                   2 ;== b10 because bit 1 is negated and bit 0 is not
                                   (bvcat 1 bit2 1 bit1))
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (e/d (mul
                                   ACL2::BVXOR-BLAST
                                   bvcat
                                   acl2::logapp
                                   pfield::add-of-+-arg1
                                   pfield::add-of-+-arg2
                                   acl2::bitxor-of-1-becomes-bitnot-arg1
                                   acl2::bitxor-of-1-becomes-bitnot-arg2
                                   acl2::bitnot-becomes-subtract)
                                  ( ;ACL2::BVCAT-OF-+-HIGH ;looped
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1)))))

(defthm bvxor-of-+-of-expt-of-one-less-arg2
  (implies (and (integerp x)
                (posp n))
           (equal (bvxor n extra (+ (expt 2 (+ -1 n)) x))
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm bvxor-of-+-of-expt-of-one-less-arg1
  (implies (and (integerp x)
                (posp n))
           (equal (bvxor n (+ (expt 2 (+ -1 n)) x) extra)
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm bvxor-of-+-of-expt-of-one-less-arg2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (integerp x)
                (posp n))
           (equal (bvxor n extra (+ k x))
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm bvxor-of-+-of-expt-of-one-less-arg1-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (integerp x)
                (posp n))
           (equal (bvxor n (+ k x) extra)
                  (bvcat 1
                         (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                     (acl2::getbit (- n 1) x)))
                         (- n 1)
                         (bvxor (- n 1) extra x))))
  :hints (("Goal" :in-theory (disable acl2::bvcat-of-getbit-and-x-adjacent

                                      bvcat-of-bitnot-high
                                      ))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1
  (implies (and (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* (expt 2 n) bit)))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :cases ((equal bit 0))
           :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot ACL2::BVCHOP-OF-SUM-CASES)
                           (acl2::slice-becomes-getbit
                            acl2::bvchop-1-becomes-getbit
                            acl2::bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-arg2
  (implies (and (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* bit (expt 2 n))))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :use (getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1)
           :in-theory (disable getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* k bit)))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

;;extend the mask and the BVXOR by 1 bit
;todo: gen the 2 and the 4
(defthm add-of-bvxor-of-add-of-neg-of-mul-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal k (expt 2 n))
                (bitp bit)
                (integerp extra)
                ;;(< 2 p)
                (posp n)
                (posp p))
           (equal (add (bvxor n mask bv) (add (neg (mul k bit p) p) extra p) p)
                  (add (- k) ;since the bit is negated
                       (add (bvxor (+ 1 n)
                                         ;; should often get computed:
                                         (bvcat 1 1 ;because the new bit is negated
                                                      n mask)
                                         (bvcat 1 bit n bv))
                            extra p)
                       p)))
  :hints (("Goal" :in-theory (e/d ( ;ACL2::BVXOR-BLAST
                                   bvcat
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
(defthm add-of-bvxor-of-add-of-of-mul-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal k (expt 2 n))
                (bitp bit)
                (integerp extra)
                ;;(< 2 p)
                (posp n)
                (posp p))
           (equal (add (bvxor n mask bv) (add (mul k bit p) extra p) p)
                  (add ;; no constant added since bit is not negated
                   (bvxor (+ 1 n)
                          ;; should often get computed:
                          (bvchop n mask) ; mask not extended by 0 since bit is not negated
                          (bvcat 1 bit n bv))
                   extra p)))
  :hints (("Goal" :in-theory (e/d ( ;ACL2::BVXOR-BLAST
                                   bvcat
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
(defthm add-of-mul-of-power-of-2-other
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p)
                (integerp y))
           (equal (add (mul k x p) y p)
                  (add (bvcat 1 x (+ -1 (integer-length k)) 0)
                       y
                       p)))
  :hints (("Goal" :in-theory (enable bitp bvcat
                                     acl2::logapp
                                     add acl2::power-of-2p
                                     mul))))

(defthm mul-of-power-of-2-when-bitp
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p))
           (equal (mul k x p)
                  (mod (bvcat 1 x (+ -1 (integer-length k)) 0) p)))
  :hints (("Goal" :in-theory (enable bitp bvcat
                                     acl2::logapp
                                     add acl2::power-of-2p
                                     mul))))

;; try this last?  here, the y does not fit into the bvcat
(defthm add-of-neg-of-mul-of-power-of-2-other
  (implies (and (syntaxp (quotep k))
                (acl2::power-of-2p k)
                (bitp x)
                (posp p)
                (integerp y))
           (equal (add (neg (mul k x p) p) y p)
                  (add (- k)
                       (add (bvcat 1
                                   (acl2::bitnot x)
                                   (+ -1 (integer-length k))
                                   0)
                            y
                            p)
                       p)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable bitp bvcat
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
                       (bvcat 1
                              (acl2::bitnot x)
                              (+ -1 (integer-length k))
                              0)
                       p)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))


;special case of add-of-neg-of-mul-of-power-of-2-other for k=1
(defthm add-of-neg-of-when-bitp
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
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;; Combine the BVCATs when possible
(defthm add-of-bvcat-1-of-0-and-add-of-bvcat-1-of-0-extra
  (implies (and (natp n)
                ;;(bitp bit1)
                ;;(bitp bit2)
                )
           (equal (add (bvcat 1 bit1 n 0)
                       (add (bvcat 1 bit2 (+ 1 n) 0)
                            extra
                            p)
                       p)
                  (add (bvcat 1 bit2
                              (+ 1 n)
                              (bvcat 1 bit1
                                     n 0))
                       extra
                       p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;;; Bringing a low value into a BVCAT, with an extra added value:

(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize))
           (equal (add lowval (add (bvcat highsize highval lowsize 0) extra p) p)
                  (add (bvcat highsize highval lowsize lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;todo: think about bitp vs unsigned-byte-p 1
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special
  (implies (and (bitp lowval)
                (natp highsize))
           (equal (add lowval (add (bvcat highsize highval 1 0) extra p) p)
                  (add (bvcat highsize highval 1 lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))


;swaps lowval and the bvcat
;rename
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize))
           (equal (add (bvcat highsize highval lowsize 0) (add lowval extra p) p)
                  (add (bvcat highsize highval lowsize lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))

;swaps lowval and the bvcat
;todo: think about bitp vs unsigned-byte-p 1
;rename
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
  (implies (and (bitp lowval)
                (natp highsize))
           (equal (add (bvcat highsize highval 1 0) (add lowval extra p) p)
                  (add (bvcat highsize highval 1 lowval) extra p)))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable bitp bvcat
                              acl2::logapp
                              add acl2::power-of-2p
                              mul
                              neg))))


;;; Bringing a low value into a BVCAT:

;swaps lowval and the bvcat
(defthm add-of-bvcat-of-0-when-unsigned-byte-p-arg1
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize)
                (posp p))
           (equal (add (bvcat highsize highval lowsize 0) lowval p)
                  (mod (bvcat highsize highval lowsize lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                               acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite
                               ;;acl2::<-of-bvcat
                               ))))

(defthm add-of-bvcat-of-0-when-unsigned-byte-p-arg2
  (implies (and (unsigned-byte-p lowsize lowval)
                (natp lowsize)
                (natp highsize)
                (posp p))
           (equal (add lowval (bvcat highsize highval lowsize 0) p)
                  (mod (bvcat highsize highval lowsize lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                               acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite
                               ;;acl2::<-of-bvcat
                               ))))

;; since for size 1 we'll have a bitp hyp
;; instead just rewrite (unsigned-byte-p 1 ..) to (bitp ..) ?
(defthm add-of-bvcat-of-0-when-unsigned-byte-p-arg1-bitp
  (implies (and (bitp lowval)
                (natp highsize)
                (posp p))
           (equal (add (bvcat highsize highval 1 0) lowval p)
                  (mod (bvcat highsize highval 1 lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special))))

;; since for size 1 we'll have a bitp hyp
;; instead just rewrite (unsigned-byte-p 1 ..) to (bitp ..) ?
(defthm add-of-bvcat-of-0-when-unsigned-byte-p-arg2-bitp
  (implies (and (bitp lowval)
                (natp highsize)
                (posp p))
           (equal (add lowval (bvcat highsize highval 1 0) p)
                  (mod (bvcat highsize highval 1 lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special))))

(defthmd not-of-if-of-nil-arg3-when-booleans
  (implies (and (booleanp x)
                (booleanp y))
           (equal (not (if x y nil)) ;; "not and"
                  (acl2::boolor (not x) (not y)))))

;; We negate the bit and add a constant on the outside to adjust
(defthm neg-of-bvcat-of-0-when-bitp
  (implies (and (natp lowsize)
                (posp p))
           (equal (neg (bvcat 1 bit lowsize 0) p)
                  (add (- (expt 2 lowsize))
                       (bvcat 1 (acl2::bitnot bit) lowsize 0) p)))
  :hints (("Goal" :cases ((equal 0 (acl2::getbit 0 bit)))
           :in-theory (enable add neg bvcat acl2::bitnot))))

;; We have a bit times a negative power of 2.  We negate the bit and shift it into position.
(defthm mul-of-negative-power-of-2-when-bitp
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (acl2::power-of-2p (- k))
                (bitp bit)
                (posp p))
           (equal (mul k bit p)
                  (add k ;; additive constant to likely be combined with others
                       (bvcat 1 (acl2::bitnot bit) (+ -1 (acl2::integer-length (- k))) 0) p)))
  :hints (("Goal" :cases ((equal 0 bit))
           :in-theory (enable add neg bvcat acl2::bitnot))))

(defun acl2::make-bitp-claims-aux (terms acc)
  (declare (xargs :guard (true-listp terms)))
  (if (endp terms)
      acc
    (acl2::make-bitp-claims-aux (rest terms)
                                (cons `(bitp ,(first terms)) acc))))

;; Make a list of terms that together assert that all of the TERMS satisfy bitp.
(defun acl2::make-bitp-claims (terms)
  (declare (xargs :guard (true-listp terms)))
  (acl2::make-bitp-claims-aux (acl2::reverse-list terms) nil))
