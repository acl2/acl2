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
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(include-book "kestrel/bv/rules7" :dir :system)
(include-book "kestrel/bv/rotate" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system) ;drop?
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/axe/rules3" :dir :system)) ; for ACL2::MOVE-MINUS-HACK2?
(local (include-book "kestrel/axe/basic-rules" :dir :system))

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

(defthm getbit-of-bvplus-tighten-to-32
  (implies (and (< 32 size) ; prevent loops
                (< n 32)
                (natp n)
                (natp size))
           (equal (getbit n (bvplus size x y))
                  (getbit n (bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (ACL2::GETBIT-TRIM)))))

;gen
(defthmd slice-of-bvplus-tighten-to-32
  (implies (and (< 32 n)
                (< high 32)
                (<= low high) ;drop?
                (natp low)
                (natp high)
                (natp n))
           (equal (slice high low (bvplus n x y))
                  (slice high low (bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (ACL2::GETBIT-TRIM)))))

(defthmd bvchop-of-bvplus-tighten-to-32
  (implies (and (< 32 n)
                (natp n))
           (equal (bvchop 32 (bvplus n x y))
                  (bvchop 32 (bvplus 32 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (ACL2::GETBIT-TRIM)))))



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

(defthm bvplus-of-bvplus-trim-to-32-arg1
  (implies (and (< 32 n)
                (natp n))
           (equal (bvplus 32 (bvplus n x y) z)
                  (bvplus 32 (bvplus 32 x y) z)))
  :hints (("Goal" :in-theory (enable acl2::bvplus))))

(defthm bvplus-of-bvplus-trim-to-32-arg2
  (implies (and (< 32 n)
                (natp n))
           (equal (bvplus 32 z (bvplus n x y))
                  (bvplus 32 (bvplus 32 x y) z)))
  :hints (("Goal" :in-theory (enable acl2::bvplus))))

(defthm bvcat-of-slice-tighten
  (implies (and (<= highsize (- high low))
                (<= low high)
                (natp highsize)
                (natp low)
                (natp high))
           (equal (bvcat highsize (slice high low x) lowsize lowval)
                  (bvcat highsize (slice (+ -1 low highsize) low x) lowsize lowval))))

(defthm bvcat-of-bitnot-low
  (implies (natp highsize)
           (equal (bvcat highsize highval 1 (bitnot lowbit))
                  (bvxor (+ highsize 1)
                         1
                         (bvcat highsize highval 1 lowbit)))))

(defthm bvcat-of-bitnot-high
  (implies (natp lowsize)
           (equal (bvcat 1 (bitnot highval) lowsize lowval)
                  (bvxor (+ 1 lowsize)
                               (bvcat 1 1 lowsize 0) ;todo: simplify?
                               (bvcat 1 highval lowsize lowval)))))

(defthm bvcat-of-bvnot-low
  (implies (and (natp highsize)
                (posp lowsize) ;gen
                )
           (equal (bvcat highsize highval lowsize (bvnot lowsize lowbit))
                  (bvxor (+ highsize lowsize)
                               (bvchop lowsize -1) ;todo: improve?
                               (bvcat highsize highval lowsize lowbit))))
  :hints (("Goal" :in-theory (enable ACL2::BVXOR-ALL-ONES-HELPER-ALT))))

(defthm bvcat-of-bvxor-low-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize (bvxor lowsize k lowval))
                  (bvxor (+ highsize lowsize)
                               (bvchop lowsize k)
                               (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bvxor-high-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize (bvxor highsize k highval) lowsize lowval)
                  (bvxor (+ highsize lowsize)
                               (bvcat highsize k lowsize 0) ;should get computed
                               (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bitxor-low-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp highsize))
           (equal (bvcat highsize highval 1 (bitxor k lowval))
                  (bvxor (+ highsize 1)
                               (bvchop 1 k)
                               (bvcat highsize highval 1 lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bitxor-high-when-quotep
  (implies (and (syntaxp (quotep k))
                (natp lowsize))
           (equal (bvcat 1 (bitxor k highval) lowsize lowval)
                  (bvxor (+ 1 lowsize)
                               (bvcat 1 k lowsize 0) ;should get computed
                               (bvcat 1 highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize)))))

(defthm bvcat-of-bvnot-high
  (implies (and (natp lowsize)
                (natp highsize))
           (equal (bvcat highsize (bvnot highsize highval) lowsize lowval)
                  (bvxor (+ highsize lowsize)
                               (bvcat highsize (bvchop highsize -1) lowsize 0) ;todo: simplify?
                               (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :cases ((equal 0 highsize))
           :in-theory (enable ACL2::BVXOR-ALL-ONES-HELPER-ALT))))

(defthm bvcat-of-slice-same-becomes-rightrotate
  (implies (and (equal upper-bit 31) ;gen!
                (equal upper-bit (+ -1 highsize lowsize))
                (natp highsize)
                (natp lowsize)
                (< lowsize upper-bit)
                (< highsize upper-bit)
                (posp highsize) ;gen
                )
           (equal (BVCAT highsize x lowsize (SLICE upper-bit highsize x))
                  (acl2::rightrotate (+ 1 upper-bit) highsize x)))
  :hints (("Goal" :in-theory (enable ;ACL2::RIGHTROTATE
                              ))))

(defthm bvcat-of-bitxor-and-bitxor-adjacent-bits
  (implies (and (natp low1)
                (equal high1 (+ 1 low1))
                (natp low2)
                (equal high2 (+ 1 low2)))
           (equal (bvcat 1 (bitxor (getbit high1 x) (getbit high2 y))
                               1 (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvxor 2 (slice high1 low1 x) (slice high2 low2 y)))))

;; has the first bitxor commuted
(defthm bvcat-of-bitxor-and-bitxor-adjacent-bits-alt
  (implies (and (natp low1)
                (equal high1 (+ 1 low1))
                (natp low2)
                (equal high2 (+ 1 low2)))
           (equal (bvcat 1 (bitxor (getbit high2 y) (getbit high1 x))
                               1 (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvxor 2 (slice high1 low1 x) (slice high2 low2 y)))))

(defthm bvxor-of-slice-trim
  (implies (and (< n (+ 1 (- high low)))
                (natp n)
                (< low high)
                (natp high)
                (natp low))
           (equal (bvxor n (slice high low x) y)
                  (bvxor n (slice (+ -1 (+ n low)) low x) y))))

(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat 1 (bitxor (getbit high1 x) (getbit high2 y))
                               n (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ 1 n)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

;; This version commutes the args to the first bitxor
(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat 1 (bitxor (getbit high2 y) (getbit high1 x))
                               n (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ 1 n)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

(defthm bvcat-of-bvxor-and-bvxor-adjacent-bits
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ n1 n2)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

;; This version commutes the args to the first bvxor
(defthm bvcat-of-bvxor-and-bvxor-adjacent-bits-alt
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                ;(<= mid2 high2)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvxor (+ n1 n2)
                               (slice high1 low1 x) (slice high2 low2 y))))
  :hints (("Goal" :in-theory (enable))))

(defthm bvcat-of-bvxor-and-bitxor-adjacent-bits
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                ;(<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1) ;why?
                (posp mid2) ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvxor (+ 1 n1)
                               (slice high1 mid1minus1 x)
                               (slice high2 mid2minus1 y))))
  :hints (("Goal" :in-theory (enable))))

;;this one commutes the args of the first bvxor
(defthm bvcat-of-bvxor-and-bitxor-adjacent-bits-alt
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                (<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1) ;why?
                (posp mid2) ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                )
           (equal (bvcat n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvxor (+ 1 n1)
                               (slice high1 mid1minus1 x)
                               (slice high2 mid2minus1 y))))
  :hints (("Goal" :in-theory (enable))))

(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(acl2::defopeners acl2::bits-to-bytes-little)

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

;only needed for axe
(DEFTHMd ACL2::BVCAT-EQUAL-REWRITE-CONSTANT-alt
  (IMPLIES
   (AND (SYNTAXP (QUOTEP ACL2::X))
        (SYNTAXP (QUOTEP ACL2::HIGHSIZE))
        (SYNTAXP (QUOTEP ACL2::LOWSIZE))
        (NATP ACL2::LOWSIZE)
        (NATP ACL2::HIGHSIZE))
   (EQUAL
    (EQUAL (BVCAT ACL2::HIGHSIZE ACL2::HIGHVAL
                        ACL2::LOWSIZE ACL2::LOWVAL)
           ACL2::X)
    (AND
     (UNSIGNED-BYTE-P (+ ACL2::LOWSIZE ACL2::HIGHSIZE)
                      ACL2::X)
     (EQUAL (BVCHOP ACL2::LOWSIZE ACL2::X)
            (BVCHOP ACL2::LOWSIZE ACL2::LOWVAL))
     (EQUAL (SLICE (+ -1 ACL2::LOWSIZE ACL2::HIGHSIZE)
                         ACL2::LOWSIZE ACL2::X)
            (BVCHOP ACL2::HIGHSIZE ACL2::HIGHVAL))))))

;or just turn equals around?
;only needed for axe
(defthmd acl2::equal-of-cons-when-quotep-alt
  (implies (syntaxp (quotep k))
           (equal (equal (cons x y) k)
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))

(defthm bvxor-of-constant-trim-arg1
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (integerp size))
           (equal (bvxor size k x)
                  (bvxor size (bvchop size k) x))))

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

(defthm equal-of-bitnot-and-bitnot
  (equal (equal (bitnot x) (bitnot y))
         (equal (getbit 0 x) (getbit 0 y)))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm bvcat-of-bvxor-and-bvxor-adjacent-bits-extra-left-assoc
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal n1+zsize (+ n1 zsize))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat n1+zsize (bvcat zsize z n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y)))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize z
                               (+ n1 n2)
                               (bvxor (+ n1 n2)
                                            (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :in-theory (enable))))

;commutes the first bvxor
(defthm bvcat-of-bvxor-and-bvxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal high1minus1 (+ -1 mid1))
                (equal high2minus1 (+ -1 mid2))
                (equal n2 (+ 1 (- high1minus1 low1)))
                (equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal n1+zsize (+ n1 zsize))
                (< low1 high1minus1)
                (< low2 high2minus1)
                (<= mid1 high1)
                (<= mid1 high2)
                ;;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat n1+zsize (bvcat zsize z n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x)))
                               n2 (bvxor n2 (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize z
                               (+ n1 n2)
                               (bvxor (+ n1 n2)
                                            (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :in-theory (enable))))

(defthm bvcat-of-bitxor-and-bitxor-adjacent-bits-extra-left-assoc
  (implies (and (equal zsize+1 (+ 1 zsize))
                (equal high1 (+ 1 low1))
                (equal high2 (+ 1 low2))
                (natp zsize)
                (natp low1)
                (natp low2))
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high1 x) (getbit high2 y)))
                               1
                               (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvcat zsize
                               z
                               2
                               (bvxor 2 (slice high1 low1 x) (slice high2 low2 y))))))

;commutes the first xor
(defthm bvcat-of-bitxor-and-bitxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal zsize+1 (+ 1 zsize))
                (equal high1 (+ 1 low1))
                (equal high2 (+ 1 low2))
                (natp zsize)
                (natp low1)
                (natp low2))
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high2 y) (getbit high1 x)))
                               1
                               (bitxor (getbit low1 x) (getbit low2 y)))
                  (bvcat zsize
                               z
                               2
                               (bvxor 2 (slice high1 low1 x) (slice high2 low2 y))))))

(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits-extra-left-assoc
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal zsize+1 (+ 1 zsize))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high1 x) (getbit high2 y)))
                               n
                               (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize
                               z
                               (+ 1 n)
                               (bvxor (+ 1 n)
                                            (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :in-theory (enable))))

;commutes the first xor
(defthm bvcat-of-bitxor-and-bvxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal high1minus1 (+ -1 high1))
                (equal high2minus1 (+ -1 high2))
                (equal zsize+1 (+ 1 zsize))
                (equal n (+ 1 (- high1minus1 low1)))
                (equal n (+ 1 (- high2minus1 low2)))
                (<= low1 high1minus1)
                ;(<= low2 high2minus1)
                (natp low1)
                (natp low2)
                (natp high1)
                (natp high2)
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+1
                               (bvcat zsize z 1 (bitxor (getbit high2 y) (getbit high1 x)))
                               n
                               (bvxor n (slice high1minus1 low1 x) (slice high2minus1 low2 y)))
                  (bvcat zsize
                               z
                               (+ 1 n)
                               (bvxor (+ 1 n)
                                            (slice high1 low1 x) (slice high2 low2 y)))))
  :hints (("Goal" :in-theory (enable))))

(defthm bvcat-of-bvxor-and-bitxor-adjacent-bits-extra-left-assoc
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal zsize+n1 (+ n1 zsize))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                ;;(<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1)  ;why?
                (posp mid2)  ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+n1
                               (bvcat zsize z n1 (bvxor n1 (slice high1 mid1 x) (slice high2 mid2 y)))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvcat zsize z
                               (+ 1 n1)
                               (bvxor (+ 1 n1)
                                            (slice high1 mid1minus1 x)
                                            (slice high2 mid2minus1 y)))))
  :hints (("Goal" :in-theory (enable))))

;has the first xor commuted
(defthm bvcat-of-bvxor-and-bitxor-adjacent-bits-extra-left-assoc-alt
  (implies (and (equal mid1minus1 (+ -1 mid1))
                (equal mid2minus1 (+ -1 mid2))
                ;;(equal n2 (+ 1 (- high1minus1 low1)))
                ;;(equal n2 (+ 1 (- high2minus1 low2)))
                (equal n1 (+ 1 (- high1 mid1)))
                (equal n1 (+ 1 (- high2 mid2)))
                (equal zsize+n1 (+ n1 zsize))
                ;;(< low1 high1minus1)
                ;;(< low2 high2minus1)
                (<= mid1 high1)
                ;;(<= mid2 high2)
                ;;(<= low2 high2minus1)
                ;;(natp low1)
                ;;(natp low2)
                (natp mid1)
                (natp mid2)
                (natp high1)
                (natp high2)
                (posp mid1)  ;why?
                (posp mid2)  ;why?
                (posp high1) ;why?
                (posp high2) ;why?
                (natp zsize)
                )
           (equal (bvcat zsize+n1
                               (bvcat zsize z n1 (bvxor n1 (slice high2 mid2 y) (slice high1 mid1 x)))
                               1 (bitxor (getbit mid1minus1 x) (getbit mid2minus1 y)))
                  (bvcat zsize z
                               (+ 1 n1)
                               (bvxor (+ 1 n1)
                                            (slice high1 mid1minus1 x)
                                            (slice high2 mid2minus1 y)))))
  :hints (("Goal" :in-theory (enable))))

;; this is for when we are associating to the left (unusual)
(defthmd acl2::bvcat-of-getbit-and-getbit-adjacent-2-left-assoc
  (implies (and (equal n (+ 1 m))
                (equal j (+ 1 size))
                (natp size)
                (natp m))
           (equal (bvcat j (bvcat size y 1 (getbit n x))
                               1 (getbit m x))
                  (bvcat size y 2 (slice n m x)))))

(defthmd acl2::bvcat-of-getbit-and-slice-adjacent-2-left-assoc
  (implies (and (equal n (+ 1 high))
                (equal j (+ 1 size))
                (equal k (+ 1 (- high low)))
                (<= low high)
                (natp size)
                (natp high)
                (natp low))
           (equal (bvcat j (bvcat size y 1 (getbit n x))
                               k (slice high low x))
                  (bvcat size
                               y
                               (+ 1 (- n low))
                               (slice n low x)))))

(defthmd acl2::bvcat-of-slice-and-slice-adjacent-2-left-assoc
  (implies (and (equal low1 (+ 1 high2))
                (equal size1 (+ size size2))
                (equal size2 (+ 1 (- high1 low1)))
                (equal size3 (+ 1 (- high2 low2)))
                (<= low1 high1)
                (<= low2 high2)
                (natp size)
                (natp high1)
                (natp low1)
                (natp high2)
                (natp low2))
           (equal (bvcat size1 (bvcat size y size2 (slice high1 low1 x))
                               size3 (slice high2 low2 x))
                  (bvcat size
                               y
                               (+ 1 (- high1 low2))
                               (slice high1 low2 x)))))

(defthmd acl2::bvcat-of-slice-and-getbit-adjacent-2-left-assoc
  (implies (and (equal low1 (+ 1 n))
                (equal size1 (+ size size2))
                (equal size2 (+ 1 (- high1 low1)))
                (<= low1 high1)
                (natp size)
                (natp high1)
                (natp low1)
                (natp n))
           (equal (bvcat size1 (bvcat size y size2 (slice high1 low1 x))
                               1 (getbit n x))
                  (bvcat size
                               y
                               (+ 2 high1 (- low1))
                               (slice high1 n x)))))



;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthm bvcat-of-bitxor-and-bitxor
  (equal (bvcat 1 (bitxor a1 b1) 1 (bitxor a2 b2))
         (bvxor 2 (bvcat 1 a1 1 a2) (bvcat 1 b1 1 b2))))

;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthm bvcat-of-bitxor-and-bvxor
  (implies (natp size)
           (equal (bvcat 1 (bitxor a1 b1) size (bvxor size a2 b2))
                  (bvxor (+ 1 size) (bvcat 1 a1 size a2) (bvcat 1 b1 size b2)))))

;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthm bvcat-of-bvxor-and-bitxor
  (implies (natp size)
           (equal (bvcat size (bvxor size a1 b1) 1 (bitxor a2 b2))
                  (bvxor (+ 1 size) (bvcat size a1 1 a2) (bvcat size b1 1 b2)))))

;; CAUTION: This will be unhelpful if the xors are not commuted right. Consider using a syntaxp hyp?
(defthm bvcat-of-bvxor-and-bvxor
  (implies (and (natp size1)
                (< 0 size1) ;why?
                (natp size2))
           (equal (bvcat size1 (bvxor size1 a1 b1) size2 (bvxor size2 a2 b2))
                  (bvxor (+ size1 size2) (bvcat size1 a1 size2 a2) (bvcat size1 b1 size2 b2)))))

;todo: gen the 32
(defthmd bvcat-becomes-rightrotate
  (implies (and (equal mid+1 (+ 1 mid))
                (equal highsize (+ 1 mid))
                (equal lowsize (- 31 mid))
                (< mid 31)
                (natp mid))
           (equal (bvcat highsize
                         (slice mid 0 x)
                         lowsize
                         (slice 31 mid+1 x))
                  (acl2::rightrotate 32 (+ 1 mid) x)))
  :hints (("Goal" :in-theory (enable ACL2::RIGHTROTATE))))

;usual case (slice down to 0 has become bvchop)
(defthmd bvcat-becomes-rightrotate-2
  (implies (and (equal highsize size)
                (equal lowsize (- 32 size))
                (< size 31)
                (natp size))
           (equal (bvcat highsize
                         (bvchop size x)
                         lowsize
                         (slice 31 size x))
                  (acl2::rightrotate 32 size x)))
  :hints (("Goal" :in-theory (e/d (ACL2::RIGHTROTATE) (ACL2::RIGHTROTATE-BECOMES-LEFTROTATE)))))

(defthmd bvcat-31-of-getbit-31-becomes-rightrotate
  (equal (bvcat 31 x 1 (getbit 31 x))
         (acl2::rightrotate 32 31 x)))

;; (defthmd bvcat-1-of-getbit-0-becomes-rightrotate
;;   (equal (bvcat 1 (getbit 0 x) 31 x)
;;          (acl2::rightrotate 32 1 x)))

(defthm acl2::consp-when-len-equal-alt
  (implies (and (equal acl2::free (len acl2::x))
                (syntaxp (quotep acl2::free)))
           (equal (consp acl2::x)
                  (< 0 acl2::free)))
  :hints (("Goal" :in-theory (e/d (len) ()))))

;; Introduce BVPLUS
(defthm mod-of-+-of-4294967296
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (+ x y) 4294967296)
                  (bvplus 32 x y)))
  :hints (("Goal" :in-theory (enable acl2::bvplus acl2::bvchop))))
