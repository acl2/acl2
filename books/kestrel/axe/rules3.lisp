; Mixed rules 3
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book was called dagrulesmore0.lisp.

(include-book "kestrel/lists-light/finalcdr" :dir :system)
(include-book "kestrel/bv/rules" :dir :system)
(include-book "kestrel/bv/rules6" :dir :system)
(include-book "kestrel/bv/rules4" :dir :system)
(include-book "kestrel/bv/rules3" :dir :system)
(include-book "kestrel/bv/rules5" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p2" :dir :system)
(include-book "kestrel/bv-lists/map-slice" :dir :system)
(include-book "kestrel/bv/rules8" :dir :system)
(include-book "kestrel/bv/sbvmoddown" :dir :system)
(include-book "kestrel/bv/sbvdiv-rules" :dir :system)
(include-book "axe-syntax") ;for work-hard -- TODO make non-work-hard versions of these
(include-book "rules1") ;drop? to prove EQUAL-OF-BV-ARRAY-WRITE-SAME
(include-book "kestrel/bv-lists/bvchop-list" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(include-book "kestrel/bv-lists/bv-arrays" :dir :system) ;needed?
(include-book "kestrel/bv-lists/bvnth" :dir :system) ; for nth2
(include-book "kestrel/utilities/mydefconst" :dir :system)
(include-book "kestrel/utilities/bind-from-rules" :dir :system)
(include-book "kestrel/lists-light/prefixp" :dir :system)
(include-book "kestrel/lists-light/prefixp2" :dir :system)
(include-book "kestrel/lists-light/rules2" :dir :system) ;todo
(include-book "kestrel/arithmetic-light/floor" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "arithmetic/equalities" :dir :system))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system)) ; for INTEGERP-OF-POWER2-HACK-ANOTHER-FACTOR, etc.
(local (include-book "kestrel/bv/floor-mod-expt" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop

(local (in-theory (disable ;natp-rw ;comes in via ihs
                           ;; for speed:
                           unsigned-byte-p-of-+-when-<-of-logtail-and-expt
                           bvchop-identity
                           LOGTAIL-EQUAL-0 ;looped
                           ;; for speed:
                           UNSIGNED-BYTE-P-FROM-BOUNDS
                           BVCHOP-WHEN-TOP-BIT-1-CHEAP
                           BVCHOP-UPPER-BOUND-LINEAR-STRONG ;slow
                           <=-OF-BVCHOP-SAME-LINEAR ;slow
                           )))

;todo: move the rest of the prefixp rules out of this file

;todo: uncomment:(add-known-boolean prefixp) ;todo: make a list-rules-axe book.  prefixp-when-longer-work-hard etc could also go there

(local (in-theory (enable getbit-when-bvlt-of-small-helper))) ;todo

;fixme why?
(local (in-theory (disable <-of-constant-when-unsigned-byte-p-size-param)))

(local (in-theory (disable <-OF-IF-ARG1)))

;drop?:
(mydefconst *minus-1* 4294967295)

;gross
 ;might be expensive
(defthmd cons-becomes-bv-array-write-size-8
  (implies (unsigned-byte-p 8 a)
           (equal (cons a nil)
                  (bv-array-write 8 1 0 a (list 0))))
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write) (;update-nth-becomes-update-nth2-extend-gen
                                                                )))))

;gen and use this more
;yikes! this lets data be a quotep
(defthmd cons-becomes-bv-array-write-size-8-gen
  (implies (and (unsigned-byte-p 8 a)
                (TRUE-LISTP data)
                (all-unsigned-byte-p 8 data))
           (equal (cons a data)
                  (bv-array-write 8 (+ 1 (len data)) 0 a (cons 0 data ))))
  :hints
  (("Goal" :in-theory (e/d (update-nth2 bv-array-write) (;update-nth-becomes-update-nth2-extend-gen
                                                         )))))

(defthm plus-equal-bvplus-rewrite
  (implies (and (natp x)
                (unsigned-byte-p 32 n)
                )
           (equal (equal (+ n x) (bvplus 32 n x))
                  (and (unsigned-byte-p 32 x)
                       (< (bvchop 32 x) (- (expt 2 32) n)))))
  :hints (("Goal" :in-theory (e/d (bvplus unsigned-byte-p bvchop-identity)
                                  (;anti-bvplus
                                   )))))

;mmoved
;gen the minus-1
(defthm bvplus-less-than-constant
  (implies (and (natp x)
                (equal j (+ -1 (expt 2 32)))
                (unsigned-byte-p 32 k))
           (equal (< (BVPLUS 32 j x) k)
                  (and (<= (bvchop 32 x) k)
                       (< 0 (bvchop 32 x)))))
  :hints (("Goal" :in-theory (e/d (bvplus UNSIGNED-BYTE-P BVCHOP-OF-SUM-CASES
                                          )
                                  (;anti-bvplus
                                   )))))

(defthm bvlt-must-be
  (implies (and (bvlt size j x) ;expensive?
                (unsigned-byte-p size k)
                (natp size)
                (equal j (+ -1 k)))
           (equal (bvlt size k x)
                  (not (equal (bvchop size x) k))))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases repeatbit)
                                  (;anti-bvplus ;BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                                   BVLT-OF-BVCHOP-ARG3 ;loops?
                                   BVLT-OF-BVCHOP-ARG2 ;loops?
                                   <-BECOMES-BVLT-FREE
                                   <-becomes-bvlt-alt
                                   <-becomes-bvlt
                                   )))))

;rename or gen the 1
(defthm bvplus-tighten-arg2
  (implies (and (unsigned-byte-p free x)
                (< free (+ -1 size)) ;allowing <= would loop
                (integerp size)
                (natp free))
           (equal (bvplus size 1 x)
                  (bvplus (+ 1 free) 1 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus ;+-BECOMES-BVPLUS-HACK ;looped
                                                        )))))


(defthm move-minus-to-constant
  (implies (syntaxp (quotep k))
           (equal (equal k (- x))
                  (if (acl2-numberp x)
                      (and (equal (- k) x)
                           (acl2-numberp k))
                    (equal k 0))))
  :hints (("Goal" :cases ((acl2-numberp k)))))

(defthm plus-1-bvplus-minus-1
  (equal (+ 1 (bvplus 32 *minus-1* x))
         (if (EQUAL (BVCHOP 32 X) 0)
             4294967296
           (bvchop 32 x))
           )
  :hints (("Goal" :in-theory (e/d (bvplus BVCHOP-OF-SUM-CASES BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;anti-bvplus
                                                                                                )))))

(defthm top-slice-equal-0-becomes-unsigned-byte-p
  (implies (unsigned-byte-p 32 x) ;expensive?
           (equal (equal (slice 31 5 x) 0)
                  (unsigned-byte-p 5 x)))
  :hints (("Goal" :use (:instance BVCAT-SLICE-SAME
                                  (x x)
                                  (k 31) (n 5)
                                  (m 27))
           :in-theory (disable BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE BVCAT-OF-SLICE-AND-X-ADJACENT))))

(defthm bvplus-of-bvplus-trim-5-32
  (equal (bvplus 5 x (bvplus 32 y z))
         (bvplus 5 x (bvplus 5 y z)))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(local (in-theory (disable sbvlt-rewrite))) ;ffixme

(defthm sbvlt-cancel-hack
  (equal (sbvlt 32 15 (bvplus 32 *minus-1* x))
         (if (equal (bvchop 32 x) 2147483648)
             t
           (sbvlt 32 16 x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases bvchop-when-i-is-not-an-integer sbvlt)
                                  (anti-bvplus logext-identity ;integer-tighten-bound
                                               LOGEXT-WHEN-NON-NEGATIVE-BECOMES-BVCHOP)))))

;gen the nth
(defthm sbvlt-bound-hack
  (implies (and (sbvlt 32 free (nth 0 arg0))
                (unsigned-byte-p 31 free)
                (> free k)
                (unsigned-byte-p 31 k)
                )
           (equal (sbvlt 32 k (nth 0 arg0))
                  t))
  :hints (("Goal" :in-theory (e/d (sbvlt) (<-BECOMES-BVLT-FREE)))))

(defthm sbvlt-must-be-value
   (implies (sbvlt 32 x 0)
            (equal (sbvlt 32 x *minus-1*)
                   (not (equal (bvchop 32 x) *minus-1*))))
   :hints (("Goal" :in-theory (enable sbvlt))))

(in-theory (disable |+-BECOMES-BVPLUS-HACK| DIVISIBILITY-IN-TERMS-OF-FLOOR))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))

;gen
(defthm bvmult-of-4
  (equal (BVMULT '32 '4 x)
         (bvcat 30 x 2 0))
  :hints (("Goal" :in-theory
           (e/d (bvmult bvcat logapp BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         bvchop-of-*)))))

(in-theory (disable BV-ARRAY-READ-OF-BV-ARRAY-WRITE-BOTH))

;(in-theory (disable GET-SIZE-OF-EXPR))

(defthm sbvdiv-hack
  (implies (natp x)
           (equal (SBVDIV 32 (BVCAT 2 x 2 2) 4)
                  (bvchop 2 x)))
  :hints (("Goal" :in-theory (e/d (sbvdiv bvcat logapp bvchop-of-logtail-becomes-slice)
                                  (usb-plus-from-bounds
                                   bvplus-of-*-arg2
                                   times-2-of-bvplus-becomes-bvmult-of-bvplus
                                   getbit-when-bvlt-of-small-helper)))))

(defthm bvcat-tighten-from-bound-4-20-2
  (implies (and (< x 4)
                (natp x)
                (natp n)
                )
           (equal (bvcat 30 x n y)
                  (bvcat 2 x n y)))
  :hints (("Goal" :in-theory (e/d (SLICE-TOO-HIGH-IS-0) ()))))

(local (in-theory (disable COLLECT-CONSTANTS-<-/))) ;investigate this

(include-book "kestrel/arithmetic-light/floor2" :dir :system) ;move up or drop?

(in-theory (disable MOD-IS-0-WHEN-MULTIPLE ;todo: these are basically the same
                    ;mod-when-multiple
                    ))

(defthmd floor-of-sum-no-split
  (implies (and (rationalp j)
                (< 0 j)
                (rationalp i1)
                (rationalp i2))
           (equal (floor (+ i1 i2) j)
                  (myif (< (+ (mod i1 j) (mod i2 j)) j)
                        (+ (floor i1 j) (floor i2 j))
                        (+ 1 (floor i1 j) (floor i2 j)))))
  :hints (("Goal" :in-theory (e/d (floor-of-sum) (divisibility-in-terms-of-floor)))))

(defthm floor-of-myif-arg1
  (equal (floor (myif test i1 i2) j)
         (myif test (floor i1 j) (floor i2 j)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm floor-of-mod-64-expt
  (implies (and (integerp x)
                (natp n)
                (< n 6))
           (equal (floor (mod x 64) (expt 2 n))
                  (mod (floor x (expt 2 n))
                       (* 64 (/ (expt 2 n))))))
  :hints (("Goal" :in-theory (e/d (mod)( multiple-idioms-for-multiple
                                         mod-of-floor-is-0-when-multiple
                                         mod-x-i*j-of-positives
                                         ;mod-recollapse-lemma
                                         ;mod-recollapse-lemma2
                                         mod-of-expt-of-2-constant-version
                                         )))))

(in-theory (disable MOD-OF-FLOOR-EQUAL-REWRITE))

(in-theory (disable ;BV-ARRAY-WRITE-DOES-NOTHING ;TRIM-TO-N-BITS-META-RULE
                    BV-ARRAY-READ-SHORTEN-DATA))

(defthm eric-hack-1000
   (equal (bvplus 32 4294967295 (bvcat 2 specparam0 2 3))
          (bvcat 2 specparam0 2 2))
   :hints (("Goal" :in-theory (e/d (bvplus bvcat logapp) (anti-bvplus)))))

(defthm eric-hack-1001
   (equal (bvplus 32 4294967294 (bvcat 2 specparam0 2 2))
          (bvcat 2 specparam0 2 0))
   :hints (("Goal" :in-theory (e/d (bvplus bvcat logapp) (anti-bvplus)))))

(defthm eric-hack-1002
   (equal (bvplus 32 4294967295 (bvcat 2 specparam0 2 2))
          (bvcat 2 specparam0 2 1))
   :hints (("Goal" :in-theory (e/d (bvplus bvcat logapp) (anti-bvplus)))))

(defthm eric-hack-1003
   (equal (bvplus 32 4294967295 (bvcat 2 specparam0 2 1))
          (bvcat 2 specparam0 2 0))
   :hints (("Goal" :in-theory (e/d (bvplus bvcat logapp) (anti-bvplus)))))

;gen
;turn sbvdiv into an unsgined version when nothing is negative
;also tighten
;; (defthm eric-hack-2000
;;   (equal (sbvdiv 32 (bvcat 2 x 2 y) 4)
;;          (bvchop 2 x))
;;   :hints (("Goal" :in-theory (enable sbvdiv floor-by-4))))

;; ;i need a slice shift rule

;; (defthm eric-hack-2001
;;  (implies (and (natp x)
;;                (< x 4))
;;           (equal (* 4 x)
;;                  (bvcat 2 x 2 0)))
;;  :hints (("Goal" :in-theory (e/d (slice logtail) (anti-slice)))))

;; (defthm eric-hack-2002
;;   (equal (* 1/4 (BVCAT 2 x 2 0))
;;          (bvchop 2 x))
;;   :hints (("Goal" :in-theory (e/d (UNSIGNED-BYTE-P slice logtail) (anti-slice)))))

;; (defthm eric-hack-2001
;;   (equal (SBVDIV 32 (+ 3 (* 4 x)) 4)
;;          x)
;;   :hints (("Goal" :in-theory (enable sbvdiv floor-by-4))))

(in-theory (disable divisibility-in-terms-of-floor))

;move
(defthm bvchop-of-nth2-becomes-bv-array-read
  (implies (and (unsigned-byte-p n x)
                (natp n)
                (natp size))
           (equal (bvchop size (nth2 n x data))
                  (bv-array-read size (expt 2 n) x data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read bvchop-when-i-is-not-an-integer nth2 ceiling-of-lg)
                                  (nth-of-bv-array-write-becomes-bv-array-read)))))

(defthm sbvlt-transitive-free
  (implies (and (sbvlt size x free)
;                (syntaxp (and (quotep free) (quotep size)))
                (sbvlt size free y))
           (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm sbvlt-of-one-more-hack
  (implies (integerp x)
           (equal (sbvlt 32 4 (+ 1 x))
                  (if (equal (bvchop 32 x) 2147483647)
                      nil
                    (sbvlt 32 3 x))))
  :hints (("Goal" :in-theory (e/d (sbvlt ;logext getbit slice
                                   ) (anti-slice LOGEXT-WHEN-NON-NEGATIVE-BECOMES-BVCHOP)))))

;rename
;just turn the + into bvplus
;; (defthm bvplus-of-minus-of-bvchop
;;  (IMPLIES (AND (INTEGERP X)
;;                (INTEGERP Y)
;;                (INTEGERP Z))
;;           (EQUAL (BVPLUS 32 x (+ Z (- (BVCHOP 32 y))))
;;                  (BVPLUS 32 x (+ Z (- Y))))))

;just turn the + into bvplus
;; (defthm bvminus-of-plus-of-bvchop
;;  (implies (and (integerp x)
;;                (natp size)
;;                (integerp z)
;;                (integerp y))
;;           (equal (bvminus size z (+ y (bvchop size x)))
;;                  (bvminus size z (+ y x))))
;;  :hints (("Goal" :in-theory (e/d (bvminus) (bvminus-becomes-bvplus-of-bvuminus bvplus-of-plus bvplus-cancel-cross2 bvplus-cancel-cross)))))

;just turn the + into bvplus
;; (defthm bvuminus-of-plus-of-bvchop
;;   (IMPLIES (AND (INTEGERP X)
;;                 (INTEGERP Y))
;;            (EQUAL (BVUMINUS 32 (+ y (BVCHOP 32 X)))
;;                   (BVUMINUS 32 (+ Y X))))
;;   :hints (("Goal" :in-theory (e/d (bvuminus) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;; (defthm bvuminus-of-plus-trim-leading-constant
;;   (implies (and (syntaxp (and (quotep k) (quotep size)))
;;                 (integerp y)
;;                 (integerp k)
;;                 (posp size)
;;                 (not (unsigned-byte-p size k)))
;;            (equal (bvuminus size (+ k y))
;;                   (bvuminus size (+ (bvchop size k) y))))
;;   :hints (("Goal" :in-theory (e/d (bvuminus) (bvminus-becomes-bvplus-of-bvuminus))
;;            :cases ((natp size)))))

;; ;kill
;; (defthm bvuminus-of-plus
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (bvuminus 32 (+ y x))
;;                   (bvuminus 32 (bvplus 32 y x))))
;;   :hints (("Goal" :in-theory (e/d (bvplus bvuminus ;bvminus
;;                                    ;bvchop-of-sum-cases
;;                                    ) ( bvminus-becomes-bvplus-of-bvuminus anti-bvplus )))))

(in-theory (disable +-becomes-bvplus-hack))

(defthm sbvlt-cancel-hack2
  (implies (integerp x)
           (equal (sbvlt 32 4 (bvplus 32 4 x))
                  (if (sbvle 32 (- (expt 2 31) 4)
                             (bvchop 31 x))
                      nil
                    (sbvlt 32 0 x))))
  :hints (("Goal" :in-theory (e/d (sbvlt logext LOGAPP-0 bvplus BVCHOP-OF-SUM-CASES bvlt getbit-of-plus)
                                  (<-BECOMES-BVLT-FREE
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   anti-bvplus TIMES-4-BECOMES-LOGAPP)))))

;move
(defthm <-of-+-cancel
  (equal (< (+ x y) x)
         (< y 0)))

(defthm integerp-of-*-of-expt-and-expt
  (implies (and (integerp i)
                (integerp j))
           (equal (integerp (* (expt 2 i) (expt 2 j)))
                  (natp (+ i j))))
  :hints (("Goal" :in-theory (disable ;integerp-of-expt
                              ;;<-OF-0-AND-EXPT
                              integerp-of-expt-when-natp)
           :use (:instance integerp-of-expt-when-natp (r 2) (i (+ i j))))))

(defthm *-of-expt-and-expt-of-1minus
  (implies (integerp size)
           (equal (* (expt 2 size) (expt 2 (+ 1 (- size))))
                  2))
  :hints (("Goal" :use (:instance exponents-add (r 2) (i size) (j (- 1 size))))))

(defthm logtail-hack77
  (implies (posp size)
           (equal (logtail (+ -1 size) (- (expt 2 size)))
                  -2))
  :hints (("Goal" :in-theory (enable logtail))))

(in-theory (disable PLUS-BVCAT-WITH-0-ALT))

(defthm <-of-plus-swap-minuses
  (equal (< (+ (- x) y) (- z))
         (< (+ z y) x)))

(defthm cancel-expts-from-<
 (implies (integerp size)
          (equal (< (+ (EXPT 2 (+ -1 SIZE)) x) (EXPT 2 SIZE))
                 (< x (EXPT 2 (+ -1 SIZE)))))
 :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <-of-logext-true
  (implies (<= (expt 2 (+ -1 size)) k)
           (< (LOGEXT size X) k))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthm <-of-logext-false
  (implies (and (<= k (- (expt 2 (+ -1 size))))
                (posp size)
                )
           (not (< (LOGEXT size X) k)))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthm floor-minus-arg1-better
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal 0 y)))
           (equal (floor (- x) y)
                  (if (equal (floor x y) (/ x y))
                      (- (floor x y))
                      (- (- (floor x y)) 1)))))

(in-theory (disable floor-minus-arg1))

;move up
(defthmd truncate-becomes-floor-gen4-better-better
  (implies (and (rationalp i) (rationalp j))
           (equal (truncate i j)
                  (if (equal 0 j)
                      0
                    (if (equal 0 (mod i j))
                        (floor i j)
                      (if (or (and (<= 0 i) (<= 0 j))
                              (and (< i 0) (< j 0)))
                          (floor i j)
                        (+ 1 (floor i j)))))))
  :hints (("Goal" ;:cases ((equal 0 j))
           :in-theory (enable mod-=-0 truncate-becomes-floor-gen))))

(defthmd tighten-multiple-of-4
  (implies (and (syntaxp (quotep high))
                (integerp (* 1/4 high))
                (integerp (* 1/4 x))
                (integerp x)
                (integerp high))
           (equal (< x high)
                  (<= x (+ -4 high))))
  :hints (("Goal" :in-theory (enable))))

;the rule logext-bounds is bad
(defthm logext-bounds-better
  (implies (< 0 size)
           (and (>= (logext size i) (- (expt 2 (+ -1 size))))
                (< (logext size i) (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable logext logapp)))
  :rule-classes ((:linear :trigger-terms ((logext size i)))
                 (:rewrite)))

;(in-theory (disable LOGEXT-BOUNDS)) ; now in a locally included book

(defthm logext-min-value
  (equal (< -2147483648 (LOGEXT 32 X))
         (not (equal -2147483648 (LOGEXT 32 X)))))

(defthm bvplus-equal-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp k1)
                (integerp k2)
                (integerp x))
           (equal (equal (bvplus 32 k2 x) k1)
                  (and (unsigned-byte-p 32 k1)
                       (equal (bvchop 32 x) (bvchop 32 (- k1 k2))))))
  :hints (("Goal" :in-theory (e/d (bvplus BVCHOP-OF-SUM-CASES UNSIGNED-BYTE-P) (anti-bvplus)))))

(defthm <-of-0-and-logext-2
  (equal (< 0 (logext 32 x))
         (and (equal (getbit 31 x) 0)
              (not (equal 0 (bvchop 32 x)))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm integerp-of-*-of-1/4-of-bvchop
  (implies (integerp x)
           (equal (integerp (* 1/4 (bvchop 31 x)))
                  (integerp (* 1/4 x))))
  :hints (("Goal" :in-theory (e/d (bvchop)
                                  (mod-by-4-becomes-bvchop)))))

(defthm integerp-of-*-of-1/4-of-logext
  (implies (integerp x)
           (equal (integerp (* 1/4 (logext 32 x)))
                  (integerp (* 1/4 x))))
  :hints (("Goal" :in-theory (enable logext logapp
                                     integerp-of-*-of-1/4-of-bvchop))))

(defthm <-of-logext-and-0-linear
  (implies (and (equal 1 (getbit 31 x))
                (integerp x))
           (< (logext 32 x) 0))
  :rule-classes ((:linear :backchain-limit-lst (0 nil))))

(defthm logext-when-equal-of-getbit
  (implies (and (equal 0 (getbit 31 x))
                (integerp x))
           (equal (logext 32 x)
                  (bvchop 31 x))))

(defthmd bound-when-mult-of-4
  (implies (and (natp x)
                (integerp (* 1/4 x))
                (not (equal 0 x)))
           (<= 4 x)))

(defthm sbvdiv-of-subtract-4-by-minus-4
  (implies (natp x)
           (equal (sbvdiv 32 (+ -4 x) -4)
                  (if (< (logext 32 x) -2147483644)
                      3758096385
                    (if (and (< 0 (logext 32 x))
                             (< (logext 32 x) 4))
                        0 ;the normal pattern would give 1
                      (bvplus 32 1 (sbvdiv 32 x -4))))))
  :hints (("Goal"
           :use ((:instance LOGEXT-BOUNDS-better (size 32) (i x))
                 (:instance bound-when-mult-of-4 (x (bvchop 31 x)))
                 (:instance FLOOR-UNIQUE (i (LOGEXT 32 X))
                            (j 4)
                            (n -536870912)))
           :in-theory (e/d (sbvdiv bvplus bvchop-plus-minus-1-split-gen
                                   bvchop-identity
                                   <-of-logext-and-0
                                   truncate-becomes-floor-other
                                   truncate-becomes-floor
                                   mod-by-4-becomes-bvchop)
                           (
                            LOGEXT-MIN-VALUE
                            anti-bvplus
                            FLOOR-UNIQUE-EQUAL-VERSION
                            ;; bvchop-of-minus ;can this loop?
                            logext-identity
                            ;
                            ;; if-backchain-rule
                            logext-bounds
                            ;bvchop-leq
                            <-of-logext-false
                            <-of-logext-true
                            logext-when-top-bit-0 sbp-32-when-non-neg
                            LOGEXT-WHEN-NON-NEGATIVE-BECOMES-BVCHOP
                            TRUNCATE-=-X/Y
                            truncate-minus
                            )))))

;(in-theory (disable logext-identity)) ; now in a locally included book

(local (in-theory (disable FLOOR-=-X/Y))) ;corollary is bad

;;MOD-TYPE ;does this overlap with mod-bounded-by-modulus?

;; (defthm <-of-expt-and-bvchop-better
;;   (equal (< (expt 2 size) (bvchop size x))
;;          nil))



;could be bad?
(defthm integerp-of-plus-of-minus
  (implies (and (integerp (+ (- x) y))
                (rationalp x)
                (rationalp y))
           (integerp (+ x (- y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :use (:instance INTEGERP-OF-- (x (+ x (- y))))
           :in-theory (disable INTEGERP-OF--))))

;could be bad?
(defthm integerp-of-plus-of-minus-alt
  (implies (and (integerp (+ y (- x)))
                (rationalp x)
                (rationalp y))
           (integerp (+ (- y) x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :use (:instance INTEGERP-OF-- (x (+ x (- y))))
           :in-theory (disable INTEGERP-OF--))))

(defthmd sbvdiv-when-x-negative
  (implies (and (integerp x)
                (integerp y)
                (sbvlt size x 0)
                (sbvle size 0 y)
                (posp size))
           (equal (sbvdiv size x y)
                  (bvuminus size (bvdiv size (bvuminus size x) y))))
  :hints (("Goal" :expand ((BVCAT 1 1 (+ -1 size) X)
                           (BVCAT 1 1 (+ -1 size) y)
                           (:with logext (LOGEXT size X))
                           (:with logext (LOGEXT size y)))
           :in-theory (e/d (sbvdiv bvdiv logapp bvuminus bvminus sbvlt BVCHOP-OF-SUM-CASES
                                   FLOOR-MINUS-ARG1
                                   bvchop-reduce-when-top-bit-known
                                   truncate-becomes-floor-other)
                           (;BVCHOP-LEQ ;these are for speed
                            |0-1-SPLIT-CHEAP|
                            FLOOR-BOUNDED-BY-/
                            BVCHOP-UPPER-BOUND

                            FLOOR-TYPE-3
                             floor-of-minus-and-minus
                             floor-minus
    ;FLOOR-MINUS-ARG1
                             PLUS-BVCAT-WITH-0
                             bvplus-recollapse
                             BVCAT-OF-+-LOW
                             BVCAT-OF-GETBIT-AND-X-ADJACENT
                             <-Y-*-Y-X
                             my-FLOOR-upper-BOUND
                             BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                             floor-bound)))))



(defthmd sbvdiv-when-y-negative
  (implies (and (integerp x)
                (integerp y)
                (sbvlt size y 0)
                (sbvle size 0 x)
                (posp size)
                )
           (equal (sbvdiv size x y)
                  (bvuminus size (bvdiv size x (bvuminus size y)))))
  :hints (("Goal" :expand ((BVCAT 1 1 (+ -1 size) X)
                           (BVCAT 1 1 (+ -1 size) y)
                           (:with logext (LOGEXT size X))
                           (:with logext (LOGEXT size y)))
           :in-theory (e/d (sbvdiv bvdiv logapp bvuminus bvminus sbvlt BVCHOP-OF-SUM-CASES
                                   bvchop-reduce-when-top-bit-known
                                   truncate-becomes-floor-other)
                           ( floor-of-minus-and-minus
                             floor-minus
                             FLOOR-MINUS-ARG1
                             PLUS-BVCAT-WITH-0
                             bvplus-recollapse
                             BVCAT-OF-+-LOW
                             BVCAT-OF-GETBIT-AND-X-ADJACENT
                             <-Y-*-Y-X
                             my-FLOOR-upper-BOUND
                             BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                             floor-bound)))))

(in-theory (disable bvdiv))

;gen
;move
(defthm sbvlt-of-0-when-not-sbvlt-of-minus1-cheap
 (implies (not (sbvlt size -1 x))
          (sbvlt size x 0))
 :rule-classes ((:rewrite :backchain-limit-lst (0)))
 :hints (("Goal" :in-theory (enable SBVLT))))

;can we tighten any of the sizes?
(defthm sbvdiv-rewrite
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (sbvdiv size x y)
                  (if (sbvle size 0 x)
                      (if (sbvle size 0 y)
                          (bvdiv (+ -1 size) x y)
                        (bvuminus size (bvdiv size x (bvuminus size y))))
                    (if (sbvle size 0 y)
                        (bvuminus size (bvdiv size (bvuminus size x) y))
                      (bvdiv size (bvuminus size x)
                             (bvuminus size y))))))
  :hints (("Goal" :in-theory (enable sbvdiv-when-y-negative
                                     sbvdiv-when-x-negative
                                     sbvdiv-when-both-negative
                                     sbvdiv-when-both-positive))))

;; (thm
;;  (implies (and (NOT (INTEGERP (* (/ J) Y)))
;;                (posp j)
;;                (posp y)
;;                (rationalp x)
;;                (rationalp y))
;;           (< (FLOOR (MOD X j) (MOD Y j)) j))
;;  :otf-flg t
;;  :hints (("Goal" :use ((:instance FLOOR-BOUNDED-BY-/ (x (MOD X j)) (y (mod y j)))
;;                        (:instance bound-hack-quotient (x (MOD X J)) (k (MOD Y J)))
;;                        )
;;           :cases ((INTEGERP (BINARY-* (UNARY-/ J) Y)))
;;           :in-theory (disable bound-hack-quotient FLOOR-BOUND-LEMMA3 FLOOR-BOUND-LEMMA2
;;                               ))))

(defthm plus-and-bvplus-hack
  (equal (equal (+ -1 x) (bvplus 32 1 y))
         (and (integerp x)
              (< 0 x)
              (<= x (expt 2 32))
              (if (EQUAL (BVCHOP 32 Y) *MINUS-1*)
                  (equal x 1)
                (if (EQUAL (BVCHOP 32 Y) (+ -2 (expt 2 32)))
                    (equal x 4294967296)
                  (equal x (bvplus 32 2 y))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (anti-bvplus)))))



;gen
(defthm sbvlt-of-minus
  (implies (integerp x)
           (equal (sbvlt 32 (+ -4 x) 0)
                  (if (sbvle 32 (+ 4 (- (expt 2 31))) x)
                      (sbvlt 32 x 4)
                    nil)))
  :hints (("Goal" :in-theory (enable sbvlt))))

;gen!
(defthm integerp-of-*-of-1/4-of-expt
  (implies (natp size)
           (equal (integerp (binary-* '1/4 (expt '2 size)))
                  (<= 2 size)))
  :hints (("Goal" :use (:instance integerp-of-expt-when-natp (r 2) (i (- size 2)))
           :in-theory (disable integerp-of-expt-when-natp))))

(defthmd integerp-of-*-of-1/4
  (implies (integerp x)
           (equal (integerp (* 1/4 x))
                  (equal 0 (bvchop 2 x))))
  :hints (("Goal" :in-theory (e/d (bvchop
                                   ) (mod-by-4-becomes-bvchop ;fixme
                                      MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                      MOD-OF-EXPT-OF-2
                                      )))))

(defthm unsigned-byte-p-of-times-1/4
 (implies (and (posp x)
               (natp size))
          (equal (unsigned-byte-p size (binary-* '1/4 x))
                 (and (equal 0 (bvchop 2 x))
                      (unsigned-byte-p (+ 2 size) x))))
 :hints (("Goal" :in-theory (enable unsigned-byte-p integerp-of-*-of-1/4))))

;this is probably done better elsewhere
;as a forward-chaining rule, this caused a big slowdown
(defthm expt-bound-fw
  (implies (and (<= k j)
                (syntaxp (and (quotep k)
                              (not (quotep j))))
                (< k 100) ;prevent huge computations
                (integerp k)
                (integerp j))
           (<= (expt 2 k) (expt 2 j)))
  :rule-classes ((:linear :trigger-terms ((EXPT 2 J)))))

;gen the 4!
(defthm bvdiv-of-subtract-4-by-4
  (implies (and (natp x)
                (integerp size)
                (< 2 size))
           (equal (bvdiv size (+ -4 x) 4)
                  (if (bvle size 4 x)
                      (bvplus size -1 (bvdiv size x 4))
                    (+ -1 (expt 2 (+ -2 size))))))
  :hints (("Goal" :in-theory (e/d (bvdiv bvplus bvchop-of-sum-cases bvlt bvchop-identity)
                                  (LOGEXT-MIN-VALUE
                                   FLOOR-UNIQUE-EQUAL-VERSION
                                   anti-bvplus
                                   ;;bvchop-of-minus ;can this loop?
                                   logext-identity
                                   ;bvchop-identity
                                   <-BECOMES-BVLT-ALT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-free
;                                   if-backchain-rule
                                   logext-bounds
                                   ;bvchop-leq
                                   <-of-logext-false
                                   <-of-logext-true
                                   logext-when-top-bit-0 sbp-32-when-non-neg)))))

(local (in-theory (disable MOD-OF-EXPT-OF-2-CONSTANT-VERSION MOD-OF-EXPT-OF-2)))

;move
(defthm expt-split-hack
  (implies (posp size)
           (equal (+ (- (EXPT 2 SIZE)) (EXPT 2 (+ -1 SIZE)))
                  (- (EXPT 2 (+ -1 SIZE)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm sbvlt-0-bvuminus
  (equal (sbvlt 32 0 (bvuminus 32 x))
         (if (equal (bvchop 32 x) 2147483648)
             nil
           (sbvlt 32 x 0)))
  :hints (("Goal" :in-theory (e/d (bvuminus sbvlt bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

;;      (NOT (SBVLT 32 GARG0 2147483652))

;;      (NOT (SBVLT 32
;;                  (BVPLUS 32 4 (BVUMINUS 32 (BVDIV 32 GARG0 4)))
;;                  0))
;;      (NOT (SBVLT 32 (BVUMINUS 31 (BVDIV 32 GARG0 4))
;;                  2147483644))

;;      (NOT (SBVLT 32 GARG0 0))
;;      (NOT (SBVLT 32 16 GARG0))

(defthm sbvlt-false-from-bound
  (implies (and (syntaxp (quotep k))
                (sbvlt 32 x free)
                (syntaxp (quotep free))
                (< (logext 32 free) (logext 32 k)) ;this will get computed
                )
           (equal (sbvlt 32 k x)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt))))

;fixme weaken hyps to sbvle?  hmm. then it might loop?!
;expensive..
(defthm sbvlt-becomes-bvlt
  (implies (and (sbvlt 32 0 x)
                (sbvlt 32 0 y))
           (equal (sbvlt 32 x y)
                  (bvlt 31 x y)))
  :hints (("Goal" :in-theory (e/d (bvlt sbvlt LOGEXT-BECOMES-BVCHOP-WHEN-POSITIVE)
                                  (<-BECOMES-BVLT-ALT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-free
                                   )
                                  ))))

(defthm sbvlt-when-bvlt-constants
  (implies (and (syntaxp (quotep k))
                (not (bvlt 31 free i))
                (syntaxp (quotep free))
                (<= free k)
                (unsigned-byte-p 31 k) ;gen??
                (natp free)
                (integerp i))
           (equal (sbvlt 32 k i)
                  nil))
  :hints (("Goal" :in-theory (e/d (logapp sbvlt bvlt logext logapp-0 <=-OF-BVCHOP-SAME-LINEAR)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                                      TIMES-4-BECOMES-LOGAPP)))))

;restrict?
(defthm sbvlt-transitive-free-back
  (implies (and (not (sbvlt size x free))
                (not (sbvlt size free y)))
           (equal (sbvlt size x y)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt))))

(in-theory (disable PLUS-BVCAT-WITH-0)) ;move up

;; (thm
;;  (implies (and (integerp x)
;;                (integerp k1)
;;                (integerp k2))
;;           (equal (sbvlt 32 (bvplus 32 k1 x) k2)
;;                  (sbvlt 32 x (bvminus 32 k2 k1))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (e/d (sbvlt bvplus bvuminus bvminus bvcat logapp) (anti-bvplus BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm bvlt-of-bvplus-add-to-both-sides
  (implies (integerp x)
           (equal (bvlt 31 15 (bvplus 31 2147483647 x))
                  (if (equal (bvchop 31 x) 0)
                      t
                    (bvlt 31 16 x)
                    )))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases)
                                  (anti-bvplus <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm plus-1-and-bvchop-becomes-bvplus
  (implies (integerp x)
           (equal (+ 1 (BVCHOP 31 x))
                  (if (equal (+ -1 (expt 2 31)) (bvchop 31 x))
                      (expt 2 31)
                    (bvplus 31 1 x))))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(defthm <-of-bvplus-hack
  (implies (integerp x)
           (equal (< (bvplus 32 1 x) 2147483648)
                  (if (EQUAL (BVCHOP 32 X) *MINUS-1*)
                      t
                    (bvlt 32 x 2147483647))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases bvlt) (anti-bvplus
                                                                      <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;; (thm
;;  (implies (integerp x)
;;           (equal (equal (bvplus 31 1 x) (bvplus 32 1 x))
;;                  (if (< (expt 2 31) (bvchop 32 x))
;;                      (if (equal (bvchop 32 x) (+ -1 (expt 2 32)))
;;                          t
;;                        nil)
;;                    (if (equal (expt 2 31) (bvchop 32 x))
;;                        nil
;;                      (if (equal (+ -1 (expt 2 31)) (bvchop 32 x))
;;                          nil
;;                        t
;;                        )))))
;;  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN bvcat logapp)
;;                                  ( ;BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
;;                                   anti-bvplus plus-1-and-bvchop-becomes-bvplus)))))

;gen
(defthm bvplus-equal-same
  (implies (integerp x)
           (equal (equal 2147483647 (bvplus 31 2147483647 x))
                  (equal 0 (bvchop 31 x))))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(defthm <-of-bvplus-hack2
  (implies (integerp x)
           (equal (< (BVPLUS 32 2147483647 x) 2147483648)
                  (or (equal 0 (bvchop 32 x))
                      (< 2147483648 (bvchop 32 x)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases) (anti-bvplus)))))



(defthm bvlt-of-minus-add
  (implies (integerp x)
           (equal (bvlt 31 16 (+ -4 x))
                  (if (< (bvchop 31 x) 4)
                      t
                    (bvlt 31 20 x))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvplus
  (implies (integerp x)
           (equal (BVLT 31 4 (BVPLUS 31 4 x))
                  (if (<= (- (expt 2 31) 4) (bvchop 31 x))
                      nil
                    (BVLT 31 0 x))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus) (anti-bvplus <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))



(defthm <-of-bvplus-constant-and-constant-other-case
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (< k2 k1) ;gen?
                (unsigned-byte-p 32 k1)
                (unsigned-byte-p 32 k2)
                (integerp x))
           (equal (< (bvplus 32 k1 x) k2)
                  (and (bvle 32 (- k1) x)
                       (bvlt 32 x (- k2 k1)))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus)
                                  (anti-bvplus
                                   <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm <-of-bvplus-constant-and-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (<= k1 k2) ;gen?
                (unsigned-byte-p 32 k1)
                (unsigned-byte-p 32 k2)
                (integerp x))
           (equal (< (bvplus 32 k1 x) k2)
                  (or (<= (+ (- k1) (expt 2 32)) (bvchop 32 x))
                      (bvlt 32 x (- k2 k1)))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus) (anti-bvplus <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvuminus-less-than-true
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 size) k)
                (natp size))
           (< (bvuminus size x) k))
  :hints (("Goal" :in-theory (e/d (bvuminus) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm bvlt-of-bvuminus-trim
  (implies (unsigned-byte-p 31 z)
           (equal (BVLT 32 (BVUMINUS 31 x) z)
                  (BVLT 31 (BVUMINUS 31 x) z)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-tighten-arg2
  (equal (BVLT 31 z (BVUMINUS 32 x))
         (BVLT 31 z (BVUMINUS 31 x)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-tighten-arg1
  (equal (BVLT 31 (BVUMINUS 32 x) z)
         (BVLT 31 (BVUMINUS 31 x) z))
  :hints (("Goal" :in-theory (e/d (bvlt) ( <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;can we split into fewer cases? maybe not?
(defthm bvlt-of-bvuminus-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (natp size))
           (equal (bvlt size (bvuminus size x) k)
                  (and (not (equal 0 (bvchop size k)))
                       (if (equal 0 (bvchop size x))
                           t
                         (bvlt size
                               (bvuminus size k)
                               x)))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus
                                        BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus
                                                <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                               ;;BVLT-OF-PLUS-ARG1
                                               ;;BVLT-OF-PLUS-ARG2
                                                )))))

(defthm bvlt-of-bvchop-tighten
  (implies (and (unsigned-byte-p 31 y)
                (< 31 size) ;<= would loop
                (integerp size))
           (equal (BVLT size (BVCHOP 31 x) y)
                  (BVLT 31 (BVCHOP 31 x) y)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;better way to handle this?  should a < in some rule somewhere be a bvlt?
(defthm <-of-bvuminus-becomes-bvlt
  (implies (and (unsigned-byte-p size y)
                (natp size) ;drop
                )
           (equal (< (bvuminus size x) y)
                  (bvlt size (bvuminus size x) y)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-and-constant-alt
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (integerp k)
                (natp size)
                (integerp x))
           (equal (bvlt size k (bvuminus size x))
                  (and (not (equal 0 (bvchop size x)))
                       (if (equal 0 (bvchop size k))
                           t
                         (bvlt size x (bvuminus size k))))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus)
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus
                                               <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
;bvlt-of-plus-arg2
;bvlt-of-plus-arg1
                                               )))))
;move and gen
(defthm floor-of-4-becomes-logtail
  (implies (integerp x)
           (equal (floor x 4)
                  (logtail 2 x)))
  :hints (("Goal" :in-theory (enable logtail))))

;;strength reduction
(defthm bvdiv-of-4
  (equal (bvdiv 32 x 4)
         (slice 31 2 x))
  :hints (("Goal" :in-theory (e/d (bvdiv slice bvchop-of-logtail
                                         ) (anti-slice bvplus-recollapse rewrite-floor-mod)))))

;rename?
;bad rule?
(defthm bvlt-by-4
  (equal (bvlt 31 x 4)
         (unsigned-byte-p 2 (bvchop 31 x)))
  :hints (("Goal" :in-theory (e/d (bvlt) (REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER
                                           <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;gen
(defthm bvplus-of-bvplus-trim
  (equal (bvplus 31 z (bvplus 32 x y))
         (bvplus 31 z (bvplus 31 x y)))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

;move
;should commut bvplus args ignoring bvuminus calls
(defthm bvplus-of-bvuminus-cancel
  (implies (natp size)
           (equal (bvplus size k1 (bvplus size a (bvuminus size k1)))
                  (bvchop size a))))

;can split into cases
;removed bool op from conclusion Tue Feb 23 12:46:43 2010
(defthm bvlt-of-bvuminus-arg2-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep size)))
                (natp size))
           (equal (bvlt size k1 (bvuminus size y))
                  (and (not (equal 0 (bvchop size y)))
                       (if (equal 0 (bvchop size k1))
                           t
                         (bvlt size y (bvuminus size k1))))))
  :hints (("Goal" :in-theory (e/d (boolor ;;bvuminus bvminus
                                   bvlt) (bvminus-BECOMES-BVPLUS-OF-BVUMINUS))
           :use (:instance bvlt-of-bvuminus-arg2))))



(defthmd bvlt-add-to-both-sides-constant-lemma-alt-helper
  (implies (and (syntaxp (and (quotep y)
                              (quotep k1)
                              (quotep size)))
                (integerp y) ;drop!
                (integerp k1)
                (natp size)
                )
           (equal (bvlt size (bvplus size k1 x) y)
                  (if (bvlt size (bvplus size k1 x) k1) ;(and (bvle size (bvuminus size x) k1) (not (equal 0 (bvchop size k1))))
                      (if (bvlt size y k1)
                          (bvlt size x (bvplus size y (bvuminus size k1)))
                        t)
                    (if (bvlt size y k1)
                        nil
                      (bvlt size x (bvplus size y (bvuminus size k1)))))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides (x (bvplus size k1 x)) (z (bvuminus size k1)))
           :in-theory (e/d (bvlt-of-0-arg2)
                           ( bvlt-add-to-both-sides
                               BVLT-OF-PLUS-ARG2
                               BVLT-OF-PLUS-ARG1)))))

;; (defthm bvplus-when-bvchop-known-subst-alt
;;   (implies (and (equal (bvchop size x) free)
;;                 (syntaxp (quotep free))
;;                 (natp size))
;;            (equal (bvplus size x y)
;;                   (bvplus size free y)))
;;   :hints (("Goal" :in-theory (enable))))

;; (defthm bvplus-when-bvchop-known-subst
;;   (implies (and (equal (bvchop size x) free)
;;                 (syntaxp (quotep free))
;;                 (natp size))
;;            (equal (bvplus size y x)
;;                   (bvplus size y free)))
;;   :hints (("Goal" :in-theory (enable))))

;this is the same as bvlt-of-bvplus-same?
(defthm bvlt-of-bvplus-same2
  (implies (natp size)
           (equal (bvlt size (bvplus size x y) x)
                  (if (equal 0 (bvchop size x))
                      nil
                    (not (bvlt size y (bvuminus size x))))))
  :hints (("Goal" :in-theory (enable BVLT-OF-0-ARG2)
           :use (:instance bvlt-of-bvuminus-arg2 (k1 x)))))

;fixme  - simplify this?
(defthm bvlt-add-to-both-sides-constant-lemma-alt
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)
                              (quotep size)))
                (natp size))
           (equal (bvlt size (bvplus size k1 x) k2)
                  (if (if (equal 0 (bvchop size k1)) ;should just get computed
                          t
                        (bvlt size x (bvuminus size k1)))
                      (if (bvlt size k2 k1) ;should just get computed
                          nil
                        (bvlt size x (bvplus size k2 (bvuminus size k1))))
                    (if (bvlt size k2 k1) ;should just get computed
                        (bvlt size x (bvplus size k2 (bvuminus size k1)))
                      t))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma-alt-helper (y (ifix k2)))
           :in-theory (disable bvlt-add-to-both-sides-constant-lemma-alt-helper))))

;;(BVLT 31 4 (BVPLUS 31 5 y))


;; (defthm bvlt-subtract-from-both-sides
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (integerp z)
;;                 )
;;            (equal (bvlt 31 x y)
;;                   (if (bvlt 31 z y)
;;                       (bvlt 31 (bvminus 31 x z) (bvminus 31 y z))
;;                     xx)))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
;;                                                                                                    PLUS-1-AND-BVCHOP-BECOMES-BVPLUS)))))


;; (defthm bvlt-of-bvplus-gen
;;   (implies (and (integerp x)
;;                 (integerp k1)
;;                 (integerp k2)
;;                 )
;;            (equal (bvlt 31 k1 (bvplus 31 k2 x))


;;            )
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1)))))


;; (defthm bvlt-of-bvplus-gen
;;   (implies (and (integerp x)
;;                 (unsigned-byte-p 31 k1)
;;                 (unsigned-byte-p 31 k2))
;;            (equal (bvlt 31 k1 (bvplus 31 k2 x))
;;                   (if (equal (bvchop 31 x) 0)
;;                       (bvlt 31 k1 k2)
;;                     (if (bvlt 31 (bvuminus 31 k2) x) ;overflow
;;                         (if (bvlt 31 k1 k2)
;;                             (bvlt 31 (- (+ 2147483648 K1) k2) X)
;;                           xx ;(bvlt 31 (bvminus 31 k2 k1) x) ;(< (+ 2147483648 K1) (+ K2 (BVCHOP 31 X))) ;;
;;                           )
;;                       (if (bvlt 31 k1 k2)
;;                           (< K1 (+ K2 (BVCHOP 31 X))) ;;
;;                         (bvlt 31 (bvminus 31 k1 k2) x))))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1)))))


;; (thm
;;  (implies (and (EQUAL (BVCHOP 31 x) free)
;;                (syntaxp (quotep free)))
;;           (equal (SLICE 31 2 x)
;;                  (slice 31 2 free))))

(defthm bvlt-of-bvplus-tighten-arg1
  (implies (unsigned-byte-p 31 z)
           (equal (BVLT 32 (BVplus 31 x y) z)
                  (BVLT 31 (BVplus 31 x y) z)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;; (defthm low-bits-dont-matter2
;;   (implies (and (<= x y)
;;                 (< z (expt 2 n))
;;                 (integerp x)
;;                 (integerp z)
;;                 (integerp y)
;;                 )
;;            (<= (+ z (* (expt 2 n) x))
;;                (* (expt 2 n) y)))
;;   :hints (("Goal" :in-theory (disable ineq-hack2 ineq-hack *-preserves->=-for-nonnegatives <-*-right-cancel *-preserves->-for-nonnegatives-1)
;;            :use (:instance multiply-both-sides-hack (y y) (x x) (z (expt 2 n))))))

;; (defthm plus-of-times-expt-bound2
;;   (implies (and (<= (logtail lowsize x) hv)
;;                 (integerp hv)
;;                 (natp lowsize)
;;                 (unsigned-byte-p lowsize lv)
;;                 (integerp x)
;;                 )
;;            (<= x (+ lv (* hv (expt 2 lowsize)))))
;;   :hints (("Goal" :use ((:instance logtail-times-expt-bound (size lowsize))
;;                         )
;;            :in-theory (disable bvchop-plus-times-expt-logtail low-bits-dont-matter LOGTAIL-TIMES-EXPT-BOUND))))

;; (thm
;;  (implies (and (EQUAL 0 (SLICE 31 2 x))
;;                (natp x))
;;           (equal (bvlt 32 x 16)
;;                  nil))
;;  :otf-flg t
;;  :hints (("Goal"
;;           :use (:instance BVCAT-SLICE-SAME (m 30) (k 31) (n 2) (x x))
;;           :in-theory (e/d ( ;slice
;;                            bvlt bvchop-of-sum-cases bvplus bvuminus bvminus)
;;                           (BVCAT-SLICE-SAME anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
;;                                             BVCAT-EQUAL-REWRITE-ALT
;;                                             BVCAT-EQUAL-REWRITE
;;                                             BVCAT-TIGHTEN-FROM-BOUND-4-20-2
;;                                             BVCAT-TIGHTEN-UPPER-SIZE
;;                                             BVCAT-OF-0
;;                                             plus-1-and-bvchop-becomes-bvplus)))))


;gen
(defthm slice-when-low-slice-known
  (implies (and (equal (slice 30 2 x) free)
                (syntaxp (quotep free)))
           (equal (slice 31 2 x)
                  (bvcat 1 (slice 31 31 x)
                         29 free))))

;; (defthm slice-of-bvplus-32-2-4
;;   (implies (integerp x)
;;            (equal (slice 31 2 (bvplus 32 4 x))
;;                   (bvplus 30 1 (slice 31 2 x))))
;;   :hints (("Goal" :in-theory (e/d (bvplus slice bvchop-of-sum-cases bvchop-of-logtail)
;;                                   (anti-bvplus anti-slice BVCHOP-PLUS-1-SPLIT)))))

;these still seem dangerous.. - use polarities?
(defthmd slice-extend-hack
  (implies (and (syntaxp (symbolp x)) ;seems to loop when x is a term that's too small
                (equal 0 (getbit 31 x)))
           (equal (equal (slice 30 2 x) 0)
                  (equal (slice 31 2 x) 0)))
  :hints (("Goal" :use (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT
                                  (n 29)
                                  (x (slice 31 2 x))
                                  )
           :in-theory (disable EQUAL-OF-SLICE-AND-SLICE
                               BVCAT-OF-GETBIT-AND-X-ADJACENT
                               SLICE-WHEN-LOW-SLICE-KNOWN
                               BVCAT-TIGHTEN-LOW-ARG
                               REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1
                               GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))))

(defthmd bvchop-extend-hack
  (implies (and (syntaxp (symbolp x)) ;seems to loop when x is a term that's too small
                (equal 0 (getbit size x))
                (natp size))
           (equal (equal (bvchop size x) 0)
                  (equal (bvchop (+ 1 size) x) 0)))
  :hints (("Goal" :use (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT
                                  (n size)
                                  (x (bvchop (+ 1 size) x))
                                  )
           :in-theory (disable BVCAT-OF-GETBIT-AND-X-ADJACENT
                               SLICE-WHEN-LOW-SLICE-KNOWN
                               BVCAT-TIGHTEN-LOW-ARG
                               REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1
                               GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))))

(in-theory (disable BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN))

(defthm bvlt-when-slice-0-hack
  (implies (and (equal (slice 31 2 x) 0) ;slow?
                (unsigned-byte-p 32 x))
           (equal (bvlt 32 3 x)
                  nil))
  :hints (("Goal"
           :use (:instance bvcat-slice-same (m 30) (k 31) (n 2) (x x))
           :in-theory (e/d (bvlt) (bvcat-slice-same <-becomes-bvlt
                                                    <-becomes-bvlt-alt <-becomes-bvlt <-becomes-bvlt-free)))))

(defthm bvchop-tighten-when-slice-0
  (implies (and (equal (slice k free x) 0)
                (equal k (+ -1 n))
                (< free n)
                (natp free)
                (posp n))
           (equal (bvchop n x)
                  (bvchop free x)))
  :hints (("Goal" :use (:instance rewrite-bv-equality-when-sizes-dont-match-2
                                  (x (bvchop free x)) (x-size free) (y (bvchop n x)) (y-size n)))))

(defthm bvlt-tighten-when-slice-0
  (implies (and (EQUAL (SLICE 31 2 x) 0)
                (unsigned-byte-p 2 z))
           (equal (BVLT 32 z x)
                  (bvlt 2 z x)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( ;<-becomes-bvlt
                                          <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                                             GETBIT-WHEN-BVLT-OF-SMALL-HELPER
                                                             BVLT-TIGHTEN-WHEN-GETBIT-0
                                          )))))



(defthm unsigned-byte-p-of-plus-minus-4
  (implies (unsigned-byte-p 32 x)
           (equal (unsigned-byte-p 32 (+ -4 x))
                  (bvlt 32 3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvchop-identity)
                                  ( ;<-becomes-bvlt
                                   <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                   )))))

(defthm unsigned-byte-p-of-plus-1
  (implies (unsigned-byte-p 32 x)
           (equal (unsigned-byte-p 32 (+ 1 x))
                  (not (equal x (+ -1 (expt 2 32))))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  ( ;<-becomes-bvlt
                                   <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                   )))))




;; (thm
;;  (implies (and (EQUAL 0 (BVCHOP 31 x))
;;                )
;;           (equal (BVLT 32 3 x)

(defthm zp-when-unsigned-byte-p
  (implies (unsigned-byte-p free x)
           (equal (zp x)
                  (equal 0 x))))



(defthm slice-31-2-minus-4
  (implies (natp x)
           (equal (SLICE 31 2 (+ -4 x))
                  (if (< x 4)
                      1073741823
                    (bvplus 30 -1 (slice 31 2 x)))))
  :hints (("Goal" :in-theory (e/d (bvplus-recollapse slice LOGTAIL-OF-BVCHOP) (anti-slice BVCHOP-OF-LOGTAIL)))))

;; (defthm slice-when-bvlt
;;   (implies (bvlt 32 x 4)
;;            (equal (slice 31 2 x)
;;                   0))
;;   :rule-classes ((:rewrite :backchain-limit-lst (1)))
;;   :hints (("Goal"
;;            :use (:instance bvcat-slice-same (m 30) (k 31) (n 2) (x x))
;;            :in-theory (e/d (bvlt) (bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite
;;                                                     <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvminus-tighten
  (implies (and (unsigned-byte-p 30 x) ;gen
                (integerp x))
           (equal (bvuminus 32 x)
                  (if (equal 0 x)
                      0
                    (bvplus 32 3221225472
                            (bvuminus 30 x)))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p bvlt bvchop-of-sum-cases bvplus bvuminus bvminus
                                                   bvchop-identity)
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                               <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                               plus-1-and-bvchop-becomes-bvplus)))))

(defthm bvlt-of-bvuminus-trim2
  (implies (unsigned-byte-p 30 z)
           (equal (BVLT 32 (BVUMINUS 30 x) z)
                  (BVLT 30 (BVUMINUS 30 x) z)))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-identity)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-trim2b
  (implies (unsigned-byte-p 30 z)
           (equal (BVLT 32 z (BVUMINUS 30 x))
                  (BVLT 30 z (BVUMINUS 30 x))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-identity)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))



;; (thm
;;  (equal (BVLT 32 (BVUMINUS 30 x) 1073741820)
;;         (bvlt 32

(defthmd bvchop-extend-hack-gen
  (implies (and (syntaxp (symbolp x)) ;seems to loop when x is a term that's too small
                (equal 0 (getbit size x))
                (natp size))
           (equal (bvchop size x)
                  (bvchop (+ 1 size) x)))
  :hints (("Goal" :use (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT
                                  (n size)
                                  (x (bvchop (+ 1 size) x))
                                  )
           :in-theory (disable BVCAT-OF-GETBIT-AND-X-ADJACENT
                               SLICE-WHEN-LOW-SLICE-KNOWN
                               BVCAT-TIGHTEN-LOW-ARG
                               REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1
                               GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))))

(local (in-theory (enable unsigned-byte-p-forced)))

;can loop?
(defthmd rewrite-<-when-sizes-dont-match
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'x-size x) (x-size))
                (bind-free (bind-var-to-unsigned-term-size 'y-size y) (y-size))
                (< y-size x-size)
                (syntaxp (and (not (quotep x))
                              (not (quotep y))))
                ;(syntaxp (not (equal y ''0)))
                (force (natp x-size))
                (force (natp y-size))
                (force (unsigned-byte-p-forced x-size x))
                (force (unsigned-byte-p-forced y-size y)))
           (equal (< x y)
                  (and (< (bvchop y-size x) y)
                       (equal (slice (+ -1 x-size) y-size x)
                              0))))
  :hints (("Goal" :use (:instance bvcat-slice-same (x x) (k (+ -1 x-size)) (n y-size) (m (+ x-size (- y-size))))
           :in-theory (disable bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite BVCAT-OF-SLICE-AND-X-ADJACENT
                               <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free))))

(local (in-theory (disable <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free))) ;fixme

;can loop?
(defthmd rewrite-<-when-sizes-dont-match2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'x-size x) (x-size))
                (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'y-size y) (y-size))
                (syntaxp (and (not (quotep x))
                              (not (quotep y))))
                (< x-size y-size)
                ;(syntaxp (not (equal y ''0)))
                (force (natp x-size))
                (force (natp y-size))
                (force (unsigned-byte-p-forced x-size x))
                (force (unsigned-byte-p-forced y-size y)))
           (equal (< x y)
                  (or (< x (bvchop x-size y))
                      (not (equal (slice (+ -1 y-size) x-size y)
                                  0)))))
  :hints (("Goal" :use (:instance BVCAT-SLICE-SAME (x y) (k (+ -1 y-size)) (n x-size) (m (+ y-size (- x-size))))
           :in-theory (disable BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE BVCAT-OF-SLICE-AND-X-ADJACENT))))

(local (in-theory (enable bvchop-identity))) ;sigh

(defthm bvlt-of-bvuminus-tighten-arg1-31-30
  (implies (integerp z)
           (equal (bvlt 31 z (bvuminus 30 x))
                  (if (unsigned-byte-p 30 (bvchop 31 z))
                      (bvlt 30 z (bvuminus 30 x))
                    nil)))
  :hints (("Goal" :in-theory (e/d (bvlt rewrite-<-when-sizes-dont-match) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-tighten-arg1-31-30-alt
  (implies (integerp z)
           (equal (bvlt 31 (bvuminus 30 x) z)
                  (if (unsigned-byte-p 30 (bvchop 31 z))
                      (bvlt 30 (bvuminus 30 x) z)
                    t)))
  :hints (("Goal" :in-theory (e/d (bvlt rewrite-<-when-sizes-dont-match2) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-tighten-arg1-32-30
  (implies (integerp z)
           (equal (bvlt 32 z (bvuminus 30 x))
                  (if (unsigned-byte-p 30 (bvchop 32 z))
                      (bvlt 30 z (bvuminus 30 x))
                    nil)))
  :hints (("Goal" :in-theory (e/d (bvlt rewrite-<-when-sizes-dont-match) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthm bvlt-of-bvuminus-tighten-arg1-32-30-alt
  (implies (integerp z)
           (equal (bvlt 32 (bvuminus 30 x) z)
                  (if (unsigned-byte-p 30 (bvchop 32 z))
                      (bvlt 30 (bvuminus 30 x) z)
                    t)))
  :hints (("Goal" :in-theory (e/d (bvlt rewrite-<-when-sizes-dont-match2) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

(defthmd bvchop-contract-hack-gen
  (implies (and (syntaxp (symbolp x)) ;seems to loop when x is a term that's too small
                (equal 0 (getbit (+ -1 size) x))
                (posp size))
           (equal (bvchop size x)
                  (bvchop (+ -1 size) x)))
;  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil)))
  :hints (("Goal" :use (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT
                                  (n (+ -1 size))
                                  (x x)
                                  )
           :in-theory (disable BVCAT-OF-GETBIT-AND-X-ADJACENT
                               ;hack1112
                               SLICE-WHEN-LOW-SLICE-KNOWN
                               BVCAT-TIGHTEN-LOW-ARG
                               REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1
                               GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))))

;rename this is only for plus 1!
(defthm +-of-bvplus
  (implies (natp size)
           (equal (+ 1 (bvplus size x y))
                  (if (equal (+ -1 (expt 2 size)) (bvplus size x y))
                      (expt 2 size)
                    (bvplus size 1 (bvplus size x y)))))
  :hints (("Goal" :in-theory (e/d (bvchop-of-sum-cases bvplus bvuminus bvminus
                                                        )
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                               plus-1-and-bvchop-becomes-bvplus
                                               ;slice-when-bvlt
                                               bvchop-tighten-when-slice-0
                                               )))))



;kill the other
;slow
(defthmd bvlt-tighten-when-slice-0-gen
  (implies (and (equal (slice (+ -1 size) 2 x) 0)
                (natp size)
                (< 3 size)
                (unsigned-byte-p 2 z))
           (equal (bvlt size z x)
                  (bvlt 2 z x)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil nil)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (hs (- size 2)) (ls 2))
           :in-theory (e/d (bvlt) ( ;<-becomes-bvlt
                                   <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                   )))))



(defthm bvplus-reduce-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (unsigned-byte-p 32 k1)
                (unsigned-byte-p 32 k2))
           (equal (equal (bvplus 32 k1 x) (bvplus 32 k2 y))
                  (equal (bvplus 32 (bvplus 32 (bvuminus 32 (min k1 k2)) k1) x)
                         (bvplus 32 (bvplus 32 (bvuminus 32 (min k1 k2)) k2) y))))
  :hints (("Goal" :in-theory (e/d (bvchop-of-sum-cases ; bvplus bvuminus bvminus
                                   )
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                               plus-1-and-bvchop-becomes-bvplus
                                               ;slice-when-bvlt
                                               bvchop-tighten-when-slice-0
                                               )))))


;gen the bvuminus
(defthm bvplus-32-of-bvuminus-30
  (implies (integerp x)
           (equal (bvplus 32 1 (bvuminus 30 x))
                  (if (equal (bvuminus 30 x) (+ -1 (expt 2 30)))
                      (expt 2 30)
                    (bvplus 30 1 (bvuminus 30 x)))))
  :hints (("Goal" :in-theory (e/d (bvchop-of-sum-cases bvplus bvuminus bvminus
                                                        )
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                               plus-1-and-bvchop-becomes-bvplus
                                               ;slice-when-bvlt
                                               bvchop-tighten-when-slice-0
                                               )))))



(defthm bv-1-0-hack
  (implies (and (not (bvlt size 1 x))
                (not (equal 0 x))
                (unsigned-byte-p size x)
                )
           (equal (equal 1 x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil)))
  :hints (("Goal"
           :in-theory (e/d (bvlt) (<-BECOMES-BVLT)))))

(defthm UNSIGNED-BYTE-P-tighten
  (implies (equal 0 (getbit 31 x))
           (equal (UNSIGNED-BYTE-P 32 x)
                  (UNSIGNED-BYTE-P 31 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (hs 1) (ls 31))
           :in-theory (e/d () (BVCHOP-CONTRACT-HACK-GEN REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1)))))

(defthm bv-3-2-1-hack
  (implies (and (bvlt size 1 x)
                (not (bvlt size 3 x))
                (not (equal x 2))
                (unsigned-byte-p size x)
                (posp size)
                )
           (equal (equal 3 x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0 nil 0)))
  :hints (("Goal"
           :in-theory (e/d (bvlt <=-OF-BVCHOP-SAME-LINEAR) (<-becomes-bvlt)))))

(defthm bv-3-2-1-hackb
  (implies (and (bvlt 2 1 x)
                (not (equal x 2))
                (unsigned-byte-p 2 x)
                )
           (equal (equal 3 x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil)))
  :hints (("Goal"
           :in-theory (e/d (bvlt) (<-becomes-bvlt)))))

;for speed:
(in-theory (disable GETBIT-BOUND-LINEAR))

;; (defthm getbit-when-not-1-stronger
;;   (implies (not (equal (getbit n x) 1))
;;            (equal (getbit n x)
;;                   0))
;;   :rule-classes ((:rewrite :backchain-limit-lst (1))))

(DEFTHM UNSIGNED-BYTE-P-TIGHTEN-alt
  (IMPLIES (not (EQUAL 1 (GETBIT 31 X)))
           (EQUAL (UNSIGNED-BYTE-P 32 X)
                  (UNSIGNED-BYTE-P 31 X)))
  :hints (("Goal" :use (:instance UNSIGNED-BYTE-P-TIGHTEN)))
  :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST (0))))


(local (in-theory (disable MOD-BY-4-BECOMES-BVCHOP)))

;new

(defthm sbvmoddown-32-4-non-neg
  (implies (and (not (sbvlt '32 x '0))
                (integerp x))
           (equal (sbvmoddown 32 x 4)
                  (bvmod 31 x 4)))
  :hints (("Goal" :in-theory (enable bvchop sbvmoddown bvmod sbvlt-rewrite))))

(in-theory (disable bvmod))  ;fixme drop

;; (thm
;;  (implies (not (natp n))
;;           (equal (getbit n x)
;;                  0))
;;  :hints (("Goal" :in-theory (e/d (getbit slice) (anti-slice bvchop-1-becomes-getbit slice-becomes-getbit)))))

(in-theory (disable BIT-BLAST-3)) ;move up

(defthm bvchop-equal-constant-reduce-when-top-bit-3-2-4
  (implies (equal 1 (getbit 2 x))
           (equal (equal (bvchop 3 x) 4)
                  (equal (bvchop 2 x) 0)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthm unsigned-byte-p-of-minus-of-expt-and-bvchop
  (implies (equal k (expt 2 size))
           (equal (unsigned-byte-p size (+ k (- (BVCHOP size X))))
                  (not (equal 0 (BVCHOP size X)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(in-theory (disable ;cancel-floor-+

            ))

(local (in-theory (disable floor-type-3)))



;(in-theory (disable BVCHOP-LEQ))

(defthm equal-of-bvchop-of-plus-1-and-bvchop
  (implies (and (posp size)
                (integerp x))
           (equal (equal (bvchop size (+ 1 x)) (bvchop size x))
                  nil))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvuminus-when-smaller-no-split-bind-free
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'free x))
                (syntaxp (quotep size))
                (syntaxp (quotep free))
                (< free size)
                (not (equal 0 x))
                (natp size)
                (force (unsigned-byte-p-forced free x))
                )
           (equal (bvuminus size x)
                  (bvplus size (- (expt 2 size) (expt 2 free)) (bvuminus free x))))
  :hints (("Goal" :use (:instance bvuminus-when-smaller)
           :in-theory (disable bvuminus-when-smaller))))

(defthm bvuminus-when-smaller-no-split
  (implies (and (unsigned-byte-p free x)
                (syntaxp (quotep size))
                (syntaxp (quotep free))
                (< free size)
                (not (equal 0 x))
                (Natp size))
           (equal (bvuminus size x)
                  (bvplus size (- (expt 2 size) (expt 2 free)) (bvuminus free x))))
  :hints (("Goal" :use (:instance bvuminus-when-smaller)
           :in-theory (disable bvuminus-when-smaller))))

(defthmd bvchop-32-split-30-hack
  (equal (bvchop 32 x)
         (+ (bvchop 30 x) (* (expt 2 30) (slice 31 30 x))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp) ( BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE))
           :use ((:instance split-with-bvcat (hs 2) (ls 30))))))

(defthm bvplus-30-expand
  (implies (and (< (bvplus 32 x y) (expt 2 30))
                (integerp x)
                (integerp y)
                )
           (equal (bvplus 32 x y)
                  (bvplus 30 x y)))
  :hints (("Goal"
     ;  :use ((:instance split-with-bvcat (hs 2) (ls 30))
     ;       (:instance split-with-bvcat (x y) (hs 2) (ls 30)))
           :cases ((equal 0 (SLICE 31 30 X)))
           :in-theory (e/d (bvchop-32-split-30-hack ;gross!
                            bvchop-of-sum-cases bvplus bvuminus bvminus bvcat logapp
                            )
                           (anti-bvplus bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                        plus-1-and-bvchop-becomes-bvplus
                                        ;slice-when-bvlt
                                        bvchop-tighten-when-slice-0
                                        BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE)))))

;can loop...
(defthmd bvplus-32-of-bvplus-30
  (implies (and (bvlt 32 (bvplus 32 x y) (expt 2 30))
                (integerp x)
                (integerp y)
                )
           (equal (bvplus 32 k (bvplus 30 x y))
                  (bvplus 32 k (bvplus 32 x y))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-bound-hack
  (equal (bvlt '31 (bvplus '30 x y) '1073741824)
         t)
  :hints (("Goal" :in-theory (e/d (bvlt) ()))))

(in-theory (disable BVPLUS-30-EXPAND))


(defthmd bvchop-32-split-30-hack2
  (equal (bvchop 32 x)
         (bvcat 2 (slice 31 30 x) 30 x))
  :hints (("Goal" :in-theory (e/d (bvcat logapp) (BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE))
           :use ((:instance split-with-bvcat (hs 2) (ls 30))))))

(defthm bvplus-3221225472-hack
  (implies (unsigned-byte-p 30 x)
           (equal (bvplus 32 3221225472 x) ;the low bits are all 0
                  (bvcat 2 3 30 x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvcat logapp) (anti-bvplus BVLT-OF-BVCHOP-ARG2 BVLT-OF-BVCHOP-ARG3 BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2)))))




(defthmd usb3-cases
  (equal (unsigned-byte-p 3 x)
         (or (equal x 0)(equal x 1)(equal x 2)(equal x 3)(equal x 4)(equal x 5)(equal x 6)(equal x 7))))

(in-theory (enable floor-when-multiple)) ;drop?

(defthmd bvchop-extend-by-1
  (implies (posp size)
           (equal (bvchop (+ -1 size) y)
                  (- (bvchop size y) (* (expt 2 (+ -1 size)) (getbit (+ -1 size) y)))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp posp) (bvcat-of-getbit-and-x-adjacent))
           :use ((:instance split-with-bvcat (x y) (hs 1) (ls (+ -1 size)))))))


(defthm minus-two-expts
  (implies (posp size)
           (equal (+ (- (expt 2 (+ -1 size))) (- (expt 2 (+ -1 size))))
                  (- (expt 2 size))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm times-x-slash-x
  (implies (and (rationalp x)
                (rationalp y))
           (equal (* Y (/ Y) x)
                  (if (equal 0 y)
                      0
                    x))))

(defthm bvchop-of-sum-minus-expt
  (implies (and (natp size)
                (integerp x))
           (equal (BVCHOP SIZE (+ X (- (EXPT 2 SIZE))))
                  (BVCHOP SIZE X)))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-sum-expt
  (implies (and (natp size)
                (integerp y)
                (integerp x))
           (equal (bvchop size (+ x (expt 2 size) y))
                  (bvchop size (+ x y))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-sum-minus-expt-alt
  (implies (and (natp size)
                (integerp x)
                (integerp y))
           (equal (BVCHOP SIZE (+ X (- (EXPT 2 SIZE)) y))
                  (BVCHOP SIZE (+ X y))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))



(defthm bvchop-of-plus-of-times-expt
  (implies (and (natp size)
                (integerp x)
                (integerp y))
           (equal (bvchop size (+ x (* (expt 2 size) y)))
                  (bvchop size x)))
  :hints (("Goal" :in-theory (disable bvplus-of-*-arg2 bvplus-recollapse))))

(defthmd usb4-cases
  (equal (unsigned-byte-p 4 x)
         (or (equal x 0)(equal x 1)(equal x 2)(equal x 3)(equal x 4)(equal x 5)(equal x 6)(equal x 7)
             (equal x 8)(equal x 9)(equal x 10)(equal x 11)(equal x 12)(equal x 13)(equal x 14)(equal x 15))))



(defthm bvlt-of-bvcat-trim
  (equal (bvlt 31 z (bvcat 2 x 30 y))
         (bvlt 31 z (bvcat 1 x 30 y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;see MOD-BY-4-BECOMES-BVCHOP
;gen
(defthm bvmod-31-4
  (equal (bvmod 31 x 4)
         (bvchop 2 x))
  :hints (("Goal" :in-theory (e/d (bvmod bvchop) (multiple-idioms-for-multiple-4
                                                    mod-type
                                                   mod-of-expt-of-2-constant-version
                                                   mod-of-expt-of-2
                                                   )))))

;gen!
(defthm bvmod-3-4
  (implies (integerp x)
           (equal (BVMOD 3 x 4)
                  (bvchop 2 x)))
  :hints (("Goal" :in-theory (e/d (bvmod bvchop) (MULTIPLE-IDIOMS-FOR-MULTIPLE-4
                                                  MOD-TYPE
                                                  )))))

(defthm bvdiv-31-4
  (equal (bvdiv 31 x 4)
         (slice 30 2 x))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (bvdiv bvchop-when-i-is-not-an-integer
                                  SLICE-WHEN-VAL-IS-NOT-AN-INTEGER
                                  bvchop-of-logtail-becomes-slice)
                           ()))))

(defthm high-slice-equal-1-rewrite
  (implies (unsigned-byte-p 32 x)
           (equal (equal 1 (slice 31 2 x))
                  (and (unsigned-byte-p 3 x)
                       (equal 1 (getbit 2 x)))))
  :hints (("Goal" :use ((:instance split-with-bvcat (hs 30) (ls 2)))
           :in-theory (disable bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite BVCAT-OF-SLICE-AND-X-ADJACENT))))

(defthm sbvmoddown-of-minus-4
  (implies (integerp x)
           (equal (sbvmoddown 32 (+ -4 x) 4)
                  (sbvmoddown 32 x 4)))
  :hints (("Goal" :in-theory (enable sbvmoddown))))

(defthm sbvle-of-minus-4
  (implies (and (sbvle 32 0 x) ;drop of move to conclusion?
                (integerp x))
           (equal (sbvle '32 '0 (+ -4 x))
                  (sbvle '32 4 x)))
  :hints (("Goal" :in-theory (enable sbvle getbit-of-plus))))

;gen the 1
(defthm equal-if-0-0-1
  (equal (equal '0 (if test '1 '0))
         (not test)))

(defthm integerp-of-times-1/4-bvchop-31
  (IMPLIES (AND (INTEGERP X)
                )
           (equal (INTEGERP (* 1/4 (bvchop 31 X)))
                  (INTEGERP (* 1/4 X))))
  :hints (("Goal" :in-theory (e/d (bvchop mod) (;MOD-RECOLLAPSE-LEMMA2 MOD-RECOLLAPSE-LEMMA
                                                )))))

(defthm integerp-of-times-1/4-logext-32
  (IMPLIES (AND (INTEGERP X)
                )
           (equal (INTEGERP (* 1/4 (LOGEXT 32 X)))
                  (INTEGERP (* 1/4 X))))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthm not-greater-than-1
  (implies (and (not (equal 0 garg0))
                (unsigned-byte-p 31 garg0)
                )
           (equal (bvlt 31 1 garg0)
                  (not (equal 1 garg0))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1))))

(theory-invariant (incompatible (:definition bvlt) (:rewrite <-BECOMES-BVLT)))

(theory-invariant (incompatible (:definition bvlt) (:rewrite <-BECOMES-BVLT-alt)))



(defthm bound-hack
  (implies (and (UNSIGNED-BYTE-P 31 GARG0)
                (NOT (EQUAL GARG0 2)))
           (equal (BVLT 31 1 GARG0)
                  (BVLT 31 2 GARG0)))
  :hints (("Goal" :in-theory (disable BVLT-WHEN-NOT-BVLT-ONE-MORE)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1))))

(defthm bound-hack2
  (implies (unsigned-byte-p 31 garg0)
           (equal (bvlt 31 2 garg0)
                  (not (or (equal 0 garg0)
                           (equal 1 garg0)
                           (equal 2 garg0)))))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt))))  )

;todo: use polarity?
(defthmd bvchop-31-equal-0-extend
  (implies (EQUAL 0 (GETBIT 31 x))
           (equal (EQUAL 0 (BVCHOP 31 x))
                  (EQUAL 0 (BVCHOP 32 x)))))

;;(EQUAL FARG0 (BVPLUS '32 '4 (SBVDIVDOWN '32 GARG0 '4294967292)))

;; garg0: 15 11 7 3 -1
;; to
;; farg0: 0 1 2 3 4
;; the sbvdivdown takes garg0 to
;; -4 -3 -2 -1 0

;; ;seems bad to divide by a negative...
;; could flip first to
;; -15 -11 -7 -3 1
;; then do (SBVDIVDOWN '32 x 4)
;; then add 4

;;(BITNOT (BITXOR '1 (GETBIT '31 GARG0)))

(defthm not-usb-rule
  (implies (and (equal 0 (bvchop 2 x))
                (not (equal 0 x)))
           (equal (unsigned-byte-p '2 x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1))))

(defthm UNSIGNED-BYTE-P-of-expt-minus-x
 (implies (unsigned-byte-p 32 x)
          (equal (UNSIGNED-BYTE-P 32 (+ 4294967296 (- X)))
                 (not (equal 0 x))))
 :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))



;terrible
(defthmd bvuminus32-when-usb31
  (implies (unsigned-byte-p 31 x)
           (equal (bvuminus '32 x)
                  (if (equal 0 (bvchop 32 x))
                      0
                    (bvcat 1 1 31 (bvuminus 31 x)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvplus getbit slice) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus
                                                                                      BVLT-OF-BVCHOP-ARG2
                                                                                    BVLT-OF-BVCHOP-ARG3
                                                                                    BVCAT-OF-+-LOW ;looped
                                                                                    BVCHOP-1-BECOMES-GETBIT
                                                                                    SLICE-BECOMES-GETBIT
                                                                                    anti-slice
                                                                                    BITXOR-OF-SLICE-ARG2 ;looped
                                                                                    )))))

(defthm equal-1-getbit-bvuminus
  (implies (unsigned-byte-p 31 x)
           (equal (equal '1 (getbit '31 (bvuminus 32 x)))
                  (and (not (equal 0 x))
                       (bvle 32 x (expt 2 31)))))
  :hints (("Goal" :in-theory (e/d (bvuminus32-when-usb31 bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm equal-0-getbit-bvuminus
  (implies (unsigned-byte-p 31 x)
           (equal (equal 0 (getbit '31 (bvuminus 32 x)))
                  (not (and (not (equal 0 x))
                            (bvle 32 x (expt 2 31))))))
  :hints (("Goal" :use (:instance equal-1-getbit-bvuminus)
           :in-theory (disable equal-1-getbit-bvuminus))))

;gen!
(defthm slice-31-2-plus-expt
 (implies (integerp x)
          (equal (slice 31 2 (+ 4294967296 x))
                 (slice 31 2 x))))

;yuck!
(defthmd bvlt-16-split
  (implies (UNSIGNED-BYTE-P 31 x)
           (equal (BVLT 31 16 x)
                  (not (or (equal x 0)(equal x 1)(equal x 2)(equal x 3)(equal x 4)(equal x 5)(equal x 6)(equal x 7)
                           (equal x 8)(equal x 9)(equal x 10)(equal x 11)(equal x 12)(equal x 13)(equal x 14)(equal x 15) (equal x 16)))))
  :hints (("Goal" :in-theory (e/d (bvuminus32-when-usb31 bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))) )



;; (thm
;;  (implies (integerp x)
;;           (equal (slice 31 2 (- x))
;;                  (if (equal 0 (bvchop 32 x))
;;                      0
;;                    (+ k (expt 2 32) (- (bvchop 32 x))))))
;;  :otf-flg t
;;  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 30) (ls 2)))
;;           :in-theory (e/d (slice bvchop-of-sum-cases) (anti-slice
;;                                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE BVCAT-OF-GETBIT-AND-X-ADJACENT
;;                                                         BVCAT-OF-GETBIT-AND-X-ADJACENT
;;                                                         )))))

;; (thm
;;  (implies (unsigned-byte-p 31 x) ;gen
;;           (equal (sbvdivdown 32 x 4294967292) ;this is -4
;;                  (sbvdivdown 32 (bvuminus 32 x) 4)))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (e/d (bvplus sbvdivdown bvchop-of-sum-cases bvuminus bvminus)
;;                                  (BVLT-OF-PLUS-ARG1
;;                                   BVLT-OF-PLUS-ARG2
;;                                   anti-bvplus bvminus-becomes-bvplus-of-bvuminus)))))

(theory-invariant (incompatible (:definition bvplus) (:rewrite bvlt-of-plus-arg1)))
(theory-invariant (incompatible (:definition bvplus) (:rewrite bvlt-of-plus-arg2)))

(in-theory (disable TIMES-4-BECOMES-LOGAPP))

(local (in-theory (enable bvchop-of-logtail)))

;gen
(defthm slice-bound-lemma
  (implies (integerp x)
           (equal (< (SLICE 30 2 X) 536870911)
                  (< (bvchop 31 x) (bvmult 31 536870911 4))))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

(theory-invariant (incompatible (:definition logtail ) (:rewrite FLOOR-OF-4-BECOMES-LOGTAIL)))

;gen
(defthm logtail-is-max
  (implies (and (<= 2147483645 x)
                (< x 2147483648)
                (integerp x))
           (equal (logtail 2 x)
                  (+ -1 (expt 2 29))))
  :hints (("Goal" :in-theory (e/d (logtail) (floor-of-4-becomes-logtail)))))

(defthm slice-is-max
  (implies (and (<= 2147483645 (bvchop 31 x))
                (integerp x))
           (equal (slice 30 2 x)
                  (+ -1 (expt 2 29))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil)))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail)
                                  (anti-slice)))))

(defthm bvchop-usb-bound
  (implies (and (equal (bvchop 2 x) 0)
                (unsigned-byte-p 31 x))
           (< x 2147483645))
  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 30) (ls 2)))
           :in-theory (e/d (bvcat logapp unsigned-byte-p) ()))))

(local (in-theory (enable sbvlt-rewrite))) ;fixme

;improve this
(defthm sbvdivdown-of-bvplus-15-case-1
  (implies (and (unsigned-byte-p 32 x)
                (not (sbvlt 32 x 2147483633)) ;rewrite?
                )
           (equal (sbvdivdown 32 (bvplus 32 15 x) 4)
                  (if (sbvlt 32 x 2147483645)
                      (bvplus 32 3221225475 (sbvdivdown 32 (bvplus 32 3 x) 4))
                    ;;kk ;2684354563
                    (+ 3221225476 (expt 2 29) -1)
                    )))
  :hints (("Goal" :in-theory (e/d (sbvdivdown bvplus bvlt
                                              logext
                                              slice-of-sum-cases
                                              bvchop-of-sum-cases
                                              bvchop-contract-hack-gen

                                              )
                                  (BVCHOP-PLUS-1-SPLIT
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   anti-bvplus bvlt-of-plus-arg2 bvlt-of-plus-arg1)))))

(defthm sbvdivdown-of-bvplus-15-case-2
  (implies (and (unsigned-byte-p 32 x)
                (sbvlt 32 x 2147483633) ;rewrite?
                )
           (equal (sbvdivdown 32 (bvplus 32 15 x) 4)
                  (bvplus 32 3 (sbvdivdown 32 (bvplus 32 3 x) 4))))
  :hints (("Goal" :in-theory (e/d (sbvdivdown bvplus bvlt
                                              logext
                                              slice-of-sum-cases
                                              ;;bvchop-of-sum-cases
                                              bvchop-of-logtail-becomes-slice
                                              )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  anti-bvplus bvlt-of-plus-arg2 bvlt-of-plus-arg1)))))

;gen!
(defthm sbvdivdown-of-bvplus-15
  (implies (unsigned-byte-p 32 x)
           (equal (sbvdivdown 32 (bvplus 32 15 x) 4)
                  (if (sbvlt 32 x (+ -15 (expt 2 31)))
                      ;;main case:
                      (bvplus 32 3 (sbvdivdown 32 (bvplus 32 3 x) 4))
                    (if (sbvlt 32 x (+ -3 (expt 2 31)))
                        (bvplus 32 3221225475 (sbvdivdown 32 (bvplus 32 3 x) 4))
                      (+ 3221225476 (expt 2 29) -1)
                      ))))
  :hints (("Goal" :in-theory (disable BVCHOP-31-EQUAL-0-EXTEND ;looped
                                      ))))

;gen
(defthm bvlt-false-when-usb
  (implies (unsigned-byte-p 31 x)
           (equal (bvlt 32 2147483648 x)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))


;; (thm
;;  (implies (and (and (unsigned-byte-p 32 x)
;;                     (natp k)

;;                     (< k 100))
;;                (<= (- (expt 2 31) k) (LOGEXT 32 X)))
;;           (equal (sbvdivdown 32 (bvplus 32 k x) 4)
;;                  xx))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (e/d (sbvdivdown bvplus) (anti-bvplus bvlt-of-plus-arg2 bvlt-of-plus-arg1)))))

(defthm slice-of-bvplus-trim
  (equal (SLICE 30 2 (BVPLUS 32 x y))
         (SLICE 30 2 (BVPLUS 31 x y)))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

 ;two ways to write this, but I prefer to split on x since it might be constant
(defthmd slice-of-bvplus-cases-helper
  (implies (natp low)
           (equal (<= (EXPT 2 low) (+ (BVCHOP low X) (BVCHOP low Y)))
                  (if (EQUAL 0 (BVCHOP LOW x))
                      nil
                    (not (bvlt low y (bvuminus low x)))
                    )))
  :hints (("Goal" :in-theory (e/d (bvplus slice-of-sum-cases
                                          bvlt
                                          bvchop-of-sum-cases
                                          bvuminus bvplus bvminus
                                          bvchop-when-i-is-not-an-integer
                                          SLICE-WHEN-VAL-IS-NOT-AN-INTEGER)
                                  (anti-bvplus BVLT-OF-PLUS-ARG2 BVLT-OF-PLUS-ARG1
                                               bvlt-of-plus-arg1 bvlt-of-plus-arg2
                                               bvminus-becomes-bvplus-of-bvuminus
                                               <-BECOMES-BVLT
                                               <-BECOMES-BVLT-alt)))))




(defthm slice-of-bvplus-cases
  (implies (and (equal size (+ 1 high))
                (<= low high)
                (natp low)
                (integerp high))
           (equal (slice high low (bvplus size x y))
                  (if (if (equal 0 (bvchop low x))
                          t
                        (bvlt low y (bvuminus low x)))
                      ;;no carry:
                      (bvplus (+ 1 high (- low))
                              (slice high low x)
                              (slice high low y))
                    ;;if carry
                    (bvplus (+ 1 high (- low))
                            1
                            (bvplus (+ 1 high (- low))
                                    (slice high low x)
                                    (slice high low y))))))
  :hints (("Goal" :in-theory (e/d (bvplus slice-of-sum-cases
                                          slice-of-bvplus-cases-helper
                                          bvchop-when-i-is-not-an-integer
                                          slice-when-val-is-not-an-integer)
                                  (anti-bvplus bvlt-of-plus-arg2 bvlt-of-plus-arg1)))))

;do we always want to do this?  when x is a constant we probably do
;should we lift the if in the conclusion?
(defthm getbit-of-bvplus-split
  (implies (and (< size size2)
                (natp size)
                (integerp size2))
           (equal (getbit size (bvplus size2 x y))
                  (if (if (equal 0 (bvchop size x))
                          t
                        ;if we move the x back to the other side, this can loop?
                        (bvlt size y (bvuminus size x)))
                      (bitxor (getbit size x) (getbit size y))
                    (bitnot (bitxor (getbit size x) (getbit size y))))))
  :hints (("Goal"
           :use (:instance getbit-of-plus (x (ifix x)) (y (ifix y)))
           :in-theory (e/d (bvplus GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                   slice-of-bvplus-cases-helper
                                   ) (getbit-of-plus
                                   anti-bvplus
                                   BVLT-OF-PLUS-ARG1
                                   BVLT-OF-PLUS-ARG2)))))

(defthm equal-of-bvplus-bvplus
  (implies (integerp x)
           (equal (equal (bvplus 31 1 x) (bvplus 32 1 x))
                  (if (equal (bvchop 32 x) (+ -1 (expt 2 32)))
                      t
                    (if (< (bvchop 32 x) (+ -1 (expt 2 31)))
                        t
                      nil))))
  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 1) (ls 31)))
           :in-theory (e/d (bvlt bvcat logapp) (<-BECOMES-BVLT <-BECOMES-BVLT-alt)))))




(defthm introduce-bvlt-hack
  (equal (< (bvplus '29 x y) '4)
         (bvlt 29 (bvplus '29 x y) 4))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt-alt <-becomes-bvlt)))))



;gen to any bv operator
(defthm equal-of-slice-and-impossible-constant
  (implies (and (syntaxp (quotep k))
                (and (integerp high))
                (and (integerp low))
                (<= low high)
                (not (unsigned-byte-p (+ high 1 (- low)) k)))
           (equal (equal k (slice high low x))
                  nil)))

(defthm slice-subst-constant
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop freesize x) free)
                (syntaxp (quotep free))
                (< high freesize)
                (natp high)
                (natp freesize)
                (natp low))
           (equal (slice high low x)
                  (slice high low free))))

(defthm slice-subst-constant-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal free (bvchop freesize x))
                (syntaxp (quotep free))
                (< high freesize)
                (natp high)
                (natp freesize)
                (natp low))
           (equal (slice high low x)
                  (slice high low free))))


;kill?
(defthm bvchop-of-expt-special
  (implies (and (natp low)
                (natp high))
           (equal (BVCHOP (+ -2 HIGH) (* 1/4 (EXPT 2 HIGH)))
                  0))
  :hints (("Goal" :use (:instance bvchop-of-expt-0 (size1 (- high 2)) (size2 (- high 2)))
           :in-theory (disable bvchop-of-expt-0 BVCHOP-OF-EXPT-2-N))))

;kill?
(defthm bvchop-of-expt-special2
  (implies (and (natp low)
                (natp high))
           (equal (BVCHOP (+ -2 HIGH) (* 1/2 (EXPT 2 HIGH)))
                  0))
  :hints (("Goal" :use (:instance bvchop-of-expt-0 (size1 (- high 2)) (size2 (- high 1)))
           :in-theory (e/d (expt-of-+) ( bvchop-of-expt-0 BVCHOP-OF-EXPT-2-N)))))

(defthm bvchop-of-expt-special3
  (implies (and (natp low)
                (natp high))
           (equal (BVCHOP (+ -1 HIGH (- LOW))
                           (* (EXPT 2 HIGH) (/ (EXPT 2 LOW))))
                  0))
  :hints (("Goal" :use (:instance bvchop-of-expt-0 (size1 (+ -1 HIGH (- LOW))) (size2 (- high low)))
           :in-theory (e/d (expt-of-+) ( bvchop-of-expt-0 BVCHOP-OF-EXPT-2-N)))))

(defthm slice-of-bvuminus
  (implies (and (< high size)
                (<= low high)
                (integerp x)
                (integerp size)
                (natp low)
                (natp high))
           (equal (slice high low (bvuminus size x))
                  (if (equal (bvchop low x) 0)
                      (bvuminus (+ 1 high (- low)) (slice high low x))
                    (bvminus (+ 1 high (- low)) (+ -1 (expt 2 (+ 1 high (- low)))) (slice high low x)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus slice-of-sum-cases
                                            bvchop-of-sum-cases
                                            ) (bvchop-of-*
                                               ;BVMULT-OF-2-GEN ;why?
                                               ;EQUAL-OF-BVMULT-AND-*-ALT
                                               ;EQUAL-OF-BVMULT-AND-*
                                               bvminus-becomes-bvplus-of-bvuminus)))))


;kill the other
;fixme - is this a problem?
;fixme should this use bvmult?
;trying disabled
(defthmd slice-bound-lemma-gen
  (implies (and (integerp x)
                (natp low)
                (natp high)
                (<= low high)
                (integerp k))
           (equal (< (slice high low x) k)
                  (< (bvchop (+ 1 high) x) (* k (expt 2 low)))))
  :hints (("Goal" :in-theory (e/d (slice bvmult) (anti-slice bvchop-of-*)))))

(in-theory (disable FLOOR-OF-4-BECOMES-LOGTAIL))

;; (thm
;;  (implies (and (natp i)
;;                (Natp j))
;;           (equal (< j (logtail 2 i))
;;                  (or (< (* 4 j) i)
;;                      (and (equal (* 4 j) i)


;;                      ))
;;  :hints (("Goal" :use (:instance FLOOR-BOUNDED-BY-/ (x i) (y 4))
;;           :in-theory (e/d (logtail) (floor-bound-lemma2 floor-bound-lemma3)))))

;trying disabled
(defthmd slice-bound-lemma-gen2
  (implies (and (integerp k)
                (<= low high)
                (natp low)
                (integerp high))
           (equal (< k (slice high low x))
                  (<= (* (+ 1 k) (expt 2 low)) (bvchop (+ 1 high) x))))
  :hints (("Goal"
           :use (:instance logtail-lessp (pos low) (i (BVCHOP (+ 1 HIGH) X)) (j (+ k 1)))
           :in-theory (e/d (slice) (anti-slice logtail-lessp)))))

(in-theory (disable BVPLUS-OF-*-ARG2 BVPLUS-WHEN-LOW-BITS-ARE-ZERO BVLT-OF-PLUS-ARG2 BVLT-OF-PLUS-ARG1))

;restrict to constants?
;fixme
(defthm bvlt-of-slice-29-30-2
  (implies (and (natp x)
                (integerp k))
           (equal (bvlt '29 k (slice '30 '2 x))
                  (if (equal (bvchop 29 k) (+ -1 (expt 2 29)))
                      nil
                    (bvle 31 (bvmult 31 (bvplus 31 1 k) (expt 2 2)) x))))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult bvplus bvchop-of-sum-cases
                                        slice-bound-lemma-gen2
                                        slice-bound-lemma-gen)
                                  (
                                   bvchop-of-*
                                   anti-bvplus
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   <-of-bvcat-alt        ;looped
                                   <-of-bvcat-alt-helper ;disable?
                                   )))))


(in-theory (disable <-BECOMES-BVLT <-BECOMES-BVLT-alt))

;; (thm
;;  (implies (and (integerp (* (expt 2 (+ -1 size)) (/ y)))
;;                (natp y)
;;                (not (equal 0 y))
;;                (natp size))
;;           (equal (unsigned-byte-p size (* (expt 2 (+ -1 size)) (/ y)))
;;                  t
;;                  ))
;;  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm bvchop-bound-lemma
  (implies (posp size)
           (not (< (EXPT 2 SIZE) (BVCHOP (+ -1 SIZE) x))))
  :hints (("Goal" :use (:instance BVCHOP-UPPER-BOUND (n (+ -1 size)) (x x))
           :in-theory (disable BVCHOP-UPPER-BOUND BVCHOP-BOUND-2)
           )))


;; (skip -proofs
;; (defthm sbvdivdown-by-minus4-equal-0
;;    (implies (unsigned-byte-p 32 x)
;;             (equal (equal 0 (sbvdivdown 32 x 4294967292))
;;                    (or (bvle 32 -3 x)
;;                        (bvle 32 x 0))))
;;    :otf-flg t
;;    :hints (("Goal" :in-theory (e/d (;sbvdivdown
;;                                     bvlt) (<-becomes-bvlt <-becomes-bvlt-alt))))))

;; ;fixme!
;; (skip -proofs
;;  (defthm not-greater-than-3
;;    (implies (and (unsigned-byte-p 31 garg0)
;;                  (equal 0 (bvchop 2 garg0))
;;                  )
;;             (equal (bvlt 31 3 garg0)
;;                    (not (equal garg0 0))))
;;    :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
;;    :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT))))
;;    ))

;; ;fixme!
;; (skip -proofs
;;  (defthm sbvdivdown-of-subtract-4-and-minus-4
;;    (implies (and (integerp x)
;;                  (unsigned-byte-p 32 x))
;;             (equal (sbvdivdown 32 (+ -4 x) 4294967292)
;;                    (if (EQUAL (LOGEXT 32 X) -2147483648)
;;                        3758096385
;;                      (bvplus 32 1 (sbvdivdown 32 x 4294967292)))))
;;    :otf-flg t
;;    :hints (("Goal" :in-theory (e/d (bvplus sbvdivdown bvchop-of-sum-cases)
;; (anti-bvplus))))))




;; ;this links sbvrem and sbvdiv
;; (skip -proofs
;;  (defthmd sbvrem-and-sbvdiv
;;    (implies (and (unsigned-byte-p size x)
;;                  (unsigned-byte-p size y)
;;      ;(equal size 3)
;;                  (posp size)
;;                  (not (equal 0 y)) ;bozo
;;                  (integerp x)
;;                  (integerp y)
;;                  )
;;             (equal (bvchop size x) (bvplus size (sbvrem size x y) (bvmult size (sbvdiv size x y) y))))
;;    :otf-flg t
;;    :hints (("Goal" ;:in-theory (enable usb4-cases)
;;             :in-theory (e/d (bvchop-extend-by-1 sbvrem sbvdiv bvmult bvplus logext logapp mod
;;                                                  floor-of-sum
;;                                                  REM-BECOMES-MOD
;;                                                  ) (FLOOR-BOUNDED-BY-/
;;                                                  REM-BECOMES-MOD-better
;;                                                  BVCHOP-LEQ
;;                                                  BVLT-OF-PLUS-ARG2
;;                                                  BVLT-OF-PLUS-ARG1
;;                                                  MOD-=-0
;;                                                  SMALL-INT-HACK
;;                                                  FLOOR-MINUS-ARG1
;;                                                  BVPLUS-OF-*-ARG2 anti-bvplus
;;                                                  MOD-RECOLLAPSE-LEMMA2
;;                                                  MOD-RECOLLAPSE-LEMMA
;;                                                  |0-1-SPLIT-CHEAP|
;;                                                  IF-BACKCHAIN-RULE
;;                                                  USB-PLUS-FROM-BOUNDS
;;                                                  ))

;;             ))))

;; (skip -proofs
;;  (defthmd sbvrem-in-terms-of-sbvdiv
;;    (implies (and (unsigned-byte-p size x)
;;                  (unsigned-byte-p size y)
;;                  (posp size)
;;                  (not (equal 0 y)) ;bozo
;;                  (integerp x)
;;                  (integerp y)
;;                  )
;;             (equal (sbvrem size x y)
;;                    (bvminus size x (bvmult size (sbvdiv size x y) y))))
;;    :hints (("Goal" :use (:instance sbvrem-and-sbvdiv)))))


;gen version elsewhere?
(defthm unsigned-byte-p-when-bvlt-3-31
  (implies (not (bvlt 31 3 x))
           (equal (unsigned-byte-p 31 x)
                  (unsigned-byte-p 2 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvmod-32-4
  (implies (integerp x)
           (equal (BVMOD 32 x 4)
                  (bvchop 2 x)))
  :hints (("Goal" :in-theory (enable bvmod bvchop))))

(defthm bvlt-of-bvcat-31-2-30-trim
 (equal (BVLT 31 (BVCAT 2 x 30 y) z)
        (BVLT 31 (BVCAT 1 x 30 y) z))
 :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT <-BECOMES-BVLT-alt)))))

(defthm bvlt-of-slice-tighten-30-30-2
  (implies (unsigned-byte-p 29 x)
           (equal (BVLT 30 x (SLICE 30 2 GARG0))
                  (BVLT 29 x (SLICE 30 2 GARG0))))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT <-BECOMES-BVLT-alt)))))

(defthm bvlt-of-bvcat-1-1-30-k
  (equal (bvlt 31 (bvcat 1 1 30 x) 2147483644)
         (bvlt 30 x 1073741820)
         )
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-31-8-becomes-unsigned-byte-p
  (implies (UNSIGNED-BYTE-P 31 x)
           (equal (BVLT 31 x 8)
                  (unsigned-byte-p 3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))

;sometimes the definitions of bvle doesn't open during backchaining
(defthm bvle-to-bvlt
  (equal (bvle size x y)
         (not (bvlt size y x))))

(in-theory (disable bvle))

;; (BVLE '31 '20 GARG0)

;fixme use bvlt in rhs
(defthm bvlt-of-bvcat-1-1-30-k2
  (equal (BVLT 31 (BVCAT 1 1 30 x) 2147483643)
         (< (BVCHOP 30 X) 1073741819))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(in-theory (enable <-of-bvplus-becomes-bvlt-arg2)) ;todo drop

;(in-theory (disable ERIC-HACK-2001))

(defthm bvlt-k-bvcat-2-3-30
  (equal (BVLT 32 2147483648 (BVCAT 2 3 30 x))
         t)
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT <-BECOMES-BVLT-alt)))))

;; (defthm slice-of-minus-30-2
;;   (implies (integerp x)
;;            (equal (slice 30 2 (- x))
;;                   (if (equal (bvchop 2 x) 0)
;;                       (if (equal 0 (slice 30 2 x))
;;                           0
;;                         (+ (expt 2 29)
;;                            (- (slice 30 2 x))))
;;                     (bvchop 29 (+ 536870911 (- (slice 30 2 x)))) ;simplify?
;;                     )))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (slice bvplus bvchop-of-sum-cases) (anti-slice anti-bvplus bvlt-of-plus-arg1 bvlt-of-plus-arg2)))))

;; (defthm slice-of-bvuminus-28-2
;;   (implies (integerp x)
;;            (equal (slice '28 '2 (bvuminus 29 x))
;;                   xx))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvuminus bvminus slice-of-sum-cases) (bvminus-becomes-bvplus-of-bvuminus)))))


;; (thm
;;  (implies (integerp x)
;;           (equal (bvlt 32 (bvplus 32 2147483644 x) 2147483648)
;;                  (if (< (bvchop 32 x) 2147483652)
;;                      (bvlt 32 x 4)
;;                    yy)))
;;  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt
;;                                                         <-of-bvplus-becomes-bvlt-arg1
;;                                                         <-of-bvplus-becomes-bvlt-arg2)))))

(defthm equal-of-slice-when-equal-of-bvchop-30-2-5-4-16
  (implies (and (equal (bvchop 5 x) free)
                (syntaxp (quotep free))
                (equal 16 free)
                (integerp x))
           (equal (equal 4 (slice 30 2 x))
                  (equal 16 (slice 30 0 x))))
  :hints (("Goal" :in-theory (enable bvchop-contract-hack-gen))))



(defthm bvlt-of-bvcat-hack
  (equal (BVLT 32 (BVCAT 2 3 30 x) 4294967292)
         (bvlt 30 X 1073741820))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-hack-1
  (implies (and (equal size 31)
                (not (bvlt size free x))
                (bvle size free 15)
;               (unsigned-byte-p 15 size)
;              (unsigned-byte-p 16 size)
                (natp size)
                )
           (equal (bvlt size x 16)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (REWRITE-<-WHEN-SIZES-DONT-MATCH
                                   REWRITE-<-WHEN-SIZES-DONT-MATCH2
                                   <-becomes-bvlt <-becomes-bvlt-alt)))))

;non-dag
(defthm slice-trim
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< (+ 1 high) xsize)
                (natp high)
                (natp low)
                (integerp xsize))
           (equal (slice high low x)
                  (slice high low (trim (+ high 1) x))))
  :hints (("Goal" :in-theory (e/d (trim) ()))))

;; (defthm slice-of-bvplus-trim2
;;   (equal (SLICE 4 2 (BVPLUS 29 x y))
;;          (SLICE 4 2 (BVPLUS 5 x y)))
;;   :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

;non-dag
(defthm bvplus-trim-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

;non-dag
(defthm bvplus-trim-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvplus size y x)
                  (bvplus size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;gened somewhere?
(defthm bvplus-32-1-29-4-tighten
  (equal (BVPLUS 32 1 (BVPLUS 29 4 x))
         (BVPLUS 30 1 (BVPLUS 29 4 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(defthm unsigned-byte-p-when-bound
  (implies (and (not (bvlt 31 free garg0))
                (bvle 31 free 15))
           (equal (unsigned-byte-p 31 garg0)
                  (unsigned-byte-p 4 garg0)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt
                                                                         GETBIT-WHEN-BVLT-OF-SMALL-HELPER)))))

(defthm bvlt-of-bvuminus-hack
  (equal (BVLT 30 (BVUMINUS 2 x) 4)
         t)
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvplus-of-bvcat-hack
  (equal (BVPLUS 32 4 (BVCAT 2 3 30 x))
         (bvplus 32 3221225476 (bvchop 30 x)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))

(defthm bvplus-of-bvcat-hack2
  (equal (BVPLUS 32 5 (BVCAT 2 3 30 x))
         (bvplus 32 3221225477 (bvchop 30 x)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))


(defthm bvlt-of-bvplus-hack
  (equal (BVLT 31 (BVPLUS 30 x y) 1073741820)
         (BVLT 30 (BVPLUS 30 x y) 1073741820))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvplus-32-30-hack
  (implies (and (< x 4)
                (natp x))
           (equal (BVPLUS 32 3221225476 (BVPLUS 30 1073741820 x))
                  (bvplus 32 (+ 3221225476 1073741820) (bvchop 30 x))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))

(defthm bvplus-32-30-hack2
  (implies (and (< x 4)
                (natp x))
           (equal (BVPLUS 32 3221225477 (BVPLUS 30 1073741820 x))
                  (bvplus 32 (+ 3221225477 1073741820) (bvchop 30 x))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))

(defthm bvplus-of-bvcat-hack4
  (equal (BVPLUS 32 19 (BVCAT 2 3 30 x))
         (bvplus 32 (+ 19 (* 3 (expt 2 30))) (bvchop 30 x)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))

(defthm bvplus-of-bvcat-hack5
  (equal (BVPLUS 32 16 (BVCAT 2 3 30 x))
         (bvplus 32 (+ 16 (* 3 (expt 2 30))) (bvchop 30 x)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))

(defthm bvplus-of-bvcat-hack6
  (equal (BVPLUS 32 18 (BVCAT 2 3 30 x))
         (bvplus 32 (+ 18 (* 3 (expt 2 30))) (bvchop 30 x)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus BVPLUS-OF-PLUS)))))

(defthm bvplus-of-bvuminus-tighten
  (implies (and (unsigned-byte-p 4 x)
                (integerp jj)
                (integerp k))
           (equal (bvplus 32 k (bvuminus 30 x))
                  (if (equal 0 (bvchop 30 x))
                      (bvchop 32 k)
                    (bvplus 32 (+ k 1073741808) (bvuminus 4 x)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvchop-of-minus bvplus) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus)))))

(defthm bvplus-of-bvuminus-when-bvchop
  (implies (and (equal (bvchop 2 x) 0)
                (integerp x))
           (equal (bvplus 32 k (bvuminus 4 x))
                  (bvplus 32 k (bvmult 32 4 (bvuminus 2 (slice 3 2 x))))))
  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 2) (ls 2)))
           :in-theory (e/d (bvmult bvuminus bvminus bvchop-of-minus bvplus bvcat logapp)
                           (bvchop-of-* anti-bvplus bvminus-becomes-bvplus-of-bvuminus)))))

;usb shift rule?

(defthm *-of-bvuminus-hack
  (equal (* 4 (BVUMINUS 2 x))
         (bvmult 4 4 (BVUMINUS 2 x)))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthm <-of-bvmult-16
  (equal (< (BVMULT '4 x y) '16)
         (bvlt 5 (bvmult 4 x y) 16))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt BVLT-WHEN-BOUND)))))

(defthm bvlt-of-bvmult-hack
  (equal (bvlt 5 (bvmult 4 4 x) 16)
         (bvlt 3 (bvchop 2 x) 4))
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (bvchop-of-*
                                                                 <-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-when-usb-hack
  (implies (unsigned-byte-p 2 x)
           (equal (BVLT '3 x '4)
                  t))
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (bvchop-of-* <-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm <-of-bvmult-hack
  (implies (and (unsigned-byte-p 32 z)
                (unsigned-byte-p 32 x))
           (equal (< (bvmult 4 x y) z)
                  (bvlt 32 (bvmult 4 x y) z)))
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (bvchop-of-* <-becomes-bvlt <-becomes-bvlt-alt bvchop-of-*)))))

(defthm bvlt-of-bvmult
  (BVLT '31 (BVMULT '4 x y) '16)
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (bvchop-of-* <-becomes-bvlt <-becomes-bvlt-alt bvchop-of-*)))))

(defthm bvuminus-bound
  (<= (BVUMINUS 2 X) 3)
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus ;bozo
                                            ) ( BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm bvlt-of-bvmult-of-bvminus-hack
  (BVLT '31 (BVMULT '4 '4 (BVUMINUS '2 x)) '14)
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt
                                                                                *-OF-BVUMINUS-HACK ;looped
                                                                                bvchop-of-*
                                                                                )))))

(defthm bvlt-of-bvmult-of-bvminus-hack2
  (BVLT '31 (BVMULT '4 '4 (BVUMINUS '2 x)) '15)
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt
                                                                                *-OF-BVUMINUS-HACK ;looped
                                                                                bvchop-of-*
                                                                                )))))

(defthm bvlt-of-bvmult-of-bvminus-hack3
  (equal (BVLT '31 (BVMULT '4 '4 (BVUMINUS '2 x)) '13)
         t)
  :hints (("Goal" :in-theory (e/d (bvmult bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt
                                                                                *-OF-BVUMINUS-HACK ;looped
                                                                                bvchop-of-*
                                                                                )))))

;gen the 1
(defthm equal-of-plus-one-and-bvplus-one
 (implies (natp x)
          (equal (EQUAL (+ 1 x) (BVPLUS 5 1 x))
                 (< x 31)))
 :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(defthm bvlt-when-usb-hack100
  (implies (unsigned-byte-p 4 x)
           (equal (BVLT 31 3 x)
                  (bvlt 4 3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm UNSIGNED-BYTE-P-when-bvlt-4-2
  (implies (NOT (BVLT 4 3 GARG0))
           (equal (UNSIGNED-BYTE-P 4 GARG0)
                  (UNSIGNED-BYTE-P 2 GARG0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-of-slice-hack
  (equal (BVLT 4 5 (SLICE 3 2 GARG0))
         nil)
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p slice-bound-lemma-gen2
                                        slice-bound-lemma-gen)
                                  (<-becomes-bvlt <-becomes-bvlt-alt)))))




(defthm bvlt-when-bvlt-hack
  (implies (BVLT 4 3 GARG0)
           (equal (BVLT '4 GARG0 '4)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-hack77
  (equal (BVLT '30 (BVPLUS '29 x y) '1073741822)
         t)
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-hack78
  (equal (BVLT '30 '2 (BVPLUS '29 x y))
         (BVLT 29 '2 (BVPLUS '29 x y)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-of-bvplus-hack200
  (implies (and (integerp x)
                (integerp y))
           (equal (bvlt 30 (bvplus 29 x y) k)
                  (if (bvle 30 (expt 2 29) k)
                      t
                    (bvlt 29 (bvplus 29 x y) k))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus
                                        bvchop-when-top-bit-1
                                        rewrite-<-when-sizes-dont-match
                                        rewrite-<-when-sizes-dont-match2)
                                  (anti-bvplus
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2)))))

(defthm bvlt-of-bvplus-hack300
  (equal (BVLT 29 w (BVPLUS 30 x y))
         (BVLT 29 w (BVPLUS 29 x y)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(DEFTHM bvuminus-IMPOSSIBLE-VALUE
  (IMPLIES (AND (SYNTAXP (QUOTEP K))
                (NOT (UNSIGNED-BYTE-P SIZE K))
                (NATP SIZE))
           (EQUAL (EQUAL K (bvuminus SIZE X)) NIL)))

(defthm bvplus-32-1-bvumiuns
  (equal (BVPLUS 32 1 (BVUMINUS 2 x))
         (bvplus 3 1 (BVUMINUS 2 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(defthm plus-32-1-bvumiuns
  (equal (+ 1 (BVUMINUS 2 x))
         (bvplus 3 1 (BVUMINUS 2 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

(defthm bvplus-30-1-29-4
  (implies (integerp x)
           (equal (bvplus 30 1 (bvplus 29 4 x))
                  (if (bvlt 29 -5 x)
                      (bvplus 30 (+ (expt 2 29) 5) (bvchop 29 x))
                    (bvplus 30 5 (bvchop 29 x)))))
  :hints (("Goal" :in-theory (e/d (bvchop-when-top-bit-1 bvlt bvplus bvchop-of-sum-cases)
                                  (anti-bvplus <-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvplus-30-2-29-3
  (implies (integerp x)
           (equal (bvplus 30 2 (bvplus 29 3 x))
                  (if (bvlt 29 -4 x)
                      (bvplus 30 (+ (expt 2 29) 5) (bvchop 29 x))
                    (bvplus 30 5 (bvchop 29 x)))))
  :hints (("Goal" :in-theory (e/d (bvchop-when-top-bit-1 bvlt bvplus bvchop-of-sum-cases)
                                  (anti-bvplus <-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvplus-of-bvuminus-hack10000
  (implies (integerp k)
           (equal (bvplus 30 k (bvuminus 29 (slice 3 2 garg0)))
                  (if (equal 0 (slice 3 2 garg0))
                      (bvchop 30 k)
                    (bvplus 30 (bvplus 30 536870908 k) (bvuminus 2 (slice 3 2 garg0))))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvchop-of-minus bvplus bvcat logapp) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus)))))

;;536870917

(defthm usb-when-bvlt-hack
  (implies (BVLT 4 FARG0 4)
           (equal (UNSIGNED-BYTE-P 4 FARG0)
                  (UNSIGNED-BYTE-P 2 FARG0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvlt-of-plus-hack
  (implies (integerp x)
           (equal (BVLT 31 4 (+ 1 x))
                  (if (EQUAL 2147483647 (BVCHOP 31 X))
                      nil
                    (bvlt 31 3 x))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvchop-31-equal-0-extend)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1
                                                  REWRITE-<-WHEN-SIZES-DONT-MATCH2)))))

;; (defthm bvplus-tighten-hack-700
;;   (implies (unsigned-byte-p 4 x)
;;            (equal (bvplus 32 3 x)
;;                   (bvplus 5 3 x)))
;;   :hints (("Goal" :in-theory (e/d ( bvplus) (anti-bvplus)))))

(defthm bvplus-tighten-non-dag
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (< (+ 1 (max xsize ysize)) size)
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                (natp size)
                (posp xsize))
           (equal (bvplus size x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal"
           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                           (r 2)
                           (i (min xsize ysize))
                           (j (max xsize ysize)))
           :in-theory (e/d (bvplus unsigned-byte-p) (EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                                                     EQUAL-OF-BVCHOP-AND-BVCHOP-SAME
                                                      <-of-expt-and-expt
                                                      anti-bvplus)))))


;fixme lhses not tight!
(defthm bvlt-of-bvmult-hack2
  (implies (bvle 5 (bvchop 4 x) 3)
           (bvlt 5 (bvmult 4 4 x) 13))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvmult)
                                  (bvchop-of-*
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-bvmult-hack3
  (implies (bvle 5 (bvchop 4 x) 3)
           (bvlt 5 (bvmult 4 4 x) 15))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvmult)
                                  (bvchop-of-*
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-bvmult-hack4
  (implies (bvle 5 (bvchop 4 x) 3)
           (bvlt 5 (bvmult 4 4 x) 14))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvmult)
                                  (bvchop-of-*
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(theory-invariant (incompatible (:definition bvplus ) (:rewrite PLUS-BECOMES-BVPLUS)))

(defthm bvplus-of-bvuminus-hack10000b
  (implies (integerp k)
           (equal (bvplus 29 k (bvuminus 29 (slice 3 2 garg0)))
                  (if (equal 0 (slice 3 2 garg0))
                      (bvchop 29 k)
                    (bvplus 29 (bvplus 29 536870908 k) (bvuminus 2 (slice 3 2 garg0))))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvchop-of-minus bvplus bvcat logapp) (anti-bvplus bvminus-becomes-bvplus-of-bvuminus PLUS-BECOMES-BVPLUS)))))

;-alt?
(defthm bvlt-tighten-non-dag
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (< (max xsize ysize) size)
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                (natp size)
                (posp xsize))
           (equal (bvlt size x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                           (r 2)
                           (i (min xsize ysize))
                           (j (max xsize ysize)))
           :in-theory (e/d (bvlt unsigned-byte-p) (EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                                                   <-of-expt-and-expt
                                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                   <-of-bvmult-hack ;bozo
                                                   <-of-bvplus-becomes-bvlt-arg1
                                                   <-of-bvplus-becomes-bvlt-arg2)))))

;non-dag
(defthm bvlt-trim-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :in-theory (e/d (bvlt trim) (<-becomes-bvlt <-becomes-bvlt-alt
                                                         <-of-bvmult-hack ;bozo
                                                         <-of-bvplus-becomes-bvlt-arg1
                                                         <-of-bvplus-becomes-bvlt-arg2)))))

;non-dag
(defthm bvlt-trim-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvlt size y x)
                  (bvlt size y (trim size x))))
  :hints (("Goal" :in-theory (e/d (bvlt trim) (<-becomes-bvlt <-becomes-bvlt-alt
                                                         <-of-bvmult-hack ;bozo
                                                         <-of-bvplus-becomes-bvlt-arg1
                                                         <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-constant-tighten-when-usb-arg1
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (unsigned-byte-p free x)
                (< free size)
                (natp k)
                (natp size)
                (natp free)
                (unsigned-byte-p size k) ;drop?
                )
           (equal (bvlt size k x)
                  (if (unsigned-byte-p free (bvchop size k))
                      (bvlt free k x)
                    nil)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   ) (<-becomes-bvlt <-becomes-bvlt-alt
                                                     ;;bvchop-identity
                                   )))))

(defthm bvlt-of-constant-tighten-when-usb-arg2
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (unsigned-byte-p free x)
                (< free size)
                (natp k)
                (natp size)
                (natp free)
                (unsigned-byte-p size k) ;drop?
                )
           (equal (bvlt size x k)
                  (if (unsigned-byte-p free k)
                      (bvlt free x k)
                    t)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p
                                   ) (<-becomes-bvlt <-becomes-bvlt-alt
                                                     ;;bvchop-identity
                                   )))))

;gen!
(defthm bvlt-of-bvmult-hack4-b
  (implies (bvle 4 x 3)
           (bvlt 4 (bvmult 4 4 x) 14))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvmult)
                                  (bvchop-of-*
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-bvmult-hack2-b
  (implies (bvle 4 x 3)
           (bvlt 4 (bvmult 4 4 x) 13))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvmult)
                                  (bvchop-of-*
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-bvmult-hack3-b
  (implies (bvle 4 x 3)
           (bvlt 4 (bvmult 4 4 x) 15))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvmult)
                                  (bvchop-of-*
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-tighten-non-dag-strong-arg3
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< xsize size)
                (natp size)
                (posp xsize)
                (natp y)
                (unsigned-byte-p size y) ;drop?
                (force (unsigned-byte-p-forced xsize x))
                )
           (equal (bvlt size y x)
                  (if (unsigned-byte-p xsize (bvchop size y))
                      (bvlt xsize y x)
                    nil)))  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                    (<-becomes-bvlt <-becomes-bvlt-alt
                                    <-of-bvmult-hack ;bozo
                                    <-of-bvplus-becomes-bvlt-arg1
                                    <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-tighten-non-dag-strong-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< xsize size)
                (natp size)
                (posp xsize)
                (natp y)
                (unsigned-byte-p size y) ;drop?
                (force (unsigned-byte-p-forced xsize x))
                )
           (equal (bvlt size x y)
                  (if (unsigned-byte-p xsize (bvchop size y))
                      (bvlt xsize x y)
                    t)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                    (<-becomes-bvlt <-becomes-bvlt-alt
                                    <-of-bvmult-hack ;bozo
                                    <-of-bvplus-becomes-bvlt-arg1
                                    <-of-bvplus-becomes-bvlt-arg2)))))


;gen
(defthm bvlt-when-usb
  (implies (and (unsigned-byte-p free x)
                (<= free 4)
                (natp free))
           (equal (bvlt 4 15 x)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-of-bvuminus-tighten-gen
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< xsize n) ;this means the bvuminus is not tight
                (<= n size)
                (natp n)
                (force (unsigned-byte-p-forced xsize x)))
           (equal (bvplus size k (bvuminus n x))
                  (if (equal 0 x)
                      (bvchop size k)
                    (bvplus size (bvplus size (- (expt 2 n) (expt 2 xsize)) k) (bvuminus xsize x)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvchop-of-minus bvplus bvcat logapp
                                            bvchop-when-i-is-not-an-integer)
                                  (anti-bvplus bvminus-becomes-bvplus-of-bvuminus PLUS-BECOMES-BVPLUS)))))

(defthm bvplus-of-bvuminus-when-bvchop-gen
  (implies (and (equal (bvchop 2 x) 0)
                (integerp x)
                (<= 5 size) ;allow 4 - maybe not?
                (integerp size)
                )
           (equal (bvplus size k (bvuminus 4 x))
                  (bvplus size k (bvmult size 4 (bvuminus 2 (slice 3 2 x))))))
  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 2) (ls 2)))
           :in-theory (e/d (bvmult bvuminus bvminus bvchop-of-minus bvplus bvcat logapp unsigned-byte-p-of-integer-length-gen)
                           (bvchop-of-* anti-bvplus bvminus-becomes-bvplus-of-bvuminus  PLUS-BECOMES-BVPLUS
                                         unsigned-byte-p-of-+-of-minus-alt
                                         unsigned-byte-p-of-+-of-minus)))))

;open a bvcat of a constant to a plus in a plus context
;kill special cases above
(defthm bvplus-of-bvcat-hack6-gen
  (implies (and (syntaxp (and (quotep k)
                              (quotep highval)
                              (quotep highsize)
                              (quotep lowsize)))
                (<= (+ lowsize highsize) size)
                (natp lowsize)
                (natp highsize)
                (integerp k)
                )
           (equal (bvplus size k (bvcat highsize highval lowsize lowval))
                  (bvplus size (+ k (* (bvchop highsize highval) (expt 2 lowsize))) (bvchop lowsize lowval))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus) (anti-bvplus  bvplus-of-plus plus-becomes-bvplus
                                                                     BVLT-OF-PLUS-ARG1
                                                                     BVLT-OF-PLUS-ARG2)))))

(defthm bvplus-of-bvplus-constants-size-differs
  (implies (and (< size bigsize) ;or else we don't need the ruls
                (bvlt size x (bvuminus size j)) ;other case?
                (integerp k)
                (natp size)
                (natp bigsize)
                (integerp j)
                (natp x))
           (equal (bvplus bigsize k (bvplus size j x))
                  (bvplus bigsize (+ k (bvchop size j)) (bvchop size x))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvplus bvchop-of-sum-cases
                                         bvlt
                                         bvuminus
                                         bvminus
                                         )
                                  (anti-bvplus  bvplus-of-plus
                                               BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                               <-becomes-bvlt <-becomes-bvlt-alt
                                               <-of-bvmult-hack ;bozo
                                               <-of-bvplus-becomes-bvlt-arg1
                                               <-of-bvplus-becomes-bvlt-arg2
                                               plus-becomes-bvplus BVCHOP-UPPER-BOUND ;speed
                                               )))))

;gen the 1!
;arg1 version?
;this may not fire since it has + in the lhs
(defthm bvlt-of-plus-1-arg2
  (implies (and (syntaxp (not (quotep x))) ;defeats ACL's overagressive matching
                (integerp x)
                (integerp k)
                (posp size)
                )
           (equal (bvlt size k (+ 1 x))
                  (if (equal (bvchop size x) (+ -1 (expt 2 size)))
                      nil
                    (if (equal (bvchop size k) 0)
                        t
                      (bvlt size (bvplus size -1 k) x)))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvchop-of-sum-cases bvplus)
                                  (BVCHOP-CHOP-LEADING-CONSTANT ;fixme
                                   plus-becomes-bvplus
                                   BVPLUS-OF-PLUS
                                   BVPLUS-OF-PLUS2
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   <-of-bvmult-hack ;bozo
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2)))))


(local (in-theory (disable BVCHOP-PLUS-1-SPLIT)))

(defthm usb-when-bvlt-hack-gen
  (implies (and (bvlt size x free)
                (syntaxp (quotep free))
                (bvle size free 4)
                (<= 2 size)
                (natp size))
           (equal (unsigned-byte-p size x)
                  (unsigned-byte-p 2 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

;this caused problems, including a loop in DISJOIN-CLAUSE-SEGMENT-TO-CLAUSE-SET, which didn't make any sense to me..
(defthmd unsigned-byte-p-when-unsigned-byte-p-bigger
  (implies (and (unsigned-byte-p free x)
                (< size free)
                (natp size)
                (natp free))
           (equal (unsigned-byte-p size x)
                  (bvlt free x (expt 2 size))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))



(in-theory (disable BVLT-BY-4)) ;did we need this? which we we prefer bounds or usb claims?

;; ;this doesn't fire, perhaps because it is hung on not..
;; (defthm not-bvlt-when-not-usb
;;   (implies (and (not (unsigned-byte-p 4 x))
;;                 (unsigned-byte-p 5 x) ;drop?
;;                 (natp x))
;;            (equal (not (bvlt 5 16 x))
;;                   (equal 16 (bvchop 5 x))))
;;   :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

;(include-book "kestrel/utilities/polarity" :dir :system)

;i want to do this when (not (bvlt 5 16 x)) is a hyp..
(defthm not-bvlt-when-not-usb-polarity
  (implies (and (syntaxp (want-to-weaken (bvlt 5 16 x)))
                (not (unsigned-byte-p 4 x))
                (unsigned-byte-p 5 x) ;drop?
                (natp x))
           (equal (bvlt 5 16 x)
                  (not (equal 16 (bvchop 5 x)))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvmult-of-4-gen
  (implies (natp size)
           (equal (bvmult size 4 x)
                  (bvcat (- size 2) x 2 0)))
  :hints (("Goal" :in-theory (e/d (bvchop-when-i-is-not-an-integer
                                   bvmult bvcat logapp)
                                  (bvchop-of-*
                                   logapp-equal-rewrite
                                   bvcat-equal-rewrite-alt bvcat-equal-rewrite
                                   )))))

(in-theory (disable BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES)) ;move up -will this break anything?

(defthm bvlt-of-max-arg2
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))))
           (equal (bvlt size k x)
                  nil))
  :hints (("Goal" :cases ((natp size))
           :in-theory (e/d (bvlt unsigned-byte-p)
                           (bvchop-chop-leading-constant
                            <-becomes-bvlt <-becomes-bvlt-alt)))))

;non-dag
(defthm getbit-trim
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< (+ 1 n) xsize)
                (natp n)
                (integerp xsize))
           (equal (getbit n x)
                  (getbit n (trim (+ 1 n) x))))
  :hints (("Goal" :in-theory (e/d ( trim) ()))))

(defthm bvplus-of-1-and-1
  (equal (bvplus 1 1 x)
         (bitnot x))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm getbit-of-bvuminus
  (implies (and (< low size)
                (integerp x)
                (integerp size)
                (natp low))
           (equal (getbit low (bvuminus size x))
                  (if (equal (bvchop low x) 0)
                      (getbit low x)
                    (bitnot (getbit low x)))))
  :hints (("Goal" :use (:instance slice-of-bvuminus (high low))
           :in-theory (disable slice-of-bvuminus))))



;could also do it for the bottom bit..
(defthm bvlt-of-slice-when-top-bit-known
  (implies (and (syntaxp (quotep k))
                (equal free (getbit high x))
                (syntaxp (quotep free))
                (equal (+ 1 (- high low)) size)
                (natp high)
                (natp low)
                (<= low high))
           (equal (bvlt size k (slice high low x))
                  (bvlt size
                        k
                        (bvplus size
                                (* free (expt 2 (- high low))) ;fixme what if low or high is not a quote?
                                (slice (+ -1 high) low x)))))
  :hints (("Goal"
           :cases ((equal 0 (GETBIT 0 K)) (equal 1 (GETBIT 0 K)))
           :use (:instance split-with-bvcat (x (slice high low x)) (hs 1) (ls (+ -1 size)))
           :in-theory (e/d (bvlt unsigned-byte-p bvcat logapp bvplus posp)
                           (
                            anti-bvplus
                            PLUS-BECOMES-BVPLUS
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2)))))

(defthm getbit-impossible-value
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 1 k)))
           (equal (equal k (getbit n x)) nil)))

(defthm slice-tighten-when-top-bit-0
  (implies (and (equal 0 (getbit high x))
                (natp high)
                (< low high)
                (natp low))
           (equal (slice high low x)
                  (slice (+ -1 high) low x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil)))
  :hints (("Goal" :use (:instance split-with-bvcat (x (slice high low x)) (hs 1) (ls (+ high (- low))))
           :in-theory (e/d (bvcat logapp posp) ( split-with-bvcat ))
           )))

;maybe the trim rules should use force-unsigned-byte-p

;reiterting last to have this fire first
(defthm unsigned-byte-p-of-bvchop2
  (implies (<= size size1)
           (equal (unsigned-byte-p size1 (bvchop size i))
                  (and (>= size1 0) (integerp size1)))))

(in-theory (disable unsigned-byte-p-of-bvchop)) ;

(DEFTHMd BVPLUS-OF-BVPLUS-CONSTANTS-SIZE-DIFFERS-BETTER-helper
  (IMPLIES
   (AND (SYNTAXP (AND (QUOTEP K)
                      (QUOTEP J)
                      (QUOTEP SIZE)))
        (< SIZE BIGSIZE)
        (INTEGERP K)
        (NATP SIZE)
        (NATP BIGSIZE)
        (INTEGERP J)
        (NATP X))
   (EQUAL
    (BVPLUS BIGSIZE K (BVPLUS SIZE J X))
    (IF (BVLT SIZE X (BVUMINUS SIZE J))
        (BVPLUS BIGSIZE (+ K (BVCHOP SIZE J))
                (BVCHOP SIZE X))
        (IF (EQUAL 0 (BVCHOP SIZE J))
            (BVPLUS BIGSIZE K (BVCHOP SIZE X))
            (BVPLUS BIGSIZE
                    (+ K (- (EXPT 2 SIZE)) (BVCHOP SIZE J))
                    (BVCHOP SIZE X))))))
  :HINTS
  (("Goal" :IN-THEORY
    (E/D (BVCAT LOGAPP BVPLUS BVCHOP-OF-SUM-CASES
                BVLT BVUMINUS BVMINUS)
         (ANTI-BVPLUS  BVPLUS-OF-PLUS
                      BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                      <-BECOMES-BVLT
                      <-BECOMES-BVLT-ALT <-OF-BVMULT-HACK
                      <-OF-BVPLUS-BECOMES-BVLT-ARG1
                      <-OF-BVPLUS-BECOMES-BVLT-ARG2
                      PLUS-BECOMES-BVPLUS
                      BVCHOP-UPPER-BOUND)))))

;the quoteps are new - no longer introduces + and -
(defthm bvplus-of-bvplus-constants-size-differs-better
  (implies (and (syntaxp (and (quotep k) (quotep j) (quotep size)))
                (< size bigsize) ;or else we don't need this rule
                (integerp k)
                (natp size)
                (natp bigsize)
                (integerp j)
                (natp x))
           (equal (bvplus bigsize k (bvplus size j x))
                  (if (bvlt size x (bvuminus size j))
                      (bvplus bigsize (bvplus bigsize k (bvchop size j)) (bvchop size x))
                    (if (equal 0 (bvchop size j))
                        (bvplus bigsize k (bvchop size x))
                      (bvplus bigsize
                              (bvplus bigsize k
                                      (bvplus bigsize
                                              (bvuminus bigsize (expt 2 size))
                                              (bvchop size j)))
                              (bvchop size x))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvuminus bvminus)
                                  (anti-bvplus BVPLUS-OF-BVPLUS-CONSTANTS-SIZE-DIFFERS PLUS-BECOMES-BVPLUS
                                               BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS))
           :use (:instance BVPLUS-OF-BVPLUS-CONSTANTS-SIZE-DIFFERS-BETTER-helper))))

(in-theory (disable bvplus-of-bvplus-constants-size-differs))

;gen!
(defthm bvlt-5-16-+-4
  (implies (integerp x)
           (equal (bvlt '5 '16 (binary-+ '-4 x))
                  (if (<= 4 (BVCHOP 5 X))
                      (bvlt 5 20 x)
                    t)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvchop-of-sum-cases bvplus)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  plus-becomes-bvplus
                                                  anti-bvplus
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

;gen!
(defthm bvlt-of-4
  (implies (syntaxp (symbolp x)) ;yuck
           (equal (BVLT 3 x '4)
                  (equal (getbit 2 x) 0)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (x x) (hs 1) (ls 2))
           :in-theory (e/d (bvlt unsigned-byte-p bvchop-of-sum-cases bvplus bvcat logapp)
                           (<-becomes-bvlt <-becomes-bvlt-alt

                                           plus-becomes-bvplus
                                           anti-bvplus
                                           <-of-bvmult-hack ;bozo
                                           <-of-bvplus-becomes-bvlt-arg1
                                           <-of-bvplus-becomes-bvlt-arg2)))))


(in-theory (enable BVLT-OF-PLUS-ARG2 BVLT-OF-PLUS-ARG1)) ;now drop bvlt-5-16-+-4?


(in-theory (enable SBVDIV-WHEN-BOTH-POSITIVE))

;need to put on a type hypothesis!
;and also prove without splitting into cases!


(in-theory (disable BVCHOP-31-EQUAL-0-EXTEND)) ;looped

(in-theory (enable <-BECOMES-BVLT
                   <-BECOMES-BVLT-ALT))


(in-theory (disable BOUND-FROM-NATP-FACT
                    ;;nth-times
                    ))

(defthm unsigned-byte-p-when-top-bit-0-polarity
  (implies (and (syntaxp (want-to-strengthen (unsigned-byte-p n x)))
                (equal 0 (getbit (+ -1 n) x))
                (integerp n)
                (< 1 n))
           (equal (unsigned-byte-p n x)
                  (unsigned-byte-p (+ -1 n) x)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil nil)))
  :hints (("Goal"
           :in-theory (disable BVCHOP-CONTRACT-HACK-GEN)
           :use (:instance split-with-bvcat (x (bvchop n x)) (hs 1) (ls (+ -1 n)))))
)

(defthm getbit-of-minus-expt
  (implies (and (< size size2)
                (natp size)
                (natp size2))
           (equal (GETBIT SIZE (- (EXPT 2 SIZE2)))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

(defthm equal-bitnot
  (equal (equal x (bitnot x))
         nil)
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm slice-of-+
  (implies (and(natp high)
               (natp low)
               (integerp x)
               (integerp y))
           (equal (SLICE high low (+ x y))
                  (slice high low (bvplus (+ 1 high) x y))))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus
                                            BVLT-OF-PLUS-ARG1
                                            PLUS-BECOMES-BVPLUS
                                            BVLT-OF-PLUS-ARG2
                                            )))))
(defthm bvlt-slice-bound-hack
  (implies (NOT (BVLT 5 16 x))
           (NOT (BVLT 3 4 (SLICE 4 2 x))))
  :hints (("Goal" :in-theory (e/d (bvlt slice-bound-lemma-gen slice-bound-lemma-gen2)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm getbit-of-+
  (implies (and (natp n)
                (integerp x)
                (integerp y))
           (equal (getbit n (+ x y))
                  (getbit n (bvplus (+ 1 n) x y))))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus PLUS-BECOMES-BVPLUS
                                                        BVLT-OF-PLUS-ARG1
                                                        BVLT-OF-PLUS-ARG2)))))

(theory-invariant (incompatible (:rewrite getbit-of-+) (:definition bvplus)))

(defthmd sbvlt-of-+-arg1
  (implies (and (posp n)
                (integerp x)
                (integerp y))
           (equal (sbvlt n (+ x y) z)
                  (sbvlt n (bvplus n x y) z)))
  :hints (("Goal" :in-theory (e/d (sbvlt bvplus) (anti-bvplus PLUS-BECOMES-BVPLUS
                                                              GETBIT-OF-+
                                                              BVLT-OF-PLUS-ARG1
                                                              BVLT-OF-PLUS-ARG2)))))


(defthmd sbvlt-of-+-arg2
  (implies (and (posp n)
                (integerp x)
                (integerp y))
           (equal (sbvlt n z (+ x y))
                  (sbvlt n z (bvplus n x y))))
  :hints (("Goal" :in-theory (e/d (sbvlt bvplus) (anti-bvplus PLUS-BECOMES-BVPLUS
                                                              GETBIT-OF-+
                                                              BVLT-OF-PLUS-ARG1
                                                              BVLT-OF-PLUS-ARG2)))))

;; ;drop?
;; (defthmd sbvle-of-+-arg1
;;   (implies (and (posp n)
;;                 (integerp x)
;;                 (integerp y))
;;            (equal (sbvle n (+ x y) z)
;;                   (sbvle n (bvplus n x y) z)))
;;   :hints (("Goal" :in-theory (e/d (sbvle) (anti-bvplus PLUS-BECOMES-BVPLUS
;;                                                        GETBIT-OF-+
;;                                                        BVLT-OF-PLUS-ARG1
;;                                                        BVLT-OF-PLUS-ARG2)))))

;; ;drop?
;; (defthmd sbvle-of-+-arg2
;;   (implies (and (posp n)
;;                 (integerp x)
;;                 (integerp y))
;;            (equal (sbvle n z (+ x y))
;;                   (sbvle n z (bvplus n x y))))
;;   :hints (("Goal" :in-theory (e/d (sbvle) (anti-bvplus PLUS-BECOMES-BVPLUS
;;                                                        BVLT-OF-PLUS-ARG1
;;                                                        BVLT-OF-PLUS-ARG2)))))

;see the -of-plus version
(defthm bvuminus-of-+
  (implies (and (natp n)
                (integerp x)
                (integerp y))
           (equal (bvuminus n (+ x y))
                  (bvuminus n (bvplus n x y))))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus PLUS-BECOMES-BVPLUS
                                                        GETBIT-OF-+
                                                        BVLT-OF-PLUS-ARG1
                                                        BVLT-OF-PLUS-ARG2)))))

(defthm bvlt-of-bvcat-hack-99
  (equal (bvlt 4 (bvcat 2 x 2 0) 12)
         (bvlt 2 x 3))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm unsigned-byte-p-false-when-high-bit-1
  (implies (and (equal 1 (getbit free x))
                (<= n free)
                (natp n)
                (integerp free))
           (equal (unsigned-byte-p n x)
                  nil)))

;todo
(include-book "rules2") ;drop (but that breaks SBVDIV-OF-SUBTRACT-4-BY-MINUS-4 below)? need BVCHOP-OF-SBP-EQUAL-CONSTANT

(defthm bvuminus-when-top-bit-known
  (implies (and (equal 1 (getbit high x))
                (equal size (+ high 1 (- low)))
                (natp low)
                (< low high)
                (natp high))
           (equal (bvuminus size (slice high low x))
                  (bvuminus size (bvplus size (expt 2 (+ -1 size)) (slice (+ -1 high) low x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil nil)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (x (slice high low x)) (hs 1) (ls (+ -1 size)))
           :in-theory (e/d (bvminus bvuminus bvcat logapp bvplus) (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus

                                                                               bvlt-of-plus-arg1
                                                                               bvminus-becomes-bvplus-of-bvuminus
                                                                               bvlt-of-plus-arg2
                                                                               )))) )

(defthm equal-of-bvchop-extend
  (implies (and (syntaxp (quotep k))
                (syntaxp (want-to-strengthen (equal k (bvchop size x))))
                (equal free (getbit size x)) ;this is treated as a binding hyp by acl2? (TODO: Would just using a backchaim limit of 0 suffice?)
                ;; try to ensure the equality really appears in the clause
                ;; (without this, I've seen this rule loop by repeatedly
                ;; extending the size of the bvchop):
                (syntaxp (or (want-to-strengthen (equal free (getbit size x)))
                             (want-to-strengthen (equal (getbit size x) free))))
                (syntaxp (quotep free))
                (natp size)
                (unsigned-byte-p size k)
                )
           (equal (equal k (bvchop size x))
                  (equal (bvcat 1 free size k) (bvchop (+ 1 size) x)))))

(in-theory (disable BVCHOP-EQUAL-CONSTANT-REDUCE-WHEN-TOP-BIT-3-2-4)) ;if it's a hyp we don't want to reduce it..

;add -dag to name
(in-theory (disable BV-ARRAY-WRITE-WHEN-DATA-ISNT-AN-ALL-UNSIGNED-BYTE-P BV-ARRAY-READ-WHEN-DATA-ISNT-AN-ALL-UNSIGNED-BYTE-P))

(in-theory (disable NTH-WHEN-all-equal$))

;sometimes we don't want these, e.g. (equal 0 (bvchop 2 x)) when we also know (equal 0 (getbit 1 x))
(in-theory (disable BVCHOP-CONTRACT-HACK-GEN SLICE-TIGHTEN-WHEN-TOP-BIT-0))

(in-theory (disable UNSIGNED-BYTE-P-OF-INTEGER-LENGTH-GEN))

(in-theory (disable bvlt-tighten-non-dag-strong-arg3 bvlt-tighten-non-dag-strong-arg2)) ;do these cause the cases?

(defthm unsigned-byte-p-when-bound-tighten-hack
  (implies (NOT (BVLT 6 16 GARG0))
           (equal (UNSIGNED-BYTE-P 6 GARG0)
                  (UNSIGNED-BYTE-P 5 GARG0)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-tighten-when-not-usb
  (implies (and (NOT (UNSIGNED-BYTE-P 3 GARG0))
                (unsigned-byte-p 5 garg0))
           (equal (BVLT 5 3 GARG0)
                  (BVLT 5 7 GARG0)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

;what other rules are missing?
(defthm bvlt-false-when-bvlt
  (implies (and (bvlt size free x)
                (bvle size k free))
           (equal (bvlt size x k)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-4-tighten-29
  (implies (and (unsigned-byte-p 3 x) ;use bind-free
                (equal 29 size)
                (< 3 size)
                (integerp size)
;               (equal x 4)
                (bvle 3 4 x))
           (equal (bvplus size 536870908 x)
                  (bvplus 3 -4 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))



;;old
;; (defthm bvlt-true-when-not-bvlt
;;   (implies (and (not (bvlt size x free))
;;                 (bvlt size k free))
;;            (equal (bvlt size k x)
;;                   t))
;;   :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
;;                                   (<-becomes-bvlt <-becomes-bvlt-alt
;;                                                   <-of-bvmult-hack ;bozo
;;                                                   <-of-bvplus-becomes-bvlt-arg1
;;                                                   <-of-bvplus-becomes-bvlt-arg2)))))

(defthm unsigned-byte-p-when-not-bvlt-tighten
  (implies (and (not (bvlt size free x))
                (syntaxp (quotep free))
                (< (integer-length free) size) ;would loop if we allowed equal
                (natp size)
                (natp free)
                )
           (equal (unsigned-byte-p size x)
                  (unsigned-byte-p (integer-length free) x)))
  :hints (("Goal"
           :use ((:instance BVCHOP-IDENTITY (size size) (i x))
                 (:instance BVCHOP-IDENTITY (size size) (i free)))
           :in-theory (e/d (bvlt unsigned-byte-p)
                           (BVCHOP-IDENTITY
                            BVCHOP-DOES-NOTHING-REWRITE ;disable globally?
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-constant-when-usb
  (implies (and (syntaxp (quotep k))
                (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (<= (expt 2 xsize) (bvchop size k))
                (<= xsize size)
                (natp xsize)
                (Integerp size)
                (force (unsigned-byte-p-forced xsize x))
                )
           (equal (BVLT size k x)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt ; unsigned-byte-p
                                   UNSIGNED-BYTE-P-FORCED)
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

;; ;can we weaken other rules by using +1?
;; (defthm bvlt-when-bvlt-false
;;   (implies (and (bvlt size x free)
;;                 (bvle size free (+ 1 k))
;;                 (integerp k)
;;                 (natp size))
;;            (equal (bvlt size k x)
;;                   nil))
;;   :hints (("Goal"
;;            :cases ((integerp k))
;;            :in-theory (e/d (bvlt
;;                             bvchop-of-sum-cases
;;                             )
;;                            (<-becomes-bvlt <-becomes-bvlt-alt
;;                                            BVLT-OF-PLUS-ARG1
;;                                            BVLT-OF-PLUS-ARG2
;;                                            <-of-bvmult-hack ;bozo
;;                                            <-of-bvplus-becomes-bvlt-arg1
;;                                            <-of-bvplus-becomes-bvlt-arg2)))))


;gen the 1
(defthm bvlt-of-bvplus-1-cancel
  (implies (and (posp size)  ;why?
                (integerp x) ;why?
                )
           (equal (bvlt size (bvplus size 1 x) x)
                  (equal (bvchop size x) (+ -1 (expt 2 size)))))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvchop-of-sum-cases
                                   bvplus
                                   )
                                  (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                               <-becomes-bvlt <-becomes-bvlt-alt
                                               bvlt-of-plus-arg1
                                               bvlt-of-plus-arg2
                                               <-of-bvmult-hack ;bozo
                                               <-of-bvplus-becomes-bvlt-arg1
                                               <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-bvplus-1-cancel-alt
  (implies (and (posp size)  ;why?
                (integerp x) ;why?
                )
           (equal (bvlt size x (bvplus size 1 x))
                  (not (equal (bvchop size x) (+ -1 (expt 2 size))))))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvchop-of-sum-cases
                                   bvplus
                                   )
                                  (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                               <-becomes-bvlt <-becomes-bvlt-alt
                                               bvlt-of-plus-arg1
                                               bvlt-of-plus-arg2
                                               <-of-bvmult-hack ;bozo
                                               <-of-bvplus-becomes-bvlt-arg1
                                               <-of-bvplus-becomes-bvlt-arg2)))))

(in-theory (disable BVPLUS-3221225472-HACK))

;subsumes the one for 0
(defthm equal-of-constant-and-bvuminus
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                ;(integerp x)
                (natp size))
           (equal (equal k (bvuminus size x))
                  (and (unsigned-byte-p size k)
                       (equal (bvuminus size k) (bvchop size x)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvchop-of-minus) (bvminus-becomes-bvplus-of-bvuminus)))))

;gen
;the lemma is much nicer when we know the top slcie
(defthm bvlt-of-slice-top
  (implies (unsigned-byte-p 5 x) ;limit?
           (equal (BVLT 3 5 (SLICE 4 2 x))
                  (bvle 5 24 x)))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvchop-of-sum-cases
                                   bvplus
                                   slice-bound-lemma-gen slice-bound-lemma-gen2
                                   )
                                  (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                               <-becomes-bvlt <-becomes-bvlt-alt
                                               bvlt-of-plus-arg1
                                               bvlt-of-plus-arg2
                                               <-of-bvmult-hack ;bozo
                                               <-of-bvplus-becomes-bvlt-arg1
                                               <-of-bvplus-becomes-bvlt-arg2)))))


;gen the 31, 3, and bvplus
;hope the case split is okay..
(defthm bvlt-of-bvplus-31-3-tighten
  (implies (and (integerp x)
                (integerp y)
                (unsigned-byte-p 31 z)
                )

           (equal (BVLT 31 (BVPLUS 3 x y) z)
                  (if (bvle 31 8 z)
                      t
                    (bvlt 3 (BVPLUS 3 x y) z))))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   UNSIGNED-BYTE-P
                                   bvplus
                                   )
                                  (REWRITE-<-WHEN-SIZES-DONT-MATCH2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   <-of-bvmult-hack ;bozo
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2)))))

;gen!
(defthm bvplus-minus-4-tighten-32
  (implies (and (unsigned-byte-p 3 x) ;use bind-free
                (bvle 3 4 x))
           (equal (bvplus 32 4294967292 x)
                  (bvplus 3 -4 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))


(local (in-theory (disable bvchop-of-*))) ;;ffixme

(defthm bvlt-of-slice-top-gen
  (implies (unsigned-byte-p 5 x) ;limit?
           (equal (BVLT 3 k (SLICE 4 2 x))
                  (if (equal 7 (bvchop 3 k))
                      nil
                    (bvle 5 (* 4 (+ 1 (bvchop 3 k))) x))))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   bvchop-of-sum-cases
                                   bvplus
                                   slice-bound-lemma-gen
                                   slice-bound-lemma-gen2
                                   )
                                  (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                               bvchop-of-*
                                               <-becomes-bvlt <-becomes-bvlt-alt
                                               bvlt-of-plus-arg1
                                               bvlt-of-plus-arg2
                                               <-of-bvmult-hack ;bozo
                                               <-of-bvplus-becomes-bvlt-arg1
                                               <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-3-tighten-33
  (implies (and (unsigned-byte-p 3 x) ;use bind-free
                (bvle 3 3 x))
           (equal (bvplus 33 8589934589 x)
                  (bvplus 3 -3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))


(defthm bvplus-minus-13-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 13 x))
           (equal (bvplus 32 4294967283 x)
                  (bvplus 5 -13 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-11-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 11 x))
           (equal (bvplus 32 4294967285 x)
                  (bvplus 5 -11 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-11-tighten-33
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 11 x))
           (equal (bvplus 33 8589934581 x)
                  (bvplus 5 -11 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

;gen the 4
(defthm times-of-bvmult-4
 (implies (natp size)
          (equal (* 4 (BVPLUS size x y))
                 (bvmult (+ 2 size) 4 (BVPLUS size x y))))
 :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

;apply this in a bvplus context - fixme
(defthmd bvuminus-when-bvchop-gen-for-5
  (implies (and (equal (bvchop 2 x) 0) ;gen the 0 and the 2
                (integerp x)
                )
           (equal (bvuminus 5 x)
                  (bvmult 5 4 (bvuminus 3 (slice 4 2 x)))))
  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 3) (ls 2)))
           :in-theory (e/d (bvmult bvuminus bvminus bvchop-of-minus bvplus bvcat logapp)
                           (bvchop-of-*
                            anti-bvplus GETBIT-OF-+ bvminus-becomes-bvplus-of-bvuminus  PLUS-BECOMES-BVPLUS
                                        BVLT-OF-PLUS-ARG1
                                        BVLT-OF-PLUS-ARG2)))))

(defthm bvplus-of-bvuminus-when-bvchop-gen-for-5
  (implies (and (equal (bvchop 2 x) 0) ;gen the 0 and the 2
                (integerp x)
                )
           (equal (bvplus size k (bvuminus 5 x))
                  (bvplus size k (bvmult 5 4 (bvuminus 3 (slice 4 2 x))))))
  :hints (("Goal" :in-theory (disable bvmult-of-expt2-constant-version ;why?
                                      BVMULT-OF-4-GEN)
           :use (:instance bvuminus-when-bvchop-gen-for-5))))

;gen!
(defthm slice-when-not-bvlt
  (implies (not (bvlt 5 16 x))
           (equal (equal '5 (slice '4 '2 x))
                  nil))
  :hints (("Goal" :use ((:instance split-with-bvcat (x x) (hs 3) (ls 2)))
           :in-theory (e/d (bvlt ;unsigned-byte-p
                            )
                           (BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2)))))

;this loops with BVMULT-OF-4-GEN ?
(defthmd bvplus-of-bvcat-hack6-gen-low-open
  (implies (and (syntaxp (and (quotep k)
                              (quotep lowval)
                              (quotep highsize)
                              (quotep lowsize)))
                (<= (+ lowsize highsize) size)
                (natp lowsize)
                (natp highsize)
                (integerp k)
                (integerp lowval)
                (natp size)
                )
           (equal (bvplus size k (bvcat highsize highval lowsize lowval))
                  (bvplus size
                          (bvplus size k (bvchop lowsize lowval)) ;this gets computed
                          (bvmult (+ highsize lowsize) (expt 2 lowsize) (bvchop highsize highval)))))
  :hints (("Goal" :in-theory (e/d (bvcat bvmult logapp bvplus)
                                  (bvchop-of-*
                                   anti-bvplus GETBIT-OF-+
                                               BVLT-OF-PLUS-ARG1
                                               BVLT-OF-PLUS-ARG2
                                               PLUS-BECOMES-BVPLUS
                                               )))))

(in-theory (disable BVMULT-OF-4-GEN))

;bvmult should have bvchops?

(defthm bvlt-of-bvmult5-4-13
  (implies (integerp x)
           (equal (BVLT '5 (BVMULT '5 '4 x) '13)
                  (bvlt 3 x 4)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvmult
                                   )
                                  (bvchop-of-*
                                   BVLT-OF-4 ;yuck?
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   <-of-bvmult-hack ;bozo
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2)))))

;can we gen the 4??
(defthm bvmult-of-bvplus-4-3-5
  (implies (and (integerp x)
                (integerp y))
           (equal (BVMULT 5 4 (BVPLUS 3 x y))
                  (bvplus 5 (bvmult 5 4 x) (bvmult 5 4 y))))
  :hints (("Goal"
           :use (:instance BVCHOP-SHIFT-GEN (n 5) (m 2) (x (+ (bvchop 3 x) (bvchop 3 y))))
           :in-theory (e/d (bvcat bvmult logapp bvplus)
                           (bvchop-of-*
                            BVCHOP-SHIFT-GEN
                            ;BVCHOP-SHIFT-GEN-CONSTANT-VERSION
                            ;DISTRIBUTIVITY
                            BVPLUS-OF-BVCHOP-ARG2
                            BVPLUS-OF-BVCHOP-ARG1
                            anti-bvplus GETBIT-OF-+
                            BVLT-OF-PLUS-ARG1
                            BVLT-OF-PLUS-ARG2
                            PLUS-BECOMES-BVPLUS
                            )))))

(defthm bvlt-of-bvmult5-4-16
  (implies (integerp x)
           (equal (BVLT '5 (BVMULT '5 '4 x) 16)
                  (bvlt 3 x 4)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvmult
                                   )
                                  (bvchop-of-*
                                   BVLT-OF-4 ;yuck?
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   <-of-bvmult-hack ;bozo
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-13-tighten-6
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 13 x))
           (equal (bvplus 6 51 x)
                  (bvplus 5 -13 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-of-bvmult5-4-29
  (implies (integerp x)
           (equal (bvlt 5 (bvmult 5 4 x) 29)
                  (bvle 3 x 7)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvmult
                                   )
                                  (bvchop-of-*
                                   bvlt-of-4 ;yuck?
                                   bvcat-equal-rewrite-alt
                                   bvcat-equal-rewrite
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   <-of-bvmult-hack ;bozo
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2)))))


;this one splits into cases but the other doesn't...
(defthm bvlt-of-bvcat-arg2-bvmult-version
  (implies (and (natp highsize)
                (equal size2 (+ 2 highsize)))
           (equal (bvlt size2 (bvmult size2 4 x) k)
                  (or (bvlt highsize x (slice (+ -1 (+ 2 highsize)) 2 k))
                      (and (equal (bvchop highsize x) (slice (+ -1 (+ 2 highsize)) 2 k))
                           (bvlt 2 0 k)))))
  :hints (("Goal" :in-theory (e/d (BVMULT-OF-4-GEN) ( BVLT-OF-BVCAT-ARG2))
           :use (:instance bvlt-of-bvcat-arg2 (lowsize 2) (y 0) (size (+ 2 highsize))))))

(defthm bvlt-of-bvcat-arg3-bvmult-version
  (implies (and (integerp size2)
                (<= 2 size2))
           (equal (bvlt size2 k (bvmult size2 4 x))
                  (bvlt (+ -2 size2) (slice (+ -1 size2) 2 k) x)))
  :hints (("Goal" :in-theory (e/d (BVMULT-OF-4-GEN booland BVLT-OF-0-ARG2) (BVLT-OF-BVCAT-ARG2))
           :use (:instance bvlt-of-bvcat-arg2 (highsize (+ -2 size2))
                           (lowsize 2) (y 0) (size size2)))))


;; (defthm bvlt-of-bvmult5-4-gen
;;   (implies (integerp x)
;;            (equal (bvlt 5 (bvmult 5 4 x) k)
;;                   (if (equal 0 (bvchop 5 k))
;;                       nil
;;                     (bvlt 3 x (slice 4 2 k)))))
;;   :hints (("Goal" :use ((:instance split-with-bvcat (x k) (hs 3) (ls 2))
;;                         (:instance split-with-bvcat (x x) (hs 3) (ls 2)))
;;            :in-theory (e/d (bvlt ;unsigned-byte-p
;;                             bvmult
;;                             bvplus
;;                             )
;;                            (TIMES-OF-BVMULT-4
;;                             anti-bvplus GETBIT-OF-+
;;                             BVLT-OF-PLUS-ARG1
;;                             BVLT-OF-PLUS-ARG2
;;                             PLUS-BECOMES-BVPLUS
;;                             bvlt-of-4 ;yuck?
;;                             bvcat-equal-rewrite-alt
;;                             bvcat-equal-rewrite
;;                             <-becomes-bvlt <-becomes-bvlt-alt
;;                             <-of-bvmult-hack ;bozo
;;                             <-of-bvplus-becomes-bvlt-arg1
;;                             <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-3-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 3 x))
           (equal (bvplus 32 4294967293 x)
                  (bvplus 5 -3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))


(defthm bvplus-minus-16-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 16 x))
           (equal (bvplus 32 4294967280 x)
                  (bvplus 5 -16 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-17-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 17 x))
           (equal (bvplus 32 4294967279 x)
                  (bvplus 5 -17 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

;ffixme more like this or gen!!
(defthm bvplus-minus-18-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 18 x))
           (equal (bvplus 32 4294967278 x)
                  (bvplus 5 -18 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm plus-of-4-and-bv-becomes-bvplus
 (implies (and (unsigned-byte-p 3 x)
               (<= x 4))
          (equal (+ 4 (- x))
                 (bvplus 3 4 (bvuminus 3 x))))
 :hints (("Goal"
          :in-theory (e/d (bvuminus bvcat bvmult logapp bvplus bvminus)
                          (bvchop-of-*
                           BVCHOP-SHIFT-GEN
                           BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                           anti-bvplus GETBIT-OF-+
                           BVLT-OF-PLUS-ARG1
                           BVLT-OF-PLUS-ARG2
                           PLUS-BECOMES-BVPLUS
                           )))))


(defthm bvplus-minus-15-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 15 x))
           (equal (bvplus 32 4294967281 x)
                  (bvplus 5 -15 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-14-tighten-32
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 14 x))
           (equal (bvplus 32 4294967282 x)
                  (bvplus 5 -14 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-14-tighten-6
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 14 x))
           (equal (bvplus 6 50 x)
                  (bvplus 5 -14 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))


(defthm rewrite-unsigned-byte-p-when-term-size-is-larger-better
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'x-size x)
                           (x-size))
                (< n x-size)
                (natp n)
                (force (natp x-size))
                (force (unsigned-byte-p-forced x-size x)))
           (equal (unsigned-byte-p n x)
                  (equal (slice (+ -1 x-size) n x) 0)))
  :hints (("Goal" :use (:instance rewrite-unsigned-byte-p-when-term-size-is-larger)
           :in-theory (e/d (unsigned-byte-p-forced) ( rewrite-unsigned-byte-p-when-term-size-is-larger)))))

(in-theory (disable rewrite-unsigned-byte-p-when-term-size-is-larger))

(defthm bvchop-of-sum-of-expt
  (implies (and (<= size size2)
                (natp size)
                (integerp size2)
                (integerp x)
                )
           (equal (BVCHOP size (+ x (EXPT 2 SIZE2)))
                  (BVCHOP size x)))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-sum-of-minus-of-expt
  (implies (and (<= size size2)
                (natp size)
                (integerp size2)
                (integerp x)
                )
           (equal (BVCHOP size (+ x (- (EXPT 2 SIZE2))))
                  (BVCHOP size x)))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-sum-of-minus-of-expt-arg3
  (implies (and (<= size size2)
                (natp size)
                (integerp size2)
                (integerp x)
                (integerp y)
                )
           (equal (BVCHOP size (+ x y (- (EXPT 2 SIZE2))))
                  (BVCHOP size (+ x y))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm equal-of-plus-and-plus-cancel
  (implies (and (rationalp z)
                (rationalp x)
                (rationalp y)
                (rationalp w))
           (equal (EQUAL (+ z y X) (+ X w))
                  (equal (+ z y) w))))

(defthm bvplus-minus-15-tighten-6
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 15 x))
           (equal (bvplus 6 49 x)
                  (bvplus 5 -15 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))


;; (thm
;;  (equal (< (SLICE 6 5 K) 3)
;;         (not (equal 3 (SLICE 6 5 K))))
;;  :hints (("Goal"
;;           :use (:instance UNSIGNED-BYTE-P-OF-SLICE (high 6) (low 5) (n (+ 1 6 (- 5))))
;;           :in-theory (e/d (UNSIGNED-BYTE-P)
;;                           (UNSIGNED-BYTE-P-OF-SLICE-GEN
;;                            SLICE-BOUND-2
;;                            SLICE-BOUND
;;                            UNSIGNED-BYTE-P-OF-SLICE)))))


;; (defthm slice-is-max-6-5
;;   (implies (and (<= 96 k)
;;                 (unsigned-byte-p 7 k))
;;            (equal (slice 6 5 k)
;;                   3))
;;   :hints (("Goal"
;;            :use (:instance split-with-bvcat (x k) (hs 2) (ls 5))
;;            :in-theory (e/d () ( ;anti-slice
;;                                <-BECOMES-BVLT-ALT
;;                                <-becomes-bvlt
;;                                BVCAT-SLICE-SAME
;;                                BVCAT-EQUAL-REWRITE-ALT
;;                                BVCAT-EQUAL-REWRITE)))))

;; (defthm bvplus-minus-15-tighten-6
;;   (implies (and (syntaxp (quotep k))
;;                 (< (- (expt 2 size) (expt 2 5)) ;gen?
;;                    (bvchop size k))
;;                 (unsigned-byte-p 5 x) ;use bind-free
;;                 (< 5 size)
;;                 (equal size 7)
;; ;                (equal k 120)
;;                 (natp size)
;;                 (unsigned-byte-p size k)
;;                 (< 0 (bvchop size k)) ;??
;;                 (integerp k)
;;                 (bvle size (- (expt 2 size) k) x))
;;            (equal (bvplus size k x)
;;                   (bvplus 5 (- (- (expt 2 size) k)) x)))
;;   :otf-flg t
;;   :hints (("Goal" :use ((:instance split-with-bvcat (x k) (hs (+ -5 size)) (ls 5))
;;                         (:instance split-with-bvcat (x x) (hs (+ -5 size)) (ls 5)))
;; ;;            :use (:instance REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2
;; ;;                            (y (BVCHOP SIZE (+ K X)))
;; ;;                            (y-size size)
;; ;;                            (x (BVCHOP 5 (+ K X)))
;; ;;                            (x-size 5))
;;            :in-theory (e/d (bvlt ;unsigned-byte-p
;;                             bvcat logapp
;;                             ;slice-of-sum-cases
;;                             bvchop-of-sum-cases
;;                             bvplus)
;;                            ( ;REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER
;;                             REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2
;;
;;                             anti-bvplus GETBIT-OF-+
;;                             SLICE-OF-+
;;                             getbit-of-+
;;                             BVLT-OF-PLUS-ARG1
;;                             BVLT-OF-PLUS-ARG2
;;                             PLUS-BECOMES-BVPLUS
;;                             <-becomes-bvlt <-becomes-bvlt-alt
;;                             <-of-bvmult-hack ;bozo
;;                             <-of-bvplus-becomes-bvlt-arg1
;;                             <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvchop-of-if
  (equal (bvchop n (if test a b))
         (if test (bvchop n a) (bvchop n b))))

(defthm bvuminus-trim
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< (+ 1 n) xsize)
                (natp n)
                (integerp xsize))
           (equal (bvuminus n x)
                  (bvuminus n (trim n x))))
  :hints (("Goal" :in-theory (e/d (bvminus bvuminus trim
                                           bvchop-when-i-is-not-an-integer)
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(in-theory (disable BVMINUS-TIGHTEN)) ;trying with this off

;; can cause case splits:
(in-theory (disable ;BVPLUS-OF-BVPLUS-CONSTANTS-SIZE-DIFFERS-BETTER
;                    BVPLUS-OF-BVUMINUS-TIGHTEN-GEN
                    ;SLICE-OF-BVPLUS-CASES
                    SLICE-OF-BVUMINUS
                    GETBIT-OF-BVPLUS-SPLIT))


;because we're not splitting slice of bvplus
(defthm slice-of-plus-minus-1-equal-0-32-4
  (implies (unsigned-byte-p 4 x) ;limit?
           (equal (equal (slice 31 4 (bvplus 32 4294967295 x)) 0)
                  (not (equal x 0))))
  :hints (("Goal" :in-theory (enable slice-of-bvplus-cases))))

;gen!
;gend below?
(defthm equal-of-1-and-getbit-of-bvpluss-minus-4
  (equal (equal 1 (getbit 31 (bvplus 32 4294967292 x)))
         (or (bvle 32 (+ (expt 2 31) 4) x)
             (bvlt 32 x 4)))
  :hints (("Goal" :in-theory (e/d (getbit-of-bvplus-split bvcat logapp bvlt ;BVCHOP-32-SPLIT-HACK
                                                          BVCHOP-WHEN-TOP-BIT-NOT-1
                                                          getbit-of-plus
                                                          )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  BVCAT-OF-GETBIT-AND-X-ADJACENT
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2
                                                  REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2
                                                  REWRITE-<-WHEN-SIZES-DONT-MATCH
                                                  REWRITE-<-WHEN-SIZES-DONT-MATCH2
                                                  ))
           :use (:instance split-with-bvcat (x x) (hs 1) (ls 31)))))

(DEFTHM BVPLUS-OF-BVUMINUS-TIGHTEN-GEN-no-split
  (IMPLIES (AND (syntaxp (and (quotep size)
                              (quotep k)
                              (quotep n)))
                (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< XSIZE N)
                (not (EQUAL 0 X))
                (<= N SIZE)
                (NATP N)
                (FORCE (UNSIGNED-BYTE-P-FORCED XSIZE X)))
           (EQUAL (BVPLUS SIZE K (BVUMINUS N X))
                  (BVPLUS SIZE
                          (BVPLUS SIZE (- (EXPT 2 N) (EXPT 2 XSIZE))
                                  K)
                          (BVUMINUS XSIZE X))))
  :hints (("Goal" :use (:instance BVPLUS-OF-BVUMINUS-TIGHTEN-GEN)
           :in-theory (disable BVPLUS-OF-BVUMINUS-TIGHTEN-GEN))))

;; (thm
;;  (implies (equal (getbit 31 x) 1)
;;           (equal (bvlt 32 x 2147483644)
;;                  nil))
;;  :hints (("Goal" :in-theory (e/d (getbit-of-bvplus-split bvcat logapp bvlt)
;;                                  (<-becomes-bvlt <-becomes-bvlt-alt
;;                                                   <-of-bvmult-hack ;bozo
;;                                                   <-of-bvplus-becomes-bvlt-arg1
;;                                                   <-of-bvplus-becomes-bvlt-arg2
;;                                                   ))
;;           :use (:instance split-with-bvcat (x x) (hs 1) (ls 31)))))


;gen to any bv
(defthm bvplus-impossible-value
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p size k))
                (Natp size))
           (equal (equal k (bvplus size x y))
                  nil)))

;just use BVUMINUS-WHEN-SMALLER or a variant of that?
(defthm bvuminus-of-bvplus-32-20
  (implies (and (integerp x)
                (integerp y)
                (equal n 30)
                )
           (equal (bvuminus 32 (bvplus n x y))
                  (if (equal 0 (bvplus n x y))
                      0
                  (bvplus 32
                          (- (expt 2 n))
                          (bvplus n (bvuminus n x)
                                  (bvuminus n y))))))
  :hints (("Goal" :use (:instance bvuminus-when-smaller (size 32) (x (bvplus n x y)) (free n))
           :in-theory (disable bvuminus-when-smaller))))

(defthm slice-equal-0-polarity2
  (implies (and (syntaxp (want-to-weaken (equal (slice n n x) 0))))
           (equal (equal 0 (slice n n x))
                  (not (equal 1 (slice n n x))))))

(defthm slice-equal-0-polarity
  (implies (and (syntaxp (want-to-weaken (equal 0 (slice n n x)))))
           (equal (equal 0 (slice n n x))
                  (not (equal 1 (slice n n x))))))




(defthm getbit-of-times-2
  (implies (and (syntaxp (not (quotep x))) ;defeats acl2's bone-headed matching
                (integerp x))
           (equal (getbit size (* 2 x))
                  (if (zp size)
                      0
                    (getbit (+ -1 size) x))))
  :hints (("Goal" :in-theory (e/d (getbit slice) (bvchop-1-becomes-getbit slice-becomes-getbit anti-slice)))))



;does this cause many case splits?
(defthm equal-of-1-and-getbit-of-bvplus
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal size2 (+ 1 size))
                (unsigned-byte-p size k) ;gen
                (integerp x)
                (integerp k)
                (natp size))
           (equal (equal 1 (getbit size (bvplus size2 k x)))
                  (if (equal 0 k)
                      (equal 1 (getbit size x))
                    ;drop bvchops?
                    (and (bvle (+ 1 size) (+ (expt 2 size) (- (bvchop size k))) x)
                         (bvlt (+ 1 size) x (- (bvchop size k)))))))
  :hints (("Goal"
;           :cases ((equal 0 (GETBIT SIZE K)) (equal 1 (GETBIT SIZE K)))
           :in-theory (e/d (getbit-of-bvplus-split
                            bvcat logapp bvlt ;BVCHOP-32-SPLIT-HACK
                            BVCHOP-WHEN-TOP-BIT-NOT-1
                            BVCHOP-WHEN-TOP-BIT-1-cheap
                            bvchop-of-sum-cases
                            bvplus
                            getbit-of-plus
                            )
                           (GETBIT-WHEN-BVLT-OF-SMALL-HELPER
                            GETBIT-OF-+ ;bozo
                            SLICE-OF-+
                            anti-bvplus GETBIT-OF-+
                            BVLT-OF-PLUS-ARG1
                            BVLT-OF-PLUS-ARG2
                            PLUS-BECOMES-BVPLUS
                            EQUAL-OF-BVCHOP-EXTEND
                            <-becomes-bvlt <-becomes-bvlt-alt
                            BVCAT-OF-GETBIT-AND-X-ADJACENT
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            )))))

(defthm equal-of-0-and-getbit-of-bvplus
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal size2 (+ 1 size))
                (unsigned-byte-p size k) ;gen
                (integerp x)
                (integerp k)
                (natp size))
           (equal (equal 0 (getbit size (bvplus size2 k x)))
                  (if (equal 0 k)
                      (not (equal 1 (getbit size x)))
                    (or (bvlt (+ 1 size) x (+ (expt 2 size) (- k)))
                        (bvle (+ 1 size) (- k) x)))))
  :hints (("Goal" :use (:instance equal-of-1-and-getbit-of-bvplus)
           :in-theory (disable equal-of-1-and-getbit-of-bvplus))))

(defthmd getbit-must-be-1
  (implies (and (<= (EXPT 2 SIZE) K)
                (UNSIGNED-BYTE-P (+ 1 SIZE) K)
                (natp size))
           (equal (GETBIT SIZE K)
                  1))
  :hints (("Goal" :in-theory (e/d (UNSIGNED-BYTE-P getbit slice logtail)
                                  (anti-slice bvchop-1-becomes-getbit slice-becomes-getbit)))))

(defthm <-of-plus-times-2-cancel
  (equal (< (+ y x) (* 2 y ))
         (< x y)))

;does this cause many case splits?
(defthm equal-of-1-and-getbit-of-bvplus-big-k
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal size2 (+ 1 size))
                (< (expt 2 size) k) ;this case ;allow =?
                (unsigned-byte-p size2 k)
                (integerp x)
                (natp k)
                (natp size))
           (equal (equal 1 (getbit size (bvplus size2 k x)))
                  (or (bvle (+ 1 size) (- (expt 2 size) k) x)
                      (bvlt (+ 1 size) x (- (expt 2 size2) k)))))
  :hints (("Goal"
           :cases ((equal 0 (GETBIT SIZE X)) (equal 1 (GETBIT SIZE X)))
           :use ((:instance split-with-bvcat (x k) (hs 1) (ls size))
                 (:instance split-with-bvcat (x x) (hs 1) (ls size)))
           :in-theory (e/d (getbit-must-be-1
                            getbit-of-plus
                            getbit-of-bvplus-split
                            bvcat logapp bvlt ;BVCHOP-32-SPLIT-HACK
                            BVCHOP-WHEN-TOP-BIT-NOT-1
                            BVCHOP-WHEN-TOP-BIT-1-cheap
                            bvchop-of-sum-cases
                            bvplus
                            )
                           (<-OF-BVCHOP-HACK
                            PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                            GETBIT-OF-+ ;bozo
                            SLICE-OF-+
                            anti-bvplus GETBIT-OF-+
                            BVLT-OF-PLUS-ARG1
                            BVLT-OF-PLUS-ARG2
                            PLUS-BECOMES-BVPLUS
                            EQUAL-OF-BVCHOP-EXTEND
                            <-becomes-bvlt <-becomes-bvlt-alt
                            BVCAT-OF-GETBIT-AND-X-ADJACENT
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            )))))

(defthm equal-of-0-and-getbit-of-bvplus-big-k
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal size2 (+ 1 size))
                (< (expt 2 size) k) ;this case ;allow =?
                (unsigned-byte-p size2 k)
                (integerp x)
                (natp k)
                (natp size))
           (equal (equal 0 (getbit size (bvplus size2 k x)))
                  (and (bvlt (+ 1 size) x (- (expt 2 size) k))
                       (bvle (+ 1 size) (- (expt 2 size2) k) x))))
  :hints (("Goal" :use (:instance equal-of-1-and-getbit-of-bvplus-big-k)
           :in-theory (disable equal-of-1-and-getbit-of-bvplus-big-k
                               ;why did these loop?:
                               SLICE-OF-+
                               BVLT-OF-PLUS-ARG2
                               ))))

(defthm bvlt-of-slice
  (implies (and (syntaxp (and (quotep k)
                              (quotep highsize)
                              (quotep lowsize)
                              (quotep size2)))
                (equal size2 (+ 1 highsize (- lowsize)))
                (unsigned-byte-p (+ 1 highsize) x) ;limit?
                (natp lowsize)
                (<= lowsize highsize) ;gen?
                (natp highsize)
                )
           (equal (bvlt size2 (slice highsize lowsize x) k)
                  (if (equal 0 (bvchop size2 k))
                      nil
                    (bvle (+ 1 highsize) x (+ -1 (* (expt 2 lowsize) (bvchop size2 k)))))))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   slice-bound-lemma-gen
                                   slice-bound-lemma-gen2
                                   bvchop-of-sum-cases
                                   bvplus
                                   )
                                  (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                               <-becomes-bvlt <-becomes-bvlt-alt
                                               bvlt-of-plus-arg1
                                               bvlt-of-plus-arg2
                                               <-of-bvmult-hack ;bozo
                                               <-of-bvplus-becomes-bvlt-arg1
                                               <-of-bvplus-becomes-bvlt-arg2)))))

;gen
(defthm equal-0-and-slice-polarity
  (implies (and (syntaxp (want-to-weaken (equal 0 (slice 4 2 x)))))
           (equal (equal 0 (slice 4 2 x))
                  (not (bvlt 3 0 (slice 4 2 x)))))
  :hints (("Goal" :in-theory (e/d (BVLT-OF-0-ARG2) (SLICE-BOUND-LEMMA-GEN2)))))

;todo
(local (in-theory (disable REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1
                           REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2
                           REWRITE-<-WHEN-SIZES-DONT-MATCH
                           REWRITE-<-WHEN-SIZES-DONT-MATCH2)))

;gen!
(defthm bvlt-when-slice-bound
  (implies (not (equal 1 (slice 4 2 x)))
           (equal (bvlt 5 5 x)
                  (bvle 5 8 x)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (hs 3) (ls 2))
           :in-theory (e/d (bvlt logapp bvcat)
                           (anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            <-becomes-bvlt <-becomes-bvlt-alt
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-when-slice-bound2
  (implies (not (equal 1 (slice 4 2 x)))
           (equal (BVLT 5 x 8)
                  (BVLT 5 x 4)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (hs 3) (ls 2))
           :in-theory (e/d (bvlt logapp bvcat)
                           (
                            anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            <-becomes-bvlt <-becomes-bvlt-alt
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            <-of-bvmult-hack ;bozo
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2)))))

;gen
(defthmd slice-equal-0-rewrite
  (equal (equal 0 (slice 4 2 x))
         (< (bvchop 5 x) 4))
  :hints (("Goal" :use (:instance split-with-bvcat (hs 3) (ls 2))
           :in-theory (disable bvcat-slice-same BVCAT-OF-SLICE-AND-X-ADJACENT
                               bvlt-of-0-arg2 ;fixme use polarity
                               rewrite-bv-equality-when-sizes-dont-match-1
                               bvcat-equal-rewrite-alt
                               bvcat-equal-rewrite))))

;gen
(defthm equal-slice-0-when-bvlt
  (implies (and (BVLT 5 free x)
                (syntaxp (quotep free))
                (bvle 5 3 free))
           (equal (EQUAL 0 (SLICE 4 2 x))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt
                                   logapp bvcat
                                   slice-equal-0-rewrite
                                   )
                                  (
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   <-becomes-bvlt <-becomes-bvlt-alt
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   <-of-bvmult-hack ;bozo
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-7-tighten-30
  (implies (and (unsigned-byte-p 3 x) ;use bind-free
                (bvle 3 7 x))
           (equal (bvplus 30 1073741817 x)
                  (bvplus 3 -7 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))



(in-theory (enable BVPLUS-OF-BVPLUS-CONSTANTS-SIZE-DIFFERS-BETTER))

(in-theory (enable SLICE-OF-BVPLUS-CASES))

(in-theory (enable SLICE-OF-BVUMINUS))

(in-theory (enable BVLT-TIGHTEN-NON-DAG-STRONG-ARG2
                   BVLT-TIGHTEN-NON-DAG-STRONG-ARG3))

(defthm bvlt-of-bvplus-and-bvplus-hack
  (equal (BVLT 3 (BVPLUS 3 4 x) (BVPLUS 3 5 x))
         (not (equal (bvchop 3 x) 3)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvchop-of-sum-cases
                                   bvplus
                                   bvchop-when-i-is-not-an-integer
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                                  bvlt-of-plus-arg1
                                                  bvlt-of-plus-arg2

                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))


(defthm bvplus-minus-3-tighten-4
  (implies (and (unsigned-byte-p 3 x) ;use bind-free
                (bvle 3 3 x))
           (equal (bvplus 4 13 x)
                  (bvplus 3 -3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-minus-3-tighten-5
  (implies (and (unsigned-byte-p 3 x) ;use bind-free
                (bvle 3 3 x))
           (equal (bvplus 5 29 x)
                  (bvplus 3 -3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  <-of-bvmult-hack ;bozo
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))










;gen!
(defthm slice-equal-0-when-top-bit-known
  (implies (and (and (syntaxp (want-to-weaken (equal (slice 4 3 x) 0))))
                (equal (getbit 3 x) 0))
           (equal (equal (slice 4 3 x) 0)
                  (equal (slice 4 4 x) 0)))
  :hints (("Goal" :in-theory (disable GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT
                                      BVCAT-EQUAL-REWRITE-ALT
                                      BVCAT-EQUAL-REWRITE)
           :use (:instance split-with-bvcat (x (slice 4 3 x)) (hs 1) (ls 1)))))

(defthm bvlt-when-bvchop-hack
  (implies (EQUAL (BVCHOP 7 x) 4)
           (equal (BVLT 8 x 132)
                  (BVLT 8 x 5)))
  :hints (("Goal"
           :cases ((equal 0 (getbit 7 x))
                   (equal 1 (getbit 7 x)))
           :in-theory (e/d (bvlt ;unsigned-byte-p
                            )
                           (<-becomes-bvlt <-becomes-bvlt-alt
                                           <-of-bvmult-hack ;bozo
                                           <-of-bvplus-becomes-bvlt-arg1
                                           <-of-bvplus-becomes-bvlt-arg2)))))

;gen
(defthm unsigned-byte-p-of-bvmod-hack
  (equal (unsigned-byte-p 6 (bvmod 31 x 44))
         t)
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm mod-upper-bound-linear
  (IMPLIES (AND (> Y 0)
                (not (equal 0 y))
                (integerp x)
                (integerp y))
           (<= (MOD X Y) (+ -1 Y)))
  :rule-classes (:linear)
  )


;this one only holds for integers..
;gen!
(defthm bvlt-of-bvmod-hack
  (implies (and (bvle 6 (bvplus 6 -1 y) k)
                (<= 6 size)
                (unsigned-byte-p 6 y))
           (equal (bvlt 6 k (bvmod size x y))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvmod
                                   bvplus
                                   bvchop-of-sum-cases
                                   )
                                  ( anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                                bvlt-of-plus-arg1
                                                bvlt-of-plus-arg2
                                                 SLICE-OF-+

                                                <-becomes-bvlt <-becomes-bvlt-alt
                                                <-of-bvmult-hack ;bozo
                                                <-of-bvplus-becomes-bvlt-arg1
                                                <-of-bvplus-becomes-bvlt-arg2)))))



;gen!
(defthm UNSIGNED-BYTE-P-of-bvmod-4-helper
  (implies (integerp size)
           (equal (UNSIGNED-BYTE-P 2 (BVMOD size x 4))
                  t))
  :hints (("Goal" :cases ((<= 3 size))
           :in-theory (e/d (bvmod UNSIGNED-BYTE-P) ()))))

(defthm unsigned-byte-p-of-bvmod-4
  (implies (and (<= 2 n)
                (integerp n)
                (integerp size))
           (equal (unsigned-byte-p n (bvmod size x 4))
                  t))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvmod-4-helper)
           :in-theory (disable unsigned-byte-p-of-bvmod-4-helper))))

(defthm unsigned-byte-p-of-constant
  (implies (and (syntaxp (quotep k))
                (natp k)
                (<= (integer-length k) size)
                (integerp size))
           (equal (UNSIGNED-BYTE-P SIZE k)
                  t))
  :hints (("Goal"
           :use (:instance INTEGER-LENGTH-BOUND (n k))
           :in-theory (e/d (UNSIGNED-BYTE-P) (INTEGER-LENGTH-BOUND)))))

(defthm unsigned-byte-p-of-bvmod-helper
  (implies (and (integerp size)
                (equal k 44) ;fixme
                (natp k))
           (equal (unsigned-byte-p (integer-length k) (bvmod size x k))
                  t))
  :hints (("Goal" :cases ((<= (integer-length k) size))
           :use (:instance mod-upper-bound-linear (x (bvchop size x)) (y (bvchop size k)))
           :in-theory (e/d (bvmod unsigned-byte-p) ( mod-upper-bound-linear)))))

(defthm unsigned-byte-p-of-bvmod-44
  (implies (and (<= (integer-length k) n)
                (natp k)
                (equal k 44) ;fixme
                (integerp n)
                (integerp size))
           (equal (unsigned-byte-p n (bvmod size x k))
                  t))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvmod-helper)
           :in-theory (disable unsigned-byte-p-of-bvmod-helper))))

(in-theory (disable BVLT-OF-0-ARG2)) ; use polarity - gen EQUAL-0-AND-SLICE-POLARITY to any bv...

;gross to mix theories?
(defthm bv-array-clear-of-cons
  (implies (and (< i len)
                (equal (+ -1 len) (len x))
                (natp i)
                (true-listp x) ;move to conclusion
                (natp len)
                (natp size)
                )
           (equal (bv-array-clear size len i (cons a x))
                  (if (zp i)
                      (cons 0 (bvchop-list size x))
                    (cons (bvchop size a) (bv-array-clear size (+ -1 len) (+ -1 i) x)))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg)
                                  (UNSIGNED-BYTE-P-OF-+-OF-MINUS-ALT
                                   UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   ;;update-nth-becomes-update-nth2-extend-gen
                                   )))))

;;fixme clear-nth becomes bv-array-clear?

;gen the 4
(defthm unsigned-byte-p-of-plus-minus-4-gen
  (implies (and (syntaxp (not (quotep x))) ;defeats acl2's over-aggressive matching
                (unsigned-byte-p size x)
                (<= 2 size)) ;gen
           (equal (unsigned-byte-p size (+ -4 x))
                  (bvlt size 3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  ( ;<-becomes-bvlt
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   )))))

(defthm unsigned-byte-p-of-plus-minus-4-gen-dag
  (implies (and (unsigned-byte-p size x)
                (<= 2 size)) ;gen
           (equal (unsigned-byte-p size (+ -4 x))
                  (bvlt size 3 x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-plus-minus-4-gen)
           :in-theory (disable unsigned-byte-p-of-plus-minus-4-gen))))

;rename
;move
(defthmd nth-becomes-bv-array-read2
  (implies (and (all-unsigned-byte-p free data)
                (natp n)
                (< n (len data)))
           (equal (nth n data)
                  (bv-array-read free (len data) n data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite NTH-BECOMES-BV-ARRAY-READ2)))

(in-theory (disable REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER-BETTER)) ;this is expensive..

;gen
(defthm unsigned-byte-p-of-bvplus-4-31-minus-1
  (implies (UNSIGNED-BYTE-P 4 x)
           (equal (UNSIGNED-BYTE-P 4 (BVPLUS 31 2147483647 x))
                  (not (equal (bvchop 4 x) 0))))
  :hints (("Goal" :in-theory (enable REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER-BETTER))))

(in-theory (enable <-of-logext-and-0)) ;push back?

(defthmd bvchop-upper-bound-tight-linear
  (implies (natp size)
           (<= (bvchop size x) (+ -1 (expt 2 size))))
  :rule-classes ((:linear))
  )

(defthmd expt-plus-expt-linear
  (implies (integerp size)
           (equal (expt 2 size) (+ (expt 2 (+ -1 size)) (expt 2 (+ -1 size)))))
  :rule-classes ((:linear))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm plus-of-bvchop-<-expt
  (implies (and (< x (EXPT 2 (+ -1 BIGSIZE)))
                (natp bigsize))
           (< (+ X (BVCHOP (+ -1 BIGSIZE) K)) (EXPT 2 BIGSIZE)))
  :hints (("Goal" :in-theory (enable bvchop-upper-bound-tight-linear expt-plus-expt-linear))))

(DEFTHM <-of-expt-when-free
  (IMPLIES (AND (< x (EXPT R free))
                (<= free I)
                (INTEGERP I)
                (INTEGERP free)
                (< 1 R)
                (REAL/RATIONALP R)
                )
           (< x (EXPT R I)))
  :hints (("Goal" :use (:instance EXPT-IS-INCREASING-FOR-BASE>1 (i free) (j i))
           :in-theory (disable EXPT-IS-INCREASING-FOR-BASE>1 <-of-expt-and-expt))))



(defthmd unsigned-byte-p-of-bvplus-gen-positive-k
  (implies (and (syntaxp (quotep k))
                (natp bigsize)
                (< size bigsize)
                (natp size)
                (unsigned-byte-p size x) ;drop?
                (sbvle bigsize 0 k)
                (integerp k))
           (equal (unsigned-byte-p size (bvplus bigsize k x))
                  (and (bvlt bigsize x (bvminus bigsize (expt 2 size) k))
                       (bvle bigsize K (expt 2 size)))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        BVCHOP-WHEN-TOP-BIT-NOT-1)
                                  ( ;<-becomes-bvlt
                                   EQUAL-OF-BVCHOP-EXTEND
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

(defthm expt-bound-linear-2
  (implies (and (< size free)
                (integerp free)
                (integerp size))
           (<= (expt 2 size) (expt 2 (+ -1 free))))
  :rule-classes ((:linear)))

;;(in-theory (disable DECREMENT-POSITIVE-UNSIGNED-BYTE)) ;this is a bad rule

(defthm <-of-plus-expt-cancel
  (implies (integerp size)
           (equal (< (+ X (EXPT 2 (+ -1 SIZE)) y) (EXPT 2 SIZE))
                  (< (+ x y) (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm plus-of-minus-of-expt-and-expt-one-less
  (implies (integerp size)
           (equal (+ X (- (EXPT 2 SIZE)) (EXPT 2 (+ -1 SIZE)) y)
                  (+ X  (- (EXPT 2 (+ -1 SIZE))) y)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthmd unsigned-byte-p-of-bvplus-gen-negative-k
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p size x)
                (< size bigsize)
                (integerp bigsize)
;                (equal size 4) (equal bigsize 31)
                (natp size)
                (sbvlt bigsize k 0)
                (integerp k))
           (equal (unsigned-byte-p size (bvplus bigsize k x))
                  (and (bvlt bigsize x (bvminus bigsize (expt 2 size) k))
                       (bvle bigsize (- k) x))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

;;(in-theory (disable UNSIGNED-BYTE-PROMOTE)) ;i have a better rule?

(defthm unsigned-byte-p-of-bvplus-when-unsigned-byte-p
  (implies (and (syntaxp (and (quotep k)
                              (quotep bigsize)
                              (quotep size)))
                (unsigned-byte-p size x) ;drop?
                (natp size)
                (< size bigsize)
                (natp bigsize)
                (integerp k))
           (equal (unsigned-byte-p size (bvplus bigsize k x))
                  (if (sbvle bigsize 0 k)
                      (and (bvlt bigsize x (bvminus bigsize (expt 2 size) k))
                           (bvle bigsize k (expt 2 size)))
                    (and (bvlt bigsize x (bvminus bigsize (expt 2 size) k))
                         (bvle bigsize (- k) x)))))
  :hints (("Goal" :use ((:instance unsigned-byte-p-of-bvplus-gen-negative-k)
                        (:instance unsigned-byte-p-of-bvplus-gen-positive-k))
           :in-theory (disable GETBIT-OF-+))))

;these can cause case splits:
;enable them when stable?
(in-theory (disable BVPLUS-OF-BVPLUS-CONSTANTS-SIZE-DIFFERS-BETTER
                    SLICE-OF-BVPLUS-CASES
                    SLICE-OF-BVUMINUS
                    BVLT-TIGHTEN-NON-DAG-STRONG-ARG2
                    BVLT-TIGHTEN-NON-DAG-STRONG-ARG3
                    BVLT-OF-SLICE-TOP-GEN))

(in-theory (disable bv-array-read-of-bv-array-write-both-better
                    bvle-tighten-32-31
                    bvlt-add-to-both-sides-constant-lemma
                    bvlt-add-to-both-sides-constant-lemma-alt
                    bvlt-of-bvcat-arg2-bvmult-version
                    bvlt-of-bvuminus-and-constant
                    bvlt-of-bvuminus-arg2-constant
                    bvlt-of-constant-tighten-when-usb-arg1
                    bvlt-of-constant-tighten-when-usb-arg2
                    bvlt-of-slice-top-gen
                    bvuminus-when-smaller
                    equal-of-0-and-getbit-of-bvplus-big-k
                    rewrite-bv-equality-when-sizes-dont-match-1
                    rewrite-bv-equality-when-sizes-dont-match-2
                    sbvdiv-rewrite
                    sbvlt-rewrite
                    sbvmoddown-rewrite
                    unsigned-byte-p-of-bvplus-when-unsigned-byte-p))

;fixme use polarities?  can this be involved in loops?
;move?
(defthm bvlt-tighten-free
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (syntaxp (quotep free))
                (< free size)
                (unsigned-byte-p free k)
                (natp free)
                (natp size)
                )
           (equal (BVLT size k x)
                  (BVLT free k x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

;fixme use polarities?  can this be involved in loops?
;move?
(defthm bvlt-tighten-free-alt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (syntaxp (quotep free))
                (< free size)
                (unsigned-byte-p free k)
                (natp free)
                (natp size)
                )
           (equal (BVLT size x k)
                  (BVLT free x k)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))


;fixme gen
(defthm bvplus-minus-4-tighten
 (implies (and (unsigned-byte-p 5 x)
               (bvlt 5 3 x))
          (equal (bvplus 31 2147483644 x)
                 (bvplus 5 -4 x)))
 :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                       BVCHOP-WHEN-TOP-BIT-1)
                                 ( ;<-becomes-bvlt
                                  PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                  BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                  <-BECOMES-BVLT
                                  <-BECOMES-BVLT-alt
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                  anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                  bvlt-of-plus-arg1
                                  bvlt-of-plus-arg2
                                  SLICE-OF-+
                                  GETBIT-OF-+ ;looped
                                  )))))

;fixme gen
(defthm bvlt-constant-bvplus-constant-no-split
  (implies (and (bvlt 5 3 x)
                (integerp x) ;why?
                )
           (equal (bvlt 5 16 (bvplus 5 28 x))
                  (bvlt 5 (bvminus 5 16 28) x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

(in-theory (enable sbvdiv-when-y-negative))

(defthm sbvlt-of-0-when-shorter
  (implies (and (unsigned-byte-p free x)
                (< free 32)
                (natp free))
           (equal (SBVLT 32 x 0)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt))))



;gen!
(defthm bvplus-minus-4-tighten-32-5
  (implies (and (unsigned-byte-p 5 x)
                (bvlt 5 3 x))
           (equal (bvplus 32 4294967292 x)
                  (bvplus 5 -4 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))





(defthm bvlt-5-4-bvplus-5-28
  (implies (bvle 5 4 x)
           (equal (bvlt 5 4 (bvplus 5 28 x))
                  (bvlt 5 8 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

(defthm bvlt-of-bvuminus-and-constant-no-split
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep size))
                (not (equal 0 (bvchop size x)))
                (natp size))
           (equal (bvlt size (bvuminus size x) k)
                  (and (not (equal 0 (bvchop size k))) ;this gets resolved
                       (bvlt size
                             (bvuminus size k)
                             x))))
  :hints (("Goal" :use (:instance bvlt-of-bvuminus-and-constant)
           :in-theory (disable bvlt-of-bvuminus-and-constant))))

(defthm bvplus-of-bvplus-constants-size-differs-better-no-split
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep j))
                (syntaxp (quotep size))
                (< size bigsize) ;or else we don't need this rule
                (bvlt size x (bvuminus size j)) ;this case
                (integerp k)
                (natp size)
                (natp bigsize)
                (integerp j)
                (natp x))
           (equal (bvplus bigsize k (bvplus size j x))
                  (bvplus bigsize (bvplus bigsize k (bvchop size j)) (bvchop size x))))
  :hints (("Goal" :use (:instance bvplus-of-bvplus-constants-size-differs-better)
           :in-theory (disable bvplus-of-bvplus-constants-size-differs-better))))

(defthm bvplus-of-bvplus-constants-size-differs-better-no-split-case2
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep j))
                (syntaxp (quotep size))
                (syntaxp (quotep bigsize))
                (< size bigsize) ;or else we don't need this rule
                (not (bvlt size x (bvuminus size j))) ;this case
                (integerp k)
                (natp size)
                (natp bigsize)
                (integerp j)
                (natp x))
           (equal (bvplus bigsize k (bvplus size j x))
                  (if (equal 0 (bvchop size j)) ;this gets resolved
                      (bvplus bigsize k (bvchop size x))
                    (bvplus bigsize
                            (bvplus bigsize k
                                    (bvplus bigsize
                                            (bvuminus bigsize (expt 2 size))
                                            (bvchop size j)))
                            (bvchop size x)))))
  :hints (("Goal" :use (:instance bvplus-of-bvplus-constants-size-differs-better)
           :in-theory (disable bvplus-of-bvplus-constants-size-differs-better))))



(defthm bvlt-of-bvmult-5-5-4-28
  (equal (BVLT '5 (BVMULT '5 '4 x) '28)
         (bvlt 3 x 7))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  (bvchop-of-*
                                   ;;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

;gen!
(defthm bvlt-of-bvmult-5-5-4-14
  (equal (BVLT '5 (BVMULT '5 '4 x) '14)
         (bvle 3 x 3))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

(defthm bvlt-of-bvmult-5-5-4-15
  (equal (BVLT '5 (BVMULT '5 '4 x) '15)
         (bvle 3 x 3))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))


(DEFTHM BVLT-OF-SLICE-TOP-GEN-no-split
  (IMPLIES (and (syntaxp (quotep k))
                (UNSIGNED-BYTE-P 5 X)
                (not (EQUAL 7 (BVCHOP 3 K))))
           (EQUAL (BVLT 3 K (SLICE 4 2 X))
                  (BVLE 5 (* 4 (+ 1 (BVCHOP 3 K))) X)))
  :hints (("Goal" :use (:instance BVLT-OF-SLICE-TOP-GEN)
           :in-theory (disable BVLT-OF-SLICE-TOP-GEN))))

(defthm bvplus-minus-4-tighten-5
 (implies (and (unsigned-byte-p 3 x)
               (bvlt 3 3 x))
          (equal (bvplus 5 28 x)
                 (bvplus 3 -4 x)))
 :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                       BVCHOP-WHEN-TOP-BIT-1)
                                 ( ;<-becomes-bvlt
                                  PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                  BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                  <-BECOMES-BVLT
                                  <-BECOMES-BVLT-alt
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                  anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                  bvlt-of-plus-arg1
                                  bvlt-of-plus-arg2
                                  SLICE-OF-+
                                  GETBIT-OF-+ ;looped
                                  )))))

;add other cases?
(defthm slice-of-bvplus-cases-no-split-case-no-carry
  (implies (and (equal size (+ 1 high))
                (equal 0 (bvchop low x))
                (<= low high)
                (natp low)
                (integerp high))
           (equal (slice high low (bvplus size x y))
                  (bvplus (+ 1 high (- low))
                          (slice high low x)
                          (slice high low y))))
  :hints (("Goal" :use (:instance slice-of-bvplus-cases)
           :in-theory (disable slice-of-bvplus-cases))))

;don't bother when low=0?
;can this loop?
(defthm slice-of-bvplus-cases-no-split-carry
  (implies (and (equal size (+ 1 high))
                (not (equal 0 (bvchop low x))) ;do we need both of these?
                (not (bvlt low y (bvuminus low x))) ;do we need both of these?
                (<= low high)
                (natp low)
                (integerp high))
           (equal (slice high low (bvplus size x y))
                  (bvplus (+ 1 high (- low))
                          1
                          (bvplus (+ 1 high (- low))
                                  (slice high low x)
                                  (slice high low y)))))
  :hints (("Goal" :use (:instance slice-of-bvplus-cases)
           :in-theory (disable slice-of-bvplus-cases))))

(defthm slice-of-bvplus-cases-no-split-no-carry2
  (implies (and (equal size (+ 1 high))
                (bvlt low y (bvuminus low x)) ;can this loop? ;fixme can cause wasted work
                (<= low high)
                (natp low)
                (integerp high))
           (equal (slice high low (bvplus size x y))
                  (bvplus (+ 1 high (- low))
                          (slice high low x)
                          (slice high low y))))
  :hints (("Goal" :use (:instance slice-of-bvplus-cases)
           :in-theory (disable slice-of-bvplus-cases))))



(defthm bvlt-add-to-both-sides-constant-lemma-no-split2
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)
                              (quotep size)))
                (not (bvlt size y (bvuminus size k1))) ;this case
                (natp size))
           (equal (bvlt size k2 (bvplus size k1 y))
                  (if (bvlt size k2 k1)
                      (if (equal 0 (bvchop size k1))
                          t
                        (bvlt size (bvplus size k2 (bvuminus size k1)) y))
                    (if (equal 0 (bvchop size k1))
                        (bvlt size k2 y)
                      nil))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma)
           :in-theory (disable bvlt-add-to-both-sides-constant-lemma))))

(defthm bvlt-add-to-both-sides-constant-lemma-alt-no-split
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)
                              (quotep size)))
                (bvlt size x (bvuminus size k1)) ;this case
                (natp size))
           (equal (bvlt size (bvplus size k1 x) k2)
                  (if (bvlt size k2 k1) ;should just get computed
                      nil
                    (bvlt size x (bvplus size k2 (bvuminus size k1))))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma-alt)
           :in-theory (disable bvlt-add-to-both-sides-constant-lemma-alt))))

(defthm bvlt-add-to-both-sides-constant-lemma-alt-no-split2
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)
                              (quotep size)))
                (not (bvlt size x (bvuminus size k1))) ;this case
                (natp size))
           (equal (bvlt size (bvplus size k1 x) k2)
                  (if (equal 0 (bvchop size k1)) ;should get computed
                      (if (bvlt size k2 k1) ;should just get computed
                          nil
                        (bvlt size x (bvplus size k2 (bvuminus size k1))))
                    (if (bvlt size k2 k1) ;should just get computed
                        (bvlt size x (bvplus size k2 (bvuminus size k1)))
                      t))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma-alt)
           :in-theory (disable bvlt-add-to-both-sides-constant-lemma-alt))))

(defthm hackkkk
  (implies (NOT (BVLT 5 16 x))
           (equal (BVLT 5 19 x)
                  nil)))

(defthm bvlt-of-bvmult-5-5-4-30
  (equal (BVLT '5 (BVMULT '5 '4 x) 30)
         (bvle 3 x 7))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

;fixme!
(defthm bvlt-of-bvmult-5-5-4-31
  (equal (BVLT '5 (BVMULT '5 '4 x) 31)
         (bvle 3 x 7))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

;ffixme how is this different from the regular rule?
(defthm bvlt-trim-arg1-new
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize
                                                                        x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))

  :HINTS
  (("Goal"
    :by BVLT-TRIM-ARG1)))

(in-theory (disable BVLT-TRIM-ARG1)) ;to make this fire first

(DEFTHM UNSIGNED-BYTE-P-WHEN-BVLT-TIGHTEN
  (IMPLIES (AND (BVLT SIZE X FREE) ;allow one more fixme
                (SYNTAXP (QUOTEP FREE))
                (< (INTEGER-LENGTH FREE) SIZE)
                (NATP SIZE)
                (NATP FREE))
           (EQUAL (UNSIGNED-BYTE-P SIZE X)
                  (UNSIGNED-BYTE-P (INTEGER-LENGTH FREE) X)))
  :HINTS
  (("Goal"
    :USE ((:INSTANCE BVCHOP-IDENTITY (SIZE SIZE)
                     (I X))
          (:INSTANCE BVCHOP-IDENTITY (SIZE SIZE)
                     (I FREE)))
    :IN-THEORY
    (E/D (BVLT UNSIGNED-BYTE-P)
         (BVCHOP-IDENTITY
                           BVCHOP-DOES-NOTHING-REWRITE
                           <-BECOMES-BVLT
                           <-BECOMES-BVLT-ALT <-OF-BVMULT-HACK
                           <-OF-BVPLUS-BECOMES-BVLT-ARG1
                           <-OF-BVPLUS-BECOMES-BVLT-ARG2)))))

;fixme gen
(defthm bvlt-of-bvmod
  (implies (and (<= 6 size)
                (natp size))
           (equal (bvlt size 43 (bvmod size x 44))
                  nil))
  :hints (("Goal"          :expand ((bvmod 31 (bvchop 31 x) 44))
           :in-theory (e/d (bvlt unsigned-byte-p bvmod)
                           (;trim-to-n-bits-meta-rule-for-slice ;fixme
                            bvchop-does-nothing-rewrite
                            <-becomes-bvlt
                            <-becomes-bvlt-alt <-of-bvmult-hack
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvplus-of-1-33-32
  (implies (and (not (equal x (bvuminus 32 132)))
                (unsigned-byte-p 32 x))
           (equal (bvplus 33 1 (bvplus 32 131 x))
                  (bvplus 32 132 x)))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus bvuminus bvminus
                                        bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))



;gen
(defthm getbit-of-bvplus-flip
  (implies (and (equal n+1 (+ 1 n))
                (equal k (expt 2 n))
                (natp n))
           (equal (getbit n (bvplus n+1 k x))
                  (bitnot (getbit n x))))
  :hints (("Goal" :in-theory (e/d ( ;bvlt
                                   bvplus getbit-of-plus
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER

                                   bvchop-of-sum-cases sbvlt
                                   bvchop-when-i-is-not-an-integer
                                   bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))


(mutual-recursion
;note: there is no attempt to make sure a repeated variable in the pattern matches the same term each time
 (defun term-matches-pattern (term pattern)
   (declare (xargs :measure (acl2-count pattern)))
   (if (atom pattern)
       t
     (if (quotep pattern)
         (equal term pattern)
       (and (equal (ffn-symb term) (ffn-symb pattern))
            (term-matches-pattern-lst (fargs term) (fargs pattern))))))

 (defun term-matches-pattern-lst (term-lst pattern-lst)
   (declare (xargs :measure (acl2-count pattern-lst)))
   (if (atom pattern-lst)
       t
     (and (term-matches-pattern (car term-lst) (car pattern-lst))
          (term-matches-pattern-lst (cdr term-lst) (cdr pattern-lst))))))

(defun find-match-for-term (term alist)
  (if (endp alist)
      nil
    (let* ((pair (car alist))
           (key (car pair)))
      (if (term-matches-pattern term key)
          (cdr pair)
        (find-match-for-term term (cdr alist))))))

;think about how to auto-populate table
;; (defun bind-var-to-size-from-table (var term mfc state)
;;   (declare (xargs :stobjs (state)
;;                   :verify-guards nil
;;                   )
;;            (ignore mfc))
;;   (let* ((table (f-get-global 'usb-table state))
;;          (size (find-match-for-term term table)))
;;     (if (natp size)
;;         (acons var (list 'quote size) nil)
;;       nil)))

;; (defun bind-var-to-list-size-from-table (var term mfc state)
;;   (declare (xargs :stobjs (state)
;;                   :verify-guards nil
;;                   )
;;            (ignore mfc))
;;   (let* ((table (f-get-global 'usb-list-table state))
;;          (size (find-match-for-term term table)))
;;     (if (natp size)
;;         (acons var (list 'quote size) nil)
;;       nil)))

;; (defthm usb-implies-integerp-table
;;   (implies (and (bind-free (bind-var-to-size-from-table 'free x mfc state))
;;                 (unsigned-byte-p free x))
;;            (equal (integerp x)
;;                   t)))

;; (defthm usb-implies-not-negative-table
;;   (implies (and (bind-free (bind-var-to-size-from-table 'free x mfc state))
;;                 (unsigned-byte-p free x))
;;            (equal (< x 0)
;;                   nil)))
;

;fixme gen
(defthm sbvlt-of-bvplus
  (implies (and (unsigned-byte-p free x)
                (<= free 30)
                (natp x))
           (equal (SBVLT '32 (BVPLUS '32 '1 x) '0)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus
                                        GETBIT-TOO-HIGH
                                        GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                        UNSIGNED-BYTE-P
                                        bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

;; (defthm sbvlt-of-bvplus-table
;;   (implies (and (bind-free (bind-var-to-size-from-table 'free x mfc state))
;;                 (<= free 30)
;;                 (unsigned-byte-p free x)
;;                 (natp x))
;;            (equal (SBVLT '32 (BVPLUS '32 '1 x) '0)
;;                   nil))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvlt bvplus
;;                                         GETBIT-TOO-HIGH
;;                                         GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
;;                                         UNSIGNED-BYTE-P
;;                                         bvchop-of-sum-cases sbvlt
;;                                         bvchop-when-i-is-not-an-integer
;;                                         bvchop-when-top-bit-1)
;;                                   ( ;<-becomes-bvlt
;;                                    plus-1-and-bvchop-becomes-bvplus ;fixme
;;                                    bvminus-becomes-bvplus-of-bvuminus
;;                                    <-becomes-bvlt
;;                                    <-becomes-bvlt-alt
;;                                    <-of-bvplus-becomes-bvlt-arg1
;;                                    <-of-bvplus-becomes-bvlt-arg2
;;                                    anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
;;                                    bvlt-of-plus-arg1
;;                                    bvlt-of-plus-arg2
;;                                    slice-of-+
;;                                    getbit-of-+ ;looped
;;                                    )))))

;fixme gen!
(defthm UNSIGNED-BYTE-P-of-bvplus-8-9-1
  (implies (and (UNSIGNED-BYTE-P 8 x)
                )
           (equal (UNSIGNED-BYTE-P 8 (BVPLUS 9 1 x))
                  (not (equal x 255))))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus
                                        GETBIT-TOO-HIGH
                                        GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                        UNSIGNED-BYTE-P
                                        bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

;gen
(defthm bvlt-when-UNSIGNED-BYTE-P
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (unsigned-byte-p free x)
                (syntaxp (quotep free))             ;new
                (<= (expt 2 free) (bvchop size k)) ;now gets computed
                (< free size)
                (natp size)
                (natp free))
           (equal (BVLT size x k)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus
                                        GETBIT-TOO-HIGH
                                        GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                        UNSIGNED-BYTE-P
                                        bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

(in-theory (enable bvuminus-when-smaller)) ;yuck?

(defthm bvplus-minus-124-tighten-32
 (implies (and (unsigned-byte-p 8 x)
               (bvlt 8 124 x))
          (equal (bvplus 32 4294967172 x)
                 (bvplus 8 -124 x)))
 :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                       BVCHOP-WHEN-TOP-BIT-1)
                                 ( ;<-becomes-bvlt
                                  PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                  BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                  <-BECOMES-BVLT
                                  <-BECOMES-BVLT-alt
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                  anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                  bvlt-of-plus-arg1
                                  bvlt-of-plus-arg2
                                  SLICE-OF-+
                                  GETBIT-OF-+ ;looped
                                  )))))

;gen! fixme
(defthm bvplus-minus-125-tighten-32
 (implies (and (unsigned-byte-p 8 x)
               (bvlt 8 125 x))
          (equal (bvplus 32 4294967171 x)
                 (bvplus 8 -125 x)))
 :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                       BVCHOP-WHEN-TOP-BIT-1)
                                 ( ;<-becomes-bvlt
                                  PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                  BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                  <-BECOMES-BVLT
                                  <-BECOMES-BVLT-alt
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                  anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                  bvlt-of-plus-arg1
                                  bvlt-of-plus-arg2
                                  SLICE-OF-+
                                  GETBIT-OF-+ ;looped
                                  )))))

(defthm bvplus-minus-124-tighten-33
 (implies (and (unsigned-byte-p 8 x)
               (bvlt 8 124 x))
          (equal (bvplus 33 8589934468  x)
                 (bvplus 8 -124 x)))
 :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                       BVCHOP-WHEN-TOP-BIT-1)
                                 ( ;<-becomes-bvlt
                                  PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                  BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                  <-BECOMES-BVLT
                                  <-BECOMES-BVLT-alt
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                  <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                  anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                  bvlt-of-plus-arg1
                                  bvlt-of-plus-arg2
                                  SLICE-OF-+
                                  GETBIT-OF-+ ;looped
                                  )))))


;introduces a case split...
(defthm bvplus-of-x-and-bvuminus-x-2
  (implies (and (unsigned-byte-p 2 x)
                (natp size)
                (<= 3 size))
           (equal (BVPLUS size x (BVUMINUS 2 x))
                  (if (equal 0 x)
                      0
                    4)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))


;move
(defthm leftrotate32-trim
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'xsize x))
                (< 5 xsize)
                (integerp xsize)
                (natp x))
           (equal (leftrotate32 x y)
                  (leftrotate32 (trim 5 x) y)))
  :hints (("Goal" :in-theory (e/d (trim) (leftrotate32)))))

;; (defthm nth-becomes-bv-array-read2-table
;;   (implies (and (bind-free (bind-var-to-list-size-from-table 'free data mfc state))
;;                 (all-unsigned-byte-p free data)
;;                 (< n (len data))
;;                 (natp n))
;;            (equal (nth n data)
;;                   (bv-array-read free (len data) n data)))
;;   :hints (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg)
;;                                   (NTH-BECOMES-BV-ARRAY-READ2
;;                                    NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

;; trying without this
;; (defthm clear-nth-of-bv-array-write
;;   (implies (and (< n len)
;;                 (natp n)
;;                 (integerp len))
;;            (equal (list::clear-nth n (bv-array-write size len n val data))
;;                   (list::clear-nth n (bvchop-list size (take len data)))))
;;   :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2 ceiling-of-lg)
;;                                   (update-nth-becomes-update-nth2-extend-gen)))))

;; (defthm <-becomes-bvlt-table
;;   (implies (and (bind-free (bind-var-to-size-from-table 'free x mfc state))
;;                 (syntaxp (quotep k))
;;                 (unsigned-byte-p free x)
;;                 (unsigned-byte-p free k)
;;                 )
;;            (equal (< k x)
;;                   (bvlt free k x)))
;;   :hints (("Goal" :use (:instance <-becomes-bvlt)
;;            :in-theory (disable <-becomes-bvlt))))

;; (defthm <-becomes-bvlt-alt-table
;;   (implies (and (bind-free (bind-var-to-size-from-table 'free x mfc state))
;;                 (syntaxp (quotep k))
;;                 (unsigned-byte-p free x)
;;                 (unsigned-byte-p free k)
;;                 )
;;            (equal (< x k)
;;                   (bvlt free x k)))
;;   :hints (("Goal" :use (:instance <-becomes-bvlt-alt)
;;            :in-theory (disable <-becomes-bvlt-alt))))

;; (DEFTHM BV-ARRAY-READ-OF-BV-ARRAY-WRITE-SAME-GEN-gen
;;   (IMPLIES (AND (<= WIDTH1 WIDTH2)
;;                 (NATP WIDTH1)
;;                 (INTEGERP WIDTH2)
;;                 (NATP INDEX)

;;                 (INTEGERP LEN))
;;            (EQUAL (BV-ARRAY-READ WIDTH1 LEN INDEX (BV-ARRAY-WRITE WIDTH2 LEN INDEX VAL LST))
;;                   (if (< INDEX LEN)
;;                       (BVCHOP WIDTH1 VAL)
;;                     nil)))
;;   :HINTS (("Goal" :IN-THEORY (E/D (BV-ARRAY-READ BV-ARRAY-WRITE)
;;                                   (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))


;alternate version?
(defthm bvlt-tighten
  (implies (and (syntaxp (want-to-weaken (bvlt size k x)))
                (not (equal k x))
                (unsigned-byte-p size x)
                (unsigned-byte-p size k)
                (natp size)
                (< 0 k))
           (equal (bvlt size k x)
                  (bvlt size (+ -1 k) x)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 1 nil nil nil)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

(in-theory (disable NOT-EQUAL-NTH-WHEN-NOT-MEMBERP-NO-LIMIT))

;; (3 Breaking (:REWRITE BVLT-ADD-TO-BOTH-SIDES-CONSTANT-LEMMA-NO-SPLIT2)
;; on (BVLT '8 '132 (BVPLUS '8 '255 FARG0)):
;; 3 ACL2 >:GO
;;
;; 3x (:REWRITE BVLT-ADD-TO-BOTH-SIDES-CONSTANT-LEMMA-NO-SPLIT2) failed
;; because :HYP 2 is judged more complicated than its ancestors (type
;; :ANCESTORS to see the ancestors and :PATH to see how we got to this
;; point).

;fixme gen - the other rule failed -- see above!
(defthm bvlt-of-bvplus-8-minus-1
  (implies (not (equal 0 (bvchop 8 x)))
           (equal (BVLT '8 '132 (BVPLUS '8 '255 x))
                  (bvlt 8 133 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))


(defthm bvlt-of-plus-of-minus-1
  (implies (and (not (equal 0 (bvchop 8 x)))
                (integerp x))
           (equal (BVLT '8 '132 (+ -1 x))
                  (bvlt 8 133 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-of-sum-cases
                                        bvchop-when-i-is-not-an-integer
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))


;yuck!
;use free vars instead!
(defthm bvlt-hackk
  (implies (not (bvlt 6 43 x))
           (bvlt '6 x '44)))

;gen!
;can this loop?
(defthm bvlt-from-rules
  (implies (and (bind-from-rules (not (bvlt '6 (:free k) x)))
                (bvle 6 k 43))
           (BVLT '6 x '44))
  :hints (("Goal" :use (:instance bvlt-transitive-core-2 (size 6) (y 44) (free 43))
           :in-theory (disable BVLT-TRANSITIVE-FREE2-BACK
                               BVLT-TRANSITIVE-1-A
                               ;BVLT-TRANSITIVE-FREE-BACK
                               )
           )))


;gen the 4!
(defthm <-when-unsigned-byte-p-from-rules
  (implies (and (bind-from-rules (unsigned-byte-p (:free free) x))
                (<= free 2))
           (< x 4)))

(DEFTHM BVPLUS-TIGHTEN-NON-DAG-arg2-from-rules
  (IMPLIES (AND (BIND-FREE (BIND-VAR-TO-UNSIGNED-TERM-SIZE 'XSIZE X) (xsize))
                (bind-from-rules (UNSIGNED-BYTE-P (:free YSIZE) Y))
                (< (+ 1 (MAX XSIZE YSIZE)) SIZE)
                (FORCE (UNSIGNED-BYTE-P-FORCED XSIZE X)) (NATP SIZE)
                (POSP XSIZE))
           (EQUAL (BVPLUS SIZE X Y)
                  (BVPLUS (+ 1 (MAX XSIZE YSIZE)) X Y)))
  :hints (("Goal" :use BVPLUS-TIGHTEN-NON-DAG
           :in-theory (e/d (UNSIGNED-BYTE-P-FORCED) ( BVPLUS-TIGHTEN-NON-DAG)))))

;use to gen the mod of 4 lemmas
(DEFTHM MOD-OF-MOD-BASES-MULTIPLE-alt
  (IMPLIES (AND (INTEGERP (/ BIG SMALL))
                (RATIONALP X)
                (<= 0 x)
                (RATIONALP SMALL)
                (<= 0 SMALL)
                (RATIONALP BIG)
                (<= 0 BIG))
           (EQUAL (MOD (MOD X big) small)
                  (if (equal 0 small)
                      (MOD X big)
                    (MOD X small))))
  :hints (("Goal" :cases ((equal 0 big)))))

;gen!
(defthm unsigned-byte-p-of-bvplus-5-6-1
  (implies (unsigned-byte-p 5 x)
           (equal (UNSIGNED-BYTE-P 5 (BVPLUS 6 1 x))
                  (not (equal x 31))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-of-sum-cases
                                        bvchop-when-i-is-not-an-integer
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

(defthm bvlt-of-bvplus-minus-1-5
  (implies (not (equal 0 (bvchop 5 x)))
           (equal (BVLT '5 '20 (BVPLUS '5 '31 x))
                  (BVLT '5 '21 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-of-sum-cases
                                        bvchop-when-i-is-not-an-integer
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

;;which do we prefer?: (BVPLUS 7 1 (BVMULT 6 2 FARG0)) or (BVCAT 5 FARG0 1 1)?
;same with (BVMULT 6 2 FARG0) and (BVCAT 5 FARG0 1 0)..
;maybe i'll say we prefer bvmult/bvplus inside an nth or bv-array-read?

(DEFTHM BVCHOP-SHIFT-GEN-alt
  (IMPLIES (AND (INTEGERP X) (INTEGERP N) (NATP M))
           (EQUAL (BVCHOP N (* X (EXPT 2 M)))
                  (IF (<= M N)
                      (* (EXPT 2 M) (BVCHOP (- N M) X))
                      0)))
  :hints (("Goal" :use (:instance BVCHOP-SHIFT-GEN)
           :in-theory (disable BVCHOP-SHIFT-GEN))))

(defthmd bvcat-rewrite
  (implies (and (natp lowsize)
                ;(natp lowval)
                (natp highsize)
                ;;(natp highval)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvplus (+ highsize lowsize)
                          (bvchop lowsize lowval)
                          (bvmult (+ lowsize highsize)
                                  (expt 2 lowsize)
                                  highval))))
  :hints (("Goal"
           :use (:instance BVCAT-NUMERIC-BOUND (k (expt 2 (+ highsize lowsize))))
           :in-theory (e/d (bvcat logapp bvplus bvmult
                                  bvchop-of-sum-cases)
                           ( anti-bvplus GETBIT-OF-+
                                            BVCAT-NUMERIC-BOUND
                                            PLUS-BECOMES-BVPLUS
                                            BVLT-OF-PLUS-ARG1
                                            BVLT-OF-PLUS-ARG2)))))

(defthm nth-of-bvcat
  (implies (and (natp lowsize)
                (natp lowval)
                (natp highsize)
                (natp highval))
           (equal (nth (bvcat highsize highval lowsize lowval) x)
                  (nth (bvplus (+ highsize lowsize)
                               (bvchop lowsize lowval)
                               (bvmult (+ lowsize highsize)
                                       (expt 2 lowsize)
                                       highval))
                       x)))
  :hints (("Goal" :in-theory (e/d (bvcat-rewrite) (BVMULT-OF-EXPT2 ;looped
                                                   )))))

;yuck?
(defthm bv-array-read-of-bvcat
  (implies (and (natp lowsize)
                (natp lowval)
                (natp highsize)
                (natp highval))
           (equal (bv-array-read width len (bvcat highsize highval lowsize lowval) data)
                  (bv-array-read width len (bvplus (+ highsize lowsize)
                                                   (bvchop lowsize lowval)
                                                   (bvmult (+ lowsize highsize)
                                                           (expt 2 lowsize)
                                                           highval)) data)))
  :hints (("Goal" :in-theory (e/d (bvcat-rewrite) (BVMULT-OF-EXPT2)))))

;(in-theory (disable BVMULT-OF-2)) ;we are leaving it as a mult in some cases now

(defthm bvmult-tighten-2-32-5
  (implies (unsigned-byte-p 5 x)
           (equal (BVMULT 32 2 x)
                  (bvmult 6 2 x)))
  :hints (("Goal" :in-theory (e/d (bvmult) (;*-OF-2-BECOMES-BVMULT
                                            )))))

(defthm bvchop-of-nth-becomes-bv-array-read
  (implies (and (all-unsigned-byte-p size data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp n))
           (equal (bvchop size (nth n data))
                  (if (< n (len data))
                      (bv-array-read size (len data) n data)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;list::nth-with-large-index
                                   )
                                  (nth-of-bv-array-write-becomes-bv-array-read
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthmd bvchop-of-nth-becomes-bv-array-read2
  (implies (and ;(all-unsigned-byte-p size data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp n))
           (equal (bvchop size (nth n data))
                  (if (< n (len data))
                      (bv-array-read size (len data) n data)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

;fixme just always turn < of bvs into bvlt - big change?
(defthm <-of-bvmult-6-2-44
  (equal (< (BVMULT '6 '2 FARG0) '44)
         (bvlt 6 (BVMULT '6 '2 FARG0) '44))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  ( ;<-becomes-bvlt
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   )))))

(defthm bvlt-of-bvmult-6-2-44
  (equal (BVLT '6 (BVMULT '6 '2 x) '44)
         (BVLT 5 x 22))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult bvchop-when-i-is-not-an-integer)
                                  ( ;<-becomes-bvlt
;                                   *-OF-2-BECOMES-BVMULT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   )))))

(defthm bvlt-of-bvmult-6-2-43
  (equal (BVLT '6 (BVMULT '6 '2 x) '43)
         (BVLT 5 x 22))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult bvchop-when-i-is-not-an-integer)
                                  ( ;<-becomes-bvlt
;                                   *-OF-2-BECOMES-BVMULT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   )))))

;can loop?  other rules turn bvmult of 0 into bvcat
(defthmd bvmult-of-bvcat-arg2
  (implies (and (natp lowsize)
                ;(natp lowval)
                (natp highsize)
                ;;(natp highval)
                )
           (equal (bvmult size (bvcat highsize highval lowsize lowval) x)
                  (bvmult size (bvplus (+ highsize lowsize)
                                       (bvchop lowsize lowval)
                                       (bvmult (+ lowsize highsize)
                                               (expt 2 lowsize)
                                               highval))
                          x)))
  :hints (("Goal" :in-theory (e/d (bvcat-rewrite) (BVMULT-OF-EXPT2)))))

;can loop?  other rules turn bvmult of 0 into bvcat
(defthmd bvmult-of-bvcat-arg3
  (implies (and (natp lowsize)
                ;(natp lowval)
                (natp highsize)
                ;;(natp highval)
                )
           (equal (bvmult size x (bvcat highsize highval lowsize lowval))
                  (bvmult size x
                          (bvplus (+ highsize lowsize)
                                  (bvchop lowsize lowval)
                                  (bvmult (+ lowsize highsize)
                                          (expt 2 lowsize)
                                          highval)))))
  :hints (("Goal" :in-theory (e/d (bvcat-rewrite) (BVMULT-OF-EXPT2)))))

(defthm bvplus-of-bvmult-tighten-7-1-6-2
  (equal (BVPLUS 7 1 (BVMULT 6 2 x))
         (BVPLUS 6 1 (BVMULT 6 2 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-of-sum-cases
                                        bvchop-when-i-is-not-an-integer
                                        bvmult
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

(defthm bvlt-of-bvplus-6-1-44
  (implies (not (equal 63 (bvchop 6 x)))
           (equal (BVLT '6 (BVPLUS '6 '1 x) '44)
                  (BVLT '6 x '43)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-of-sum-cases
                                        bvchop-when-i-is-not-an-integer
                                        bvmult
                                        BVCHOP-WHEN-TOP-BIT-1)
                                  ( ;<-becomes-bvlt
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS ;fixme
                                   PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   SLICE-OF-+
                                   GETBIT-OF-+ ;looped
                                   )))))

;; (defthm equal-of-bvmult-2-k
;;   (implies (and (syntaxp (and (quotep k)
;;                               (quotep k2)))
;;                 (equal k2 3))
;;            (equal (equal k (bvmult 6 k2 x))
;;                   (and (unsigned-byte-p 6 k)
;;                        (integerp (/ k k2))
;;                        (equal (bvchop 5 x) (/ k k2)))))
;;   :hints (("Goal" :in-theory (enable bvmult bvchop-when-i-is-not-an-integer))))


;gen the 2..
(defthm equal-of-bvmult-2-impossible-value
  (implies (and (syntaxp (quotep k))
                (not (equal 0 (getbit 0 k)))
                (natp n))
           (equal (equal k (bvmult n 2 x))
                  nil))
  :hints (("Goal" :in-theory (enable bvmult))))

(in-theory (disable SBVDIV)) ;move up!

;gen! rename!
(defthm sbvlt-when-negative
  (implies (EQUAL 1 (GETBIT 31 x))
           (equal (SBVLT 32 15 x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable sbvlt logext))))

(defthm sbvlt-of-minus-1-when-negative
  (implies (and (syntaxp (want-to-weaken (sbvlt 32 x 4294967295)))
                (equal 1 (getbit 31 x)))
           (equal (sbvlt 32 x *minus-1*)
                  (not (equal (bvchop 32 x) *minus-1*))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :hints (("Goal" :in-theory (enable sbvlt logext))))

(in-theory (disable BVMULT-OF-2-GEN)) ;looped with BVPLUS-OF-BVCAT-HACK6-GEN-LOW-OPEN - we don't want to turn mult into cat in a plus context

(defthm bvmult-of-bvplus-4-4-3-4
  (equal (BVMULT 4 4 (BVPLUS 3 4 x))
         (BVMULT 4 4 x))
  :hints (("Goal" :in-theory (e/d (BVMULT bvchop-when-i-is-not-an-integer) (TIMES-OF-BVMULT-4)))))

(in-theory (enable SBVLT-REWRITE)) ;trying..

(defthm bvlt-of-bvmult-cancel-5-5-4-12
  (equal (BVLT 5 (BVMULT '5 '4 x) 12)
         (BVLT 3 x 3))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult bvchop-when-i-is-not-an-integer)
                                  ( ;<-becomes-bvlt
;                                   *-OF-2-BECOMES-BVMULT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   )))))

(defthm equal-1-becomes-bvlt
  (implies (and (syntaxp (want-to-weaken (equal 1 x)))
                (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (not (equal x 0))
                (natp xsize)
                (force (unsigned-byte-p-forced xsize x))
                )
           (equal (equal 1 x)
                  (not (bvlt xsize 1 x))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil nil nil 0 nil)))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult bvchop-when-i-is-not-an-integer
                                        unsigned-byte-p-forced)
                                  ( ;<-becomes-bvlt
;                                   *-OF-2-BECOMES-BVMULT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG1
                                   <-OF-BVPLUS-BECOMES-BVLT-ARG2
                                   )))))


(local (in-theory (disable <-BECOMES-BVLT <-BECOMES-BVLT-alt))) ;move up

;replaced these in favor of the non-dag ones:
;; (defthmd bvlt-when-bvchop-known-subst-dag
;;   (implies (and (equal free (bvchop size x)) ;order here?
;;                 (syntaxp (quotep free))
;;                 (natp size))
;;            (equal (bvlt size y x)
;;                   (bvlt size y free)))
;;   :hints (("Goal" :use (:instance bvlt-when-bvchop-known-subst))))

;; (defthmd bvlt-when-bvchop-known-subst-alt-dag
;;   (implies (and (syntaxp (not (quotep x)))    ;new (may help prevent loops?)
;;                 (equal free (bvchop size x)) ;note that the constant comes first
;;                 (syntaxp (quotep free))
;;                 (natp size))
;;            (equal (bvlt size x y)
;;                   (bvlt size free y)))
;;   :hints (("Goal" :use (:instance bvlt-when-bvchop-known-subst-alt))))

(defthm equal-of-bvif-hack
  (implies (posp size)
           (equal (equal (bvif size test '1 '0) '0)
                  (not test)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm equal-of-bvif-hack2
  (implies (posp size)
           (equal (equal (bvif size test '0 '1) '0)
                  (bool-fix test)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvchop-equal-when-bvlt-hack
  (implies (and (BVLT 31 free x) ;syntaxp??
                (bvle 31 0 free)) ;weaken
           (equal (equal (bvchop 31 x) 0)
                  nil)))

(defthm bvchop-equal-when-bvlt-hack-32
  (implies (and (BVLT 31 free x) ;syntaxp??
                (bvle 31 0 free)) ;weaken
           (equal (equal (bvchop 32 x) 0)
                  nil))
  :hints (("Goal" :in-theory (disable bvchop-equal-when-bvlt-hack)
           :use (:instance bvchop-equal-when-bvlt-hack))))

(defthmd not-sbvlt-of-0-when-sbvlt-free
  (implies (and (sbvlt 32 free x)
                (sbvle 32 0 free) ;weaken
                )
           (not (sbvlt 32 x 0)))
  :hints (("Goal" :in-theory (enable sbvlt LOGEXT-BECOMES-BVCHOP-WHEN-POSITIVE))))

;replace
(defthm sbvlt-false-from-bound-better
  (implies (and (syntaxp (quotep k))
                (sbvlt 32 x free)
                (syntaxp (quotep free))
                (<= (logext 32 free) (logext 32 k)) ;this will get computed
                )
           (equal (sbvlt 32 k x)
                  nil))
  :hints (("Goal" :in-theory (e/d (sbvlt) (SBVLT-REWRITE)))))

(defthmd sbvlt-false-from-bound-dag
  (implies (and (syntaxp (quotep k))
                (sbvlt 32 x free)
                (syntaxp (quotep free))
                (<= (logext 32 free) (logext 32 k)))
           (equal (sbvlt 32 k x) nil))
  :hints (("Goal" :use (:instance sbvlt-false-from-bound-better))))

;; or just go to bvlt?
;; (thm
;;  (equal (sbvlt '32 (bvplus '32 k x) j)
;;         (sbvlt '32 x (bvminus 32 j k)))
;;  :hints (("Goal" :in-theory (e/d () (sbvlt-rewrite)))))


;this is the loop that zeros out the low 16 bytes of the array...
;interesting... need to generalize..
;add this to pattern detection code? firstn elements all the same, where n is related to a loop index?
;also observe that all other elements are unchanged?
;; (thm
;;  (implies t;(equal (nth 15 (nth 1 arg)) 0)
;;           (equal (nth 15 (nth 1 (sha1-loop-23 arg))) 0))
;;  :hints (("Goal" :in-theory (e/d (SHA1-LOOP-23) (SHA1-LOOP-23-EXIT-TEST)))))


;; ;loops!
;; (defthmd sbvlt-becomes-bvlt-better
;;   (implies (and (sbvle 32 0 x)
;;                 (sbvle 32 0 y))
;;            (equal (sbvlt 32 x y)
;;                   (bvlt 31 x y)))
;;   :hints (("Goal" :in-theory (enable sbvlt LOGEXT-BECOMES-BVCHOP-WHEN-POSITIVE))))

(defthmd bvlt-add-to-both-sides-constant-lemma-alt-dag
  (implies (and (syntaxp (quotep k2))
                (syntaxp (quotep k1))
                (syntaxp (quotep size))
;                (integerp x)
                (integerp k2)
                (integerp k1)
                (natp size))
           (equal (bvlt size (bvplus size k1 x) k2)
                  (if (if (equal 0 (bvchop size k1)) ;should just get computed
                          t
                        (bvlt size x (bvuminus size k1)))
                      (if (bvlt size k2 k1) ;should just get computed
                          nil
                        (bvlt size x (bvplus size k2 (bvuminus size k1))))
                    (if (bvlt size k2 k1) ;should just get computed
                        (bvlt size x (bvplus size k2 (bvuminus size k1)))
                      t))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma-alt)
           :in-theory (disable bvlt-add-to-both-sides-constant-lemma-alt))))

(defthm unsigned-byte-p-of-plus-of-minus-1
  (implies (unsigned-byte-p size x)
           (equal (unsigned-byte-p size (binary-+ '-1 x))
                  (not (equal 0 x))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p bvlt) (<-becomes-bvlt <-becomes-bvlt-alt)))))


;gen the 1
(defthm plus-becomes-bvplus-free
  (implies (and (unsigned-byte-p xsize x)
                (posp xsize))
           (equal (+ 1 x)
                  (bvplus (+ 1 xsize) 1 x)))
  :hints (("Goal" :in-theory (e/d (UNSIGNED-BYTE-P-FORCED)( PLUS-BECOMES-BVPLUS-ARG1-FREE))
           :use (:instance PLUS-BECOMES-BVPLUS (y 1) (ysize 1)))))

;gen!
(defthm bvmod-by-8
  (equal (bvmod 31 x 8)
         (bvchop 3 x))
  :hints (("Goal" :in-theory (e/d (bvmod bvchop) ()))))

;gen!
(defthm bvplus-10-shrink-to-9
  (implies (and (unsigned-byte-p freesize x)
                (equal freesize 9) ;gen to anything < 10
                (not (equal x 511))
                )
           (equal (BVPLUS 10 1 x)
                  (BVPLUS freesize 1 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus GETBIT-OF-+ BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                                                        PLUS-BECOMES-BVPLUS
                                                        PLUS-BECOMES-BVPLUS-FREE
                                                        PLUS-BECOMES-BVPLUS-ARG2-FREE)))))


(defthmd <-becomes-bvlt-alt-dag
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (unsigned-byte-p free k))
           (equal (< x k)
                  (bvlt free x k)))
  :hints (("Goal" :use (:instance <-becomes-bvlt-alt)
           :in-theory (disable <-becomes-bvlt-alt))))

;gen the size!
(defthm bvlt-of-slice-3-2
  (implies (equal k 1) ;gen!
           (equal (bvlt 2 k (slice 3 2 x))
                  (bvle 4 (* 4 (+ 1 k)) x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvlt bvchop-of-sum-cases slice-bound-lemma-gen slice-bound-lemma-gen2)
                                  (anti-bvplus GETBIT-OF-+ bvlt-of-plus-arg1 bvlt-of-plus-arg2 plus-becomes-bvplus
                                               plus-becomes-bvplus-free
                                               )))))

(defthm bvplus-of-nth-becomes-bv-array-read-arg2
  (implies (and (all-unsigned-byte-p size data) ;;not logically necessary but helps
                (< n (len data))
                (natp n))
           (equal (bvplus size arg1 (nth n data))
                  (bvplus size arg1 (bv-array-read size (len data) n data))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2
                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ)))))



(local (in-theory (disable bvchop-of-nth-becomes-bv-array-read2)))

(DEFTHM EQUAL-OF-NTH-AND-BV-ARRAY-READ-better
  (IMPLIES (AND (EQUAL LEN (LEN X)) ;weaken
                (UNSIGNED-BYTE-P SIZE (nth n X))
                (NATP N)
                (< N LEN))
           (EQUAL (EQUAL (NTH N X) (BV-ARRAY-READ SIZE LEN N X))
                  T))
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D (BV-ARRAY-READ-opener ;LIST::NTH-WITH-LARGE-INDEX
          )
         (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
          NTH-BECOMES-BV-ARRAY-READ2
          BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ)))))

(DEFTHM EQUAL-OF-NTH-AND-BV-ARRAY-READ-ALT-better
  (IMPLIES (AND (EQUAL LEN (LEN X)) ;weaken
                (UNSIGNED-BYTE-P SIZE (nth n X))
                (NATP N)
                (< N LEN))
           (EQUAL (EQUAL (BV-ARRAY-READ SIZE LEN N X)
                         (NTH N X))
                  T))
  :HINTS
  (("Goal"
    :USE (:INSTANCE EQUAL-OF-NTH-AND-BV-ARRAY-READ-better)
    :IN-THEORY (e/d ()( EQUAL-OF-NTH-AND-BV-ARRAY-READ-better)))))


;move
(defthmd bvmod-of-power-of-2-helper
  (implies (and (equal k (expt 2 m))
                (< m n)
                (natp n)
                (natp m))
           (equal (bvmod n x k)
                  (bvchop m x)))
  :hints (("Goal" :in-theory (e/d (bvmod bvchop) ()))))

;move
(defthm bvmod-of-power-of-2
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 (integer-length k))))
                (< (+ -1 (integer-length k)) n) ;gen?
                (natp n)
                (natp k))
           (equal (bvmod n x k)
                  (bvchop (+ -1 (integer-length k)) x)))
  :hints (("Goal" :use (:instance bvmod-of-power-of-2-helper
                                  (m (+ -1 (integer-length k)))))))

;rename
;do we really want to introduce bool-to-bit?
;shouldn't the bitxor with 1 become bitnot?
(defthm bvif-t-x-and-bitxor-1-x
  (equal (bvif 1 test x (bitxor 1 x))
         (bitnot (bitxor x (bool-to-bit test))))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;rename
;do we really want to introduce bool-to-bit?
;shouldn't the bitxor with 1 become bitnot?
(defthm bvif-t-bitxor-1-x-and-x
  (equal (bvif 1 test (bitxor 1 x) x)
         (bitxor x (bool-to-bit test)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;todo
(defthmd bvuminus-equal-constant-alt-dag
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep size))
                (natp size)
                (integerp x))
           (equal (equal (bvuminus size x) k)
                  (and (unsigned-byte-p size k)
                       (equal (bvuminus size k)
                              (bvchop size x)))))
  :hints (("Goal"
           :use (:instance bvuminus-equal-constant))))


;gen
(defthm bvdiv-of-bvplus-minus-5
  (implies (and (bvlt 31 4 x)
                ;(< 2 size)
                (natp x)
                ;(integerp size)
                )
           (equal (bvdiv '31 (bvplus '31 '2147483643 x) '4)
                  (bvminus 31
                           (bvdiv '31 (bvplus '31 '2147483647 x) '4)
                           1)))
  :hints (("Goal"
           :in-theory (e/d (BVLT-ADD-TO-BOTH-SIDES-CONSTANT-LEMMA-ALT)
                           ( BVDIV-OF-SUBTRACT-4-BY-4))
           :use (:instance BVDIV-OF-SUBTRACT-4-BY-4
                           (size 31)
                           (x (bvplus '32 '2147483647 x))))))



;gen!
(defthm slice-0-when-bvchop-less-than
  (IMPLIES (and (< (BVCHOP 31 X) free)
                (<= free 4))
           (EQUAL (SLICE 30 2 X)
                  0))
  :hints (("Goal" :use (:instance SLICE-TOO-HIGH-IS-0 (x (bvchop 31 x)) (high 30) (low 2)))))

(defthm bvdiv-equal-0-rewrite
  (equal (equal 0 (bvdiv '31 x '4))
         (bvlt 31 x 4))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT <-BECOMES-BVLT-alt)))))

(defthm bvdiv-equal-0-rewrite-alt
  (equal (equal (bvdiv 31 x 4) 0)
         (bvlt 31 x 4))
  :hints (("Goal" :use (:instance bvdiv-equal-0-rewrite)
           :in-theory (disable bvdiv-equal-0-rewrite))))

;move
;reorder lhs?
;use IF in conclusion?
(defthm equal-of-myif-same
  (implies (booleanp test)
           (equal (equal (myif test x y) x)
                  (or test
                      (equal y x)))))

;helps in the weird case where the test is a constant but we haven't simplified the myif (happens when we don't simplify the dag after merging nodes)
(defthm equal-of-myif-same-1
  (equal (equal x (myif test x y))
         (or (bool-fix test) (equal x y)))
  :hints (("Goal" :in-theory (enable myif))))

;helps in the weird case where the test is a constant but we haven't simplified the myif (happens when we don't simplify the dag after merging nodes)
(defthm equal-of-myif-same-2
  (equal (equal x (myif test y x))
         (or (not test) (equal x y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm equal-of-myif-same-1-alt
  (equal (equal (myif test x y) x)
         (or (bool-fix test) (equal x y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm equal-of-myif-same-2-alt
  (equal (equal (myif test y x) x)
         (or (not test) (equal x y)))
  :hints (("Goal" :in-theory (enable myif))))


(defthmd bvlt-of-max-when-bvlt-constant-dag
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 size)))
                (bvlt size x free)
                ;(natp size)
                )
           (equal (bvlt size x k)
                  t)))

;maybe always turn UNSIGNED-BYTE-P into bvlt if the argument is wider
(defthm unsigned-byte-p-of-bvplus-wider-9-10
  (equal (unsigned-byte-p 9 (bvplus 10 k x))
         (bvlt 10 (bvplus 10 k x) (expt 2 9)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt
                                                         <-of-bvplus-becomes-bvlt-arg1)))))





(defthmd slice-when-bvchop-small
  (implies (and (< (bvchop m x) (expt 2 n))
                (natp n)
                (natp m))
           (equal (slice (+ -1 m) n x)
                  0))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

(defthmd bvchop-expand
  (implies (and (< (bvchop m x) (expt 2 n))
                (<= n m)
                (natp n)
                (natp m))
           (equal (bvchop n x)
                  (bvchop m x)))
  :hints (("Goal" :in-theory (enable slice-when-bvchop-small)
           :use (:instance REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2
                           (x (bvchop n x))
                           (x-size n)
                           (y (bvchop m x))
                           (y-size m)))))


;gen to more than 1 extra bit
(defthmd bvplus-expand-when-no-carry
  (implies (and (bvlt m (bvplus m x z) (expt 2 n))
                (< n m) ;gen
                (natp n)
                (natp m)
                (integerp x)
                (integerp z))
           (equal (BVPLUS n z x)
                  (BVPLUS m z x)))
  :hints (("Goal"
           :use (:instance bvchop-expand (x (+ x z)))
           :in-theory (e/d (bvplus bvlt UNSIGNED-BYTE-P)
                                  (anti-bvplus GETBIT-OF-+
                                   PLUS-BECOMES-BVPLUS
                                   BVLT-OF-PLUS-ARG2
                                   BVLT-OF-PLUS-ARG1
                                   SLICE-OF-+ ;SLICE-OF-BVCHOP-LOW-GEN-BETTER ;looped

                                   )))))

;when do we want to do something like this?
;what can this loop with?
;this is a generalization of the associativity rule and so should not loop?
(defthm bvplus-of-bvplus-narrower-when-no-carry
  (implies (and (< n m) ;(equal n+1 (+ 1 n))
                (bvlt m (bvplus m x z) (expt 2 n))
                (integerp x)
                (integerp z)
                (natp n))
           (equal (bvplus m (bvplus n z x) y)
                  (bvplus m z (bvplus m x y))))
  :hints (("Goal" :use (:instance bvplus-expand-when-no-carry)
           :in-theory (disable bvplus-expand-when-no-carry))))

(defthm bvplus-of-bvplus-narrower-quoteps
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y))
                (syntaxp (quotep m))
                (< n m)
                (bvlt m (bvplus m y z) (expt 2 n))
                (integerp x)
                (integerp y)
                (integerp z)
                (natp n))
           (equal (bvplus m x (bvplus n y z))
                  (bvplus m z (bvplus m x y))))
  :hints (("Goal" :use (:instance bvplus-of-bvplus-narrower-when-no-carry
                                  (x y) (y x))
           :in-theory (disable bvplus-of-bvplus-narrower-when-no-carry))))

(defthm equal-of-bvif
  (equal (equal x (bvif size test a b))
         (boolif test (equal x (bvchop size a)) (equal x (bvchop size b))))
  :hints (("Goal" :in-theory (enable bvif
                                     boolor ;why?
                                     ))))

(defthm equal-of-bvif-alt
  (equal (equal (bvif size test a b) x)
         (boolif test (equal x (bvchop size a))
                 (equal x (bvchop size b))))
  :hints (("Goal" :in-theory (enable bvif boolor))))



(defthm bvplus-of-bvuminus-same-gen
  (implies (and (unsigned-byte-p size x)
                (< size n)
                (natp size)
                (integerp n))
           (equal (bvplus n (bvuminus size x) x)
                  (if (equal 0 (bvchop size x))
                      0
                    (expt 2 size))))
  :hints (("Goal" :in-theory (e/d (bvplus bvuminus bvminus
                                          unsigned-byte-p-forced)
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   bvminus-becomes-bvplus-of-bvuminus
                                   plus-becomes-bvplus-arg1-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   )))))

(defthm bvlt-of-bvplus-1-when-not-bvlt
  (implies (and (not (bvlt size y x))
                (natp size))
           (equal (bvlt size y (bvplus size 1 x))
                  (and (equal (bvchop size x) (bvchop size y))
                       (not (equal (+ -1 (expt 2 size)) (bvchop size x)))
                       )))
  :hints (("Goal" :in-theory (e/d (BVCHOP-OF-SUM-CASES
                                   bvlt
                                   bvplus bvuminus bvminus
                                   unsigned-byte-p-forced)
                                  (<-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   ;TRIM-TO-N-BITS-META-RULE-FOR-SLICE ;looped!
                                   SLICE-OF-+
                                   anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   bvminus-becomes-bvplus-of-bvuminus
                                   plus-becomes-bvplus-arg1-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   )))))

;gross?
;gen!
(defthm bvplus-of-bvuminus-tighten-10-to-9
  (implies (and (not (bvlt 9 y x))
                (unsigned-byte-p 9 y))
           (equal (bvplus 10 (bvuminus 9 x) y)
                  (if (equal 0 (bvchop 9 x))
                      y ;(bvchop 10 y)
                    (bvplus 10 512 (bvplus 9 (bvuminus 9 x) y)))))
  :hints (("Goal" :in-theory (e/d (BVCHOP-OF-SUM-CASES
                                   bvlt
                                   bvplus bvuminus bvminus
                                   unsigned-byte-p-forced)
                                  (<-BECOMES-BVLT-FREE
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt
                                   ;TRIM-TO-N-BITS-META-RULE-FOR-SLICE ;looped!
                                   SLICE-OF-+
                                   anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   bvminus-becomes-bvplus-of-bvuminus
                                   plus-becomes-bvplus-arg1-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   )))))

;; 0=y-x  --> x=y
(defthm equal-of-0-and-bvplus-of-bvuminus
  (equal (equal 0 (bvplus size (bvuminus size x) y))
         (equal (bvchop size x)
                (bvchop size y)))
  :hints (("Goal"
           :cases ((natp size))
           :in-theory (e/d (bvchop-of-sum-cases
                                   bvlt
                                   bvplus bvuminus bvminus
                                   unsigned-byte-p-forced)
                                  (<-becomes-bvlt-free
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   ;trim-to-n-bits-meta-rule-for-slice ;looped!
                                   slice-of-+
                                   anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   bvminus-becomes-bvplus-of-bvuminus
                                   plus-becomes-bvplus-arg1-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   )))))

(defthm equal-of-0-and-bvplus-of-bvuminus-alt
  (equal (equal 0 (bvplus size y (bvuminus size x)))
         (equal (bvchop size x)
                (bvchop size y)))
  :hints (("Goal" :use (:instance equal-of-0-and-bvplus-of-bvuminus)
           :in-theory (disable equal-of-0-and-bvplus-of-bvuminus))))



;gen the k (i.e., the -1)?
(defthm bvplus-of-minus-1-tighten
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< xsize size2)
                (equal k (+ -1 (expt 2 size2)))
                (posp size2)
                (unsigned-byte-p-forced xsize x))
           (equal (bvplus size2 k x)
                  (if (equal 0 x)
                      k
                    (bvplus xsize (bvchop xsize -1) x))))
  :hints (("Goal" :in-theory (e/d (bvchop-of-sum-cases
                                   bvlt
                                   bvplus bvuminus bvminus
                                   unsigned-byte-p-forced)
                                  (<-becomes-bvlt-free
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   ;trim-to-n-bits-meta-rule-for-slice ;looped!
                                   slice-of-+
                                   anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   bvminus-becomes-bvplus-of-bvuminus
                                   plus-becomes-bvplus-arg1-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   )))))



(defthmd bvlt-when-unsigned-byte-p-better-helper
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (< free size)
                (natp size)
                (natp free)
                (bvle size (expt 2 free) k) ;this case
                )
           (equal (bvlt size x k)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus
                                        GETBIT-TOO-HIGH
                                        GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                        UNSIGNED-BYTE-P
                                        bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   )))))

(defthmd slice-when-bvchop-bound
  (implies (and (< (bvchop size k) (expt 2 free))
                (natp free)
                (natp size)
                (< free size))
           (equal (slice (+ -1 size) free k)
                  0))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

;corresponding theorem about mod?
(defthm bvchop-when-<-tighten
  (implies (and (< (bvchop size k) (expt 2 free))
                (< free size)
                (natp free)
                (natp size))
           (equal (bvchop size k)
                  (bvchop free k)))
  :hints (("Goal"
           :use (:instance split-with-bvcat
                           (hs (- size free))
                           (ls free)
                           (x k))
           :in-theory (e/d (slice-when-bvchop-bound)
                           (BVCAT-SLICE-SAME ;PLUS-CANCEL-HACK-LEMMA
                            BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE)))))

;fixme - why the bvchops?
(DEFTHMd BVLT-TIGHTEN-gen
  (IMPLIES (AND (UNSIGNED-BYTE-P FREE (bvchop size x))
                (< FREE SIZE)
                (UNSIGNED-BYTE-P FREE (bvchop size k))
                (NATP FREE)
                (NATP SIZE))
           (EQUAL (BVLT SIZE K X)
                  (BVLT FREE K X)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BVLT UNSIGNED-BYTE-P)
                    (PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                     BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                     <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                     <-OF-BVPLUS-BECOMES-BVLT-ARG1
                     <-OF-BVPLUS-BECOMES-BVLT-ARG2
                     ANTI-BVPLUS GETBIT-OF-+ PLUS-BECOMES-BVPLUS
                     BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                     SLICE-OF-+ GETBIT-OF-+)))))

;drop the special case above?
;get rid of the other rule?
(defthm bvlt-when-unsigned-byte-p-better
  (implies (and (syntaxp (quotep k)) ;drop?
                (unsigned-byte-p free x)
                (< free size)
                (natp size)
                (natp free)
                )
           (equal (bvlt size x k)
                  (if (bvle size (expt 2 free) k) ;this will usually get computed
                      t
                    (bvlt free x k))))
    :HINTS
  (("Goal"
    :IN-THEORY (E/D (BVLT UNSIGNED-BYTE-P)
                    (PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                     BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                     <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                     <-OF-BVPLUS-BECOMES-BVLT-ARG1
                     <-OF-BVPLUS-BECOMES-BVLT-ARG2
                     ANTI-BVPLUS GETBIT-OF-+ PLUS-BECOMES-BVPLUS
                     BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                     SLICE-OF-+ GETBIT-OF-+)))))

(defthm equal-of-bvmult-5-4-16
  (equal (equal 16 (bvmult 5 4 x))
         (equal (bvchop 3 x) 4))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvlt-when-slice-not-equal
  (implies (and (syntaxp (want-to-weaken (BVLT 5 16 x)))
                (NOT (EQUAL 4 (SLICE 4 2 x))))
           (equal (BVLT 5 16 x)
                  (BVLT 5 15 x))))

;gen the 4
(defthm equal-of-0-and-bvmult
  (implies (and (natp size)
                (<= 3 size))
           (equal (equal 0 (bvmult size 4 x))
                  (equal 0 (bvchop (- size 2) x))))
  :hints (("Goal" :in-theory (enable bvmult))))

(in-theory (disable sbvlt-becomes-bvlt))

(defthm unsigned-byte-p-of-bvplus-2-3-4
  (implies (integerp x)
           (equal (UNSIGNED-BYTE-P 2 (BVPLUS 3 4 x))
                  (bvle 3 4 x)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BVLT UNSIGNED-BYTE-P bvplus
                          BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                          bvchop-of-sum-cases)
                    (PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                     BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                     <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                     <-OF-BVPLUS-BECOMES-BVLT-ARG1
                     <-OF-BVPLUS-BECOMES-BVLT-ARG2
                     ANTI-BVPLUS GETBIT-OF-+ PLUS-BECOMES-BVPLUS
                     BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                     SLICE-OF-+ GETBIT-OF-+)))))

(defthm bvlt-of-bvuminus-3-3-4
  (implies (integerp x)
           (equal (bvlt 3 (bvuminus 3 x) 4)
                  (or (equal 0 (bvchop 3 x))
                      (bvlt 3 4 x))))
  :hints
  (("Goal"
    :in-theory (e/d (bvlt unsigned-byte-p bvplus
                          bvuminus bvminus
                          bvchop-reduce-when-top-bit-known
                          bvchop-of-sum-cases)
                    (plus-1-and-bvchop-becomes-bvplus
                     <-of-bvuminus-becomes-bvlt ;yuck?
                     bvminus-becomes-bvplus-of-bvuminus
                     <-becomes-bvlt <-becomes-bvlt-alt
                     <-of-bvplus-becomes-bvlt-arg1
                     <-of-bvplus-becomes-bvlt-arg2
                     anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                     bvlt-of-plus-arg1 bvlt-of-plus-arg2
                     slice-of-+ getbit-of-+)))))

;newly disabled
;make a bind-free version
(defthmd +-of-minus-1-and-bv2
  (implies (unsigned-byte-p free x)
           (equal (+ -1 x)
                  (if (equal x 0)
                      -1
                    (bvplus free -1 x))))
  :hints
  (("Goal" :in-theory
    (e/d (bvplus bvchop-of-sum-cases)
         (anti-bvplus getbit-of-+ bvlt-of-plus-arg1 bvlt-of-plus-arg2
                      plus-becomes-bvplus)))))

(defthmd +-of-minus-1-and-bv
  (implies (unsigned-byte-p 32 x) ;the 32 is gross
           (equal (+ -1 x)
                  (if (equal x 0)
                      -1
                    (bvplus 32 -1 x))))
  :hints (("Goal" :use (:instance +-OF-MINUS-1-AND-BV2 (free 32))
           :in-theory (disable +-OF-MINUS-1-AND-BV2))))


(defthm unsigned-byte-p-of-bvplus-1
  (implies (unsigned-byte-p 31 x)
           (equal (unsigned-byte-p 31 (bvplus 32 1 x))
                  (not (equal (bvchop 31 x)
                              (+ -1 (expt 2 31))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases)
                                  (anti-bvplus GETBIT-OF-+ BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2 PLUS-BECOMES-BVPLUS
                                               PLUS-BECOMES-BVPLUS-FREE)))))


(defthm unsigned-byte-p-of-bvplus-minus-1
  (implies (unsigned-byte-p 31 x)
           (equal (unsigned-byte-p 31 (bvplus 32 4294967295 x))
                  (not (equal 0 x))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases)
                                  (anti-bvplus GETBIT-OF-+ bvlt-of-plus-arg1 bvlt-of-plus-arg2 plus-becomes-bvplus
                                               plus-becomes-bvplus-free)))))

(defthm equal-of-minval-and-bvplus-of-bvminus
  (implies (unsigned-byte-p 31 x)
           (equal (equal 2147483648 (bvplus 32 x (bvuminus 31 y)))
                  (if (equal 0 (bvchop 31 y))
                      (equal 2147483648 (bvchop 32 x))
                    (equal (bvchop 31 x) (bvchop 31 y)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases bvlt bvuminus bvminus)
                                  (anti-bvplus GETBIT-OF-+ bvlt-of-plus-arg1 bvlt-of-plus-arg2 plus-becomes-bvplus
                                               plus-becomes-bvplus-arg1-free
                                               plus-becomes-bvplus-free
                                               <-becomes-bvlt-free
                                               <-becomes-bvlt
                                               <-becomes-bvlt-alt
                                               bvminus-becomes-bvplus-of-bvuminus)))))

(defthm equal-of-minval-and-bvplus-of-bvminus-alt
  (implies (unsigned-byte-p 31 x)
           (equal (equal 2147483648 (bvplus 32 (bvuminus 31 y) x))
                  (if (equal 0 (bvchop 31 y))
                      (equal 2147483648 (bvchop 32 x))
                    (equal (bvchop 31 x) (bvchop 31 y)))))
  :hints (("Goal" :use (:instance equal-of-minval-and-bvplus-of-bvminus)
           :in-theory (disable equal-of-minval-and-bvplus-of-bvminus))))

(defthm nthcdr-of-bvplus-1
  (implies (and (not (equal 4294967295 (bvchop 32 n)))
                (natp n))
           (equal (nthcdr (bvplus '32 '1 n) x)
                  (cdr (nthcdr (bvchop 32 n) x))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases CDR-OF-NTHCDR)
                                  (anti-bvplus GETBIT-OF-+
                                   PLUS-BECOMES-BVPLUS
                                   BVLT-OF-PLUS-ARG1
                                   BVLT-OF-PLUS-ARG2)))))






(defthm equal-of-bvplus-and-bvplus-hack
  (implies (unsigned-byte-p 8 x)
           (equal (EQUAL (BVPLUS '8 '1 x) (BVPLUS '9 '1 x))
                  (not (equal 255 (bvchop 8 x)))))
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D
     (BVCHOP-OF-SUM-CASES
      BVLT BVPLUS
      BVUMINUS BVMINUS UNSIGNED-BYTE-P-FORCED)
     (<-BECOMES-BVLT-FREE <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                          ;TRIM-TO-N-BITS-META-RULE-FOR-SLICE
                          SLICE-OF-+ ANTI-BVPLUS GETBIT-OF-+ GETBIT-OF-+
                          BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                          PLUS-BECOMES-BVPLUS-ARG1-FREE
                          BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                          PLUS-BECOMES-BVPLUS
                          PLUS-BECOMES-BVPLUS-FREE)))))





(DEFTHMd BVLT-TIGHTEN-gen2
  (IMPLIES (AND (UNSIGNED-BYTE-P FREE x)
                (< FREE SIZE)
                (UNSIGNED-BYTE-P FREE k)
                (NATP FREE)
                (NATP SIZE))
           (EQUAL (BVLT SIZE K X)
                  (BVLT FREE K X)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BVLT UNSIGNED-BYTE-P)
                    (PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                     BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                     <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                     <-OF-BVPLUS-BECOMES-BVLT-ARG1
                     <-OF-BVPLUS-BECOMES-BVLT-ARG2
                     ANTI-BVPLUS GETBIT-OF-+ PLUS-BECOMES-BVPLUS
                     BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                     SLICE-OF-+ GETBIT-OF-+
                     <-BECOMES-BVLT-FREE)))))

;fffixme gross?!  we need to substitute!
;fffixme can this loop?
(defthm len-when-equal-take
  (implies (and (equal x (take free1 free2))
                (natp free1))
           (equal (len x)
                  free1)))

(defthm bvlt-of-bvplus-of-1-and-same
  (equal (BVLT '32 (BVPLUS '32 '1 x) x)
         (equal 4294967295 (bvchop 32 x)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BVLT UNSIGNED-BYTE-p bvplus bvchop-of-sum-cases)
                    (PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                     BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                     <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                     <-OF-BVPLUS-BECOMES-BVLT-ARG1
                     <-OF-BVPLUS-BECOMES-BVLT-ARG2
                     ANTI-BVPLUS GETBIT-OF-+ PLUS-BECOMES-BVPLUS
                     BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                     SLICE-OF-+ GETBIT-OF-+
                     <-BECOMES-BVLT-FREE)))))

; Matt K. mod 5/2016 (type-set bit for {1}):
; needed for +-of-bvplus-1-same-and-unary-minus
(local (in-theory (disable plus-becomes-bvplus-free)))

(defthm +-of-bvplus-1-same-and-unary-minus
  (implies (unsigned-byte-p 32 x)
           (equal (BINARY-+ (BVPLUS '32 '1 x) (UNARY-- x))
                  (if (equal 4294967295 (bvchop 32 x))
                      (unary-- x)
                    1)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BVLT UNSIGNED-BYTE-p bvplus bvchop-of-sum-cases)
                    (PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                     BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                     <-BECOMES-BVLT <-BECOMES-BVLT-ALT
                     <-OF-BVPLUS-BECOMES-BVLT-ARG1
                     <-OF-BVPLUS-BECOMES-BVLT-ARG2
                     ANTI-BVPLUS GETBIT-OF-+ PLUS-BECOMES-BVPLUS
                     BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
                     SLICE-OF-+ GETBIT-OF-+
                     <-BECOMES-BVLT-FREE)))))



;yuck!
(defthm car-when-equal-nthcdr
  (implies (and (equal x (nthcdr free free2))
                (natp free) ;drop?
                )
           (equal (car x)
                  (nth free free2))))



;; (thm
;;  (implies (and (<= (len x) n)
;;                (equal len (len x)))
;;           (equal (bv-array-read size len n x)
;;                  0))
;;  :hints (("Goal" :in-theory (e/d (bv-array-read LIST::NTH-WITH-LARGE-INDEX) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

;; (defthm equal-of-bvchop-of-nth-and-bv-array-read-better
;;   (implies (and (equal len (len x))
;;                 (natp n)
;;                 (< n len)
;;                 )
;;            (equal (equal (bvchop size (nth n x)) (bv-array-read size len n x))
;;                   t))
;;   :hints (("Goal" :use (:instance equal-of-bvchop-of-nth-and-bv-array-read)
;;            :in-theory (e/d (LIST::NTH-WITH-LARGE-INDEX) ( equal-of-bvchop-of-nth-and-bv-array-read)))))

;;remove -dag from BVLT-TIGHTEN-FREE-DAG, etc.



;redo the non-gen version?
(defthmd <-of-myif-arg1-gen
  (equal (< (myif test a b) k)
         (myif test (< a k) (< b k)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm slice-when-not-bvlt-gen
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep highsize))
                (syntaxp (quotep lowsize))
                (not (bvlt size2 x free)) ;this is bvle - make a bvlt version
                (equal size2 (+ 1 highsize)) ;gen?
                (syntaxp (quotep free))
                (< k (slice highsize lowsize free))
                (integerp highsize)
                (natp lowsize)
                (<= lowsize highsize))
           (equal (equal k (slice highsize lowsize x))
                  nil))
  :hints (("Goal"
           :use (:instance split-with-bvcat (hs (- (+ 1 highsize) lowsize)) (ls lowsize) (x (bvchop (+ 1 highsize) x)))
           :in-theory (e/d (bvlt unsigned-byte-p bvplus bvchop-of-sum-cases posp)
                           (BVCAT-OF-SLICE-AND-X-ADJACENT
                            plus-1-and-bvchop-becomes-bvplus
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1 bvlt-of-plus-arg2
                            slice-of-+ getbit-of-+
                            <-becomes-bvlt-free
                            bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite
                            bvcat-slice-same)))))

;do i need this?
;might be nicer to use an iff rule if the dag-rewriter supported that
(defthm not-of-append
  (equal (not (append x y))
         (and (not (true-list-fix x))
              (not y))))

(defthm bvmult-tighten-5-4-2
  (implies (unsigned-byte-p 2 x)
           (equal (BVMULT 5 4 x)
                  (BVMULT 4 4 x)))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvplus-tighten-1-3-2
  (implies (and (unsigned-byte-p 2 x)
                (not (equal 3 x)))
           (equal (BVPLUS 3 1 x)
                  (BVPLUS 2 1 x)))
  :hints (("Goal"
           :in-theory (e/d (bvlt unsigned-byte-p bvplus bvchop-of-sum-cases posp)
                           (plus-1-and-bvchop-becomes-bvplus
                            PLUS-BECOMES-BVPLUS-FREE
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1 bvlt-of-plus-arg2
                            slice-of-+ getbit-of-+
                            <-becomes-bvlt-free
                            bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite
                            bvcat-slice-same)))))

(defthm bvplus-hack-for-rc6
  (implies (and (unsigned-byte-p 2 x)
                (not (equal x 1)))
           (equal (BVPLUS 3 (BVPLUS 2 3 x)
                          (BVPLUS 2 1 (BVUMINUS 2 x)))
                  4))
  :hints (("Goal"
           :in-theory (e/d (bvlt unsigned-byte-p bvplus bvchop-of-sum-cases posp
                                 bvminus
                                 bvuminus)
                           (plus-1-and-bvchop-becomes-bvplus
                            PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                            PLUS-32-1-BVUMIUNS
                            PLUS-BECOMES-BVPLUS-FREE
                            +-OF-MINUS-1-AND-BV2
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1 bvlt-of-plus-arg2
                            slice-of-+ getbit-of-+
                            <-becomes-bvlt-free
                            bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite
                            bvcat-slice-same)))))



;add to the map theorems?
(defthm equal-of-nil-and-bvchop-list
  (equal (equal 'nil (bvchop-list n x))
         (not (consp x)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

;this spilts off the last element - we could instead choose the first element
(defthm take-of-bvplus-32-1
  (implies (UNSIGNED-BYTE-P 31 n)
           (equal (take (BVPLUS '32 '1 n) x)
                  (append (take n x)
                          (list (nth n x)))))
  :hints (("Goal"
           :in-theory (e/d ( bvplus bvchop-of-sum-cases posp
                                    bvminus ifix
                                    bvuminus
                                    equal-of-append)
                           (plus-1-and-bvchop-becomes-bvplus
                            PLUS-OF-4-AND-BV-BECOMES-BVPLUS
                            PLUS-32-1-BVUMIUNS
                            PLUS-BECOMES-BVPLUS-FREE
                            +-OF-MINUS-1-AND-BV2
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1 bvlt-of-plus-arg2
                            slice-of-+ getbit-of-+
                            <-becomes-bvlt-free
                            bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite
                            bvcat-slice-same)))))





;gen!
(defthmd bvlt-when-bit-2-1-hack
  (implies (and (equal free (getbit 2 x))
                (syntaxp (quotep free))
                (equal 1 free))
           (equal (bvlt 3 4 x)
                  (bvlt 2 0 x)))
  :hints (("Goal" :in-theory (e/d (bvlt BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-FREE)))))


(defthm bvlt-of-4-hack
  (implies (equal 1 (getbit 2 x))
           (equal (bvlt '3 x '4)
                  nil)))

(DEFTHM BVPLUS-MINUS-4-TIGHTEN-32-gen
  (IMPLIES (AND (UNSIGNED-BYTE-P free X)
                (posp free)
                (< 2 free)
                (< free 32)
                (BVLE free 4 X))
           (EQUAL (BVPLUS 32 4294967292 X)
                  (BVPLUS free -4 X)))
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D (BVLT bvplus bvchop-of-sum-cases)
         (anti-bvplus GETBIT-OF-+ <-BECOMES-BVLT <-BECOMES-BVLT-ALT <-OF-BVMULT-HACK

                      BVLT-OF-PLUS-ARG1
                      BVLT-OF-PLUS-ARG2
                      PLUS-BECOMES-BVPLUS
                      <-OF-BVPLUS-BECOMES-BVLT-ARG1
                      <-BECOMES-BVLT-FREE
                      <-OF-BVPLUS-BECOMES-BVLT-ARG2)))))

(defthm plus-of-minus-3-bv-5
  (implies (and (unsigned-byte-p 5 x) ;use bind-free
                (bvle 5 3 x))
           (equal (binary-+ '-3 x)
                  (bvplus 5 -3 x)))
  :hints
  (("Goal"
    :in-theory
    (e/d (bvlt bvplus bvchop-of-sum-cases)
         (anti-bvplus GETBIT-OF-+

                      bvlt-of-plus-arg1
                      bvlt-of-plus-arg2
                      plus-becomes-bvplus

                      <-becomes-bvlt <-becomes-bvlt-alt <-of-bvmult-hack
                      <-of-bvplus-becomes-bvlt-arg1
                      <-becomes-bvlt-free
                      <-of-bvplus-becomes-bvlt-arg2)))))



(defthm equal-0-top-slice-5-4-2
  (implies (unsigned-byte-p 5 x)
           (equal (equal 0 (slice 4 2 x))
                  (bvlt 5 x 4))))

(defthm UNSIGNED-BYTE-P-of-bvplus-smaller
  (equal (UNSIGNED-BYTE-P 3 (bvplus 4 x y))
         (bvlt 4 (bvplus 4 x y) 8))
  :hints (("Goal" :in-theory (enable bvlt UNSIGNED-BYTE-P integer-range-p))))



;gen!
;slow?
(defthm equal-of-bvplus-hack-for-sha1
  (implies (and (unsigned-byte-p '31 x6)
                (unsigned-byte-p '31 x30))
           (equal (equal x30 (bvplus '32 '2147483649 x6))
                  (and (equal 0 x30)
                       (equal 2147483647 x6))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus)))))

;gen the 4
(defthmd bvlt-4-when-unsigned-byte-p
  (implies (and (unsigned-byte-p size x)
                (< 2 size)
                (natp size))
           (equal (bvlt size x 4)
                  (unsigned-byte-p 2 x)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt <-of-bvmult-hack
                                                         <-of-bvplus-becomes-bvlt-arg1
                                                         <-becomes-bvlt-free
                                                         <-of-bvplus-becomes-bvlt-arg2
                                                         )))))

(DEFTHM BVLT-4-WHEN-UNSIGNED-BYTE-P-back
  (IMPLIES (AND (UNSIGNED-BYTE-P SIZE X)
                (< 2 SIZE)
                (NATP SIZE))
           (EQUAL (UNSIGNED-BYTE-P 2 X)
                  (BVLT SIZE X 4)))
  :hints (("Goal" :use (:instance bvlt-4-when-unsigned-byte-p))))

;general theory of this?
(defthm myif-of-myif-of-boolor-same
  (equal (myif test x (myif (boolor test y) z w))
         (myif test x (myif y z w)))
  :hints (("Goal" :in-theory (enable boolor myif))))

(defthm myif-of-myif-of-boolor-same2
  (equal (myif test (myif (boolor test test2) t2 e2) e1)
         (myif test t2 e1))
  :hints (("Goal" :in-theory (enable myif))))

(defthm nthcdr-of-myif-arg2
  (equal (nthcdr n (myif test x y))
         (myif test (nthcdr n x) (nthcdr n y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm bvlt-of-myif-arg3
  (equal (bvlt size z (myif test x y))
         (bvlt size z (bvif size test x y)))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm bvlt-of-myif-arg2
  (equal (bvlt size (myif test x y) z)
         (bvlt size (bvif size test x y) z))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm sbvlt-of-myif-arg2-safe
  (implies (and (syntaxp (and (quotep x) ;prevents explosion if x is a large term
                              ;;(or (quotep a) (quotep b))
                              (quotep size))))
           (equal (sbvlt size (myif test a b) x)
                  (boolif test
                          (sbvlt size a x)
                          (sbvlt size b x))))
  :hints (("Goal" :in-theory (enable myif))))

(defthm sbvlt-of-myif-arg3-safe
  (implies (and (syntaxp (and (quotep x) ;prevents explosion if x is a large term
                              ;;(or (quotep a) (quotep b))
                              (quotep size))))
           (equal (sbvlt size x (myif test a b))
                  (boolif test
                          (sbvlt size x a)
                          (sbvlt size x b))))
  :hints (("Goal" :in-theory (enable myif))))


;gen
;use polarity?
(defthm bvlt-of-31-and-2147483646
  (equal (bvlt 31 2147483646 x)
         (equal 2147483647 (bvchop 31 x)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt <-of-bvmult-hack
                                                         <-of-bvplus-becomes-bvlt-arg1
                                                         <-becomes-bvlt-free
                                                         <-of-bvplus-becomes-bvlt-arg2
                                                         )))))

(defthm equal-1-slice-4-2-5
  (implies (unsigned-byte-p 5 x)
           (equal (equal 1 (slice 4 2 x))
                  (and (bvle 5 4 x)
                       (bvlt 5 x 8)))))

(defthm unsigned-byte-p-of-bvplus-tighten
  (implies (and (< size size2)
                (integerp size2)
                (natp size))
           (equal (unsigned-byte-p size (bvplus size2 x y))
                  (bvlt size2 (bvplus size2 x y) (expt 2 size))))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt <-of-bvmult-hack
                                                         <-of-bvplus-becomes-bvlt-arg1
                                                         <-becomes-bvlt-free
                                                         <-of-bvplus-becomes-bvlt-arg2
                                                         )))))


(defthm bvlt-flip-top-bit-3-4
  (equal (bvlt 3 (bvplus 3 4 x) 4)
         (bvle 3 4 x)))

(defthm minus-<-minus-hack
  (equal (< -4 (- x))
         (< x 4)))

(defthm plus-of-1-and-bvplus
  (implies (natp size)
           (equal (+ 1 (BVPLUS SIZE X Y))
                  (bvplus (+ 1 size) 1 (BVPLUS SIZE X Y))))
  :hints (("Goal" :in-theory (e/d (bvplus)
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus)))))

(defthm cdr-of-nthcdr-of-bvplus
  (implies (natp size)
           (equal (CDR (NTHCDR (bvplus size x y) lst))
                  (NTHCDR (bvplus (+ 1 size) 1 (bvplus size x y)) lst)))
  :hints (("Goal" :in-theory (enable cdr-of-nthcdr))))

(defthm bvlt-max-63
  (equal (BVLT 6 Y 63)
         (not (equal (bvchop 6 y) 63)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT-ALT
                                          <-BECOMES-BVLT
                                          <-BECOMES-BVLT-free)))))


(defthm bvmod-cancel-hack-8-1-44-6-1
  (implies (and ;(unsigned-byte-p 8 x)
                (not (equal (bvchop 8 x) 255))
                (not (equal (bvchop 6 y) 63))
                ;(unsigned-byte-p 6 y)
                )
           (equal (equal (bvmod 6 (bvplus 6 1 y) 44) (bvmod 8 (bvplus 8 1 x) 44))
                  (equal (bvmod 6 (bvchop 6 y) 44) (bvmod 8 (bvchop 8 x) 44))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases)
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   )))))

(defthm bvmod-does-nothing-6-44
  (equal (equal x (bvmod '6 x '44))
         (and (unsigned-byte-p 6 x)
              (bvlt 6 x 44)))
  :hints (("Goal" :in-theory (e/d (bvmod bvlt)
                                  (<-becomes-bvlt-alt
                                   <-becomes-bvlt
                                   <-becomes-bvlt-free)))))

(defthm bvlt-of-mod-hack
  (implies (natp x)
           (equal (bvlt 6 43 (mod x 44))
                  nil))
  :hints (("Goal" :in-theory (e/d ( bvlt)
                                  (
                                   <-becomes-bvlt-alt
                                   <-becomes-bvlt
                                   <-becomes-bvlt-free)))))

(defthm minus-becomes-bv
  (implies (and (unsigned-byte-p free x)
                (unsigned-byte-p free y)
                (not (bvlt free x y))
                (natp free)
                )
           (equal (+ x (- y))
                  (bvplus free x (bvuminus free y))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT-FREE
                                    <-BECOMES-BVLT-FREE-ALT
                                   <-BECOMES-BVLT
                                   <-BECOMES-BVLT-alt)))))

(defthm equal-of-bvplus-and-bvplus-diff-sizes
  (implies (and (< size size2)
                (Natp size)
                (integerp size2))
           (equal (equal (bvplus size w z) (bvplus size2 x y))
                  (and (unsigned-byte-p size (bvplus size2 x y))
                       (equal (bvplus size w z) (bvplus size x y)))))
  :hints (("Goal" :in-theory (disable BVLT-31-8-BECOMES-UNSIGNED-BYTE-P
                                      UNSIGNED-BYTE-P-OF-BVPLUS-TIGHTEN))))

(defthm equal-of-bvplus-and-bvplus-diff-sizes-alt
  (implies (and (< size size2)
                (Natp size)
                (integerp size2))
           (equal (equal (bvplus size2 x y) (bvplus size w z))
                  (and (unsigned-byte-p size (bvplus size2 x y))
                       (equal (bvplus size w z) (bvplus size x y)))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-diff-sizes)
           :in-theory (disable equal-of-bvplus-and-bvplus-diff-sizes))))

;gen!
(defthm bvlt-of-bvplus-constants2
  (implies (and (bvlt 32 k 8)
                (equal k 4) ;gen!
                (integerp k))
           (equal (bvlt 32 (bvplus 32 k x) 8)
                  (or (bvlt 32 x k)
                      (bvle 32 (+ (expt 2 32) (- k)) x))))
  :hints (("Goal" :in-theory (disable SLICE-OF-+))))

(defthm equal-of-bvplus-move-bvminus-2
  (IMPLIES (AND (NATP SIZE))
           (equal (EQUAL (BVPLUS SIZE K2 (BVPLUS SIZE X (BVUMINUS SIZE K1)))
                         (BVCHOP SIZE Y))
                  (EQUAL (BVPLUS SIZE K2 X)
                         (BVPLUS SIZE K1 Y))))
  :hints (("Goal" :use (:instance equal-of-bvplus-move-bvminus
                                  (k2 (bvplus size k2 x)))
           :in-theory (disable equal-of-bvplus-move-bvminus))))

(defthm equal-of-bvplus-and-bvplus-reduce-constants
  (implies (and (syntaxp (quotep k2))
                (syntaxp (quotep k1))
                (syntaxp (quotep size))
                (natp size))
           (equal (equal (bvplus size k2 x) (bvplus size k1 y))
                  (equal (bvplus size (bvminus size k2 k1) x) (bvchop size y))))
  :hints (("Goal" :use (:instance equal-of-bvplus-and-bvplus-cancel-arg1-arg1
                                  (size size)
                                  (x (bvchop size k1))
                                  (y (bvplus size (bvminus size k2 k1) x))
                                  (z y))
           :in-theory (disable equal-of-bvplus-and-bvplus-cancel-arg1-arg1))))



;bad idea - causes the sizes to differ
(defthm bvplus-of-bvuminus-tighten2
  (implies (unsigned-byte-p 31 x)
           (equal (bvplus 32 (bvuminus 32 x) y)
                  (if (equal 0 x)
                      (bvchop 32 y)
                    (bvplus 32 (expt 2 31) (bvplus 32 (bvuminus 31 x) y)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   PLUS-BECOMES-BVPLUS-ARG1-FREE
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   <-BECOMES-BVLT-FREE
                                   <-BECOMES-BVLT-FREE-ALT
                                   <-BECOMES-BVLT
                                   MINUS-BECOMES-BV
                                   <-BECOMES-BVLT-alt)))))

;bad idea - causes the sizes to differ
(defthm bvplus-of-bvuminus-tighten2-alt
  (implies (unsigned-byte-p 31 x)
           (equal (bvplus 32 y (bvuminus 32 x))
                  (if (equal 0 x)
                      (bvchop 32 y)
                    (bvplus 32 (expt 2 31) (bvplus 32 (bvuminus 31 x) y)))))
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-tighten2)
           :in-theory (disable bvplus-of-bvuminus-tighten2))))

(defthm bvlt-of-bvplus-of-bvminus-expt
  (implies (unsigned-byte-p 31 x)
           (equal (bvlt '32 (bvplus '32 (bvuminus '31 y) x) '2147483648)
                  (if (equal 0 (bvchop 31 y))
                      t
                    (bvlt '31 x y))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                   <-becomes-bvlt-alt)))))

(defthm bvlt-of-bvplus-of-bvminus-expt-alt
  (implies (unsigned-byte-p 31 x)
           (equal (bvlt '32 (bvplus '32 x (bvuminus '31 y)) '2147483648)
                  (if (equal 0 (bvchop 31 y))
                      t
                    (bvlt '31 x y))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-of-bvminus-expt)
           :in-theory (disable bvlt-of-bvplus-of-bvminus-expt))))



(defthm sha1-loop-hack
  (implies (and (not (bvlt '31 x '2147483644))
                (not (bvlt '31 y x)))
           (equal (bvlt '31 '4 (bvplus '31 (bvuminus '31 x) y))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                   <-becomes-bvlt-alt)))))

(defthm sha1-loop-hack2
  (implies (and (not (bvlt 31 y x))
                (bvlt 31 4 x)
                (not (bvlt '31 y x)))
           (equal (bvlt 31 (bvplus 31 y (bvuminus 31 x)) 2147483644)
                  t))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                   <-becomes-bvlt-alt)))))





(defthm bvplus-of-bvplus-combine-constants-when-not-overflow
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep k1))
                (syntaxp (quotep smallsize))
                (syntaxp (quotep bigsize))
                (< smallsize bigsize)
                (bvlt smallsize x (- (expt 2 smallsize) k1)) ;this case
                (integerp k)
                (natp smallsize)
                (natp bigsize)
                (unsigned-byte-p smallsize k1)
                (unsigned-byte-p smallsize x))
           (equal (bvplus bigsize k (bvplus smallsize k1 x))
                  (bvplus bigsize (bvplus bigsize k k1) x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   COLLECT-CONSTANTS-OVER-<
                                   <-becomes-bvlt-alt)))))

(defthm bvlt-of-bvuminus-and-bvuminus
  (implies (natp size)
           (equal (bvlt size (bvuminus size x) (bvuminus size y))
                  (if (equal 0 (bvchop size y))
                      nil
                    (if (equal 0 (bvchop size x))
                        t
                      (bvlt size y x)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   COLLECT-CONSTANTS-OVER-<
                                   <-becomes-bvlt-alt)))))

(defthm bvplus-of-bvuminus-tighten-hack
  (implies (and (unsigned-byte-p 31 x25)
                (not (equal 0 (bvchop 31 x6)))
                (not (bvlt '31 x25 x6)))
           (equal (bvplus '32 (bvuminus '31 x6) x25)
                  (bvplus 32 (expt 2 31) (bvplus '31 (bvuminus '31 x6) x25))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   collect-constants-over-<
                                   <-becomes-bvlt-alt)))))

(defthm equal-of-bool-to-bit-split
  (equal (equal x (bool-to-bit y))
         (and (unsigned-byte-p 1 x)
              (iff (equal 1 x)
                   (bool-fix y)))))

;ffixme does this help?
(defthm bvlt-of-bvplus-of-bvuminus
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size))
           (equal (bvlt size z (bvplus size x (bvuminus size y)))
                  (if (bvlt size z (bvuminus size y))
                    ;simplify this?:
                      (if (bvlt size (bvplus size x (bvuminus size y)) (bvuminus size y))
                          (bvlt size (bvplus size z y) x)
                        t)
                    ;simplify this?:
                    (if (bvlt size (bvplus size x (bvuminus size y)) (bvuminus size y))
                        nil
                      (bvlt size (bvplus size z y) x)))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides
                                  (x z)
                                  (y (bvplus size x (bvuminus size y)))
                                  (z y)))))

;ffixme does this help?
(defthm bvlt-of-bvplus-of-bvuminus-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size))
           (equal (bvlt size z (bvplus size (bvuminus size y) x))
                  (if (bvlt size z (bvuminus size y))
                      (if (bvlt size (bvplus size x (bvuminus size y)) (bvuminus size y))
                          (bvlt size (bvplus size z y) x)
                        t)
                    ;simplify this?:
                    (if (bvlt size (bvplus size x (bvuminus size y)) (bvuminus size y))
                        nil
                      (bvlt size (bvplus size z y) x)))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-of-bvuminus)
           :in-theory (disable bvlt-of-bvplus-of-bvuminus))))

;; (defthm bvlt-of-bvuminus
;;   (implies (and (integerp y)
;;                 (integerp x)
;;                 (natp size))
;;            (equal (bvlt size x (bvuminus size y))

;gen the 0
(defthm bvlt-of-0-and-bvuminus
  (implies (natp size)
           (equal (bvlt size 0 (bvuminus size x))
                  (bvlt size 0 x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases
                                          bvuminus
                                          bvchop-of-minus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   collect-constants-over-<
                                   <-becomes-bvlt-alt)))))

(defthm bvlt-of-0-polarity
  (implies (syntaxp (want-to-weaken (BVLT SIZE 0 Z)))
           (equal (BVLT SIZE 0 Z)
                  (not (equal 0 (bvchop size z)))))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt-free
                                          <-becomes-bvlt-free-alt
                                          <-becomes-bvlt
                                          <-becomes-bvlt-alt)))))





;gen!
(defthm getbit-of-bvplus-of-expt-2
  (implies (integerp x)
           (equal (GETBIT 31 (BVPLUS 32 2147483648 x))
                  (bitnot (getbit 31 x))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases
                                          getbit-of-plus
                                          bvuminus
                                          bvchop-of-minus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   collect-constants-over-<
                                   <-becomes-bvlt-alt)))))

(defthm sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (sbvlt 32 0 (bvplus 32 (bvuminus 32 x) y))
                  (bvlt 31 x y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases
                                          bvuminus
                                          getbit-of-plus
                                          bvchop-of-minus
                                          bvminus
                                          bvlt
                                          )
                                  (anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   collect-constants-over-<
                                   <-becomes-bvlt-alt)))))

(defthm sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger-alt
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (sbvlt 32 0 (bvplus 32 y (bvuminus 32 x)))
                  (bvlt 31 x y)))
  :hints (("Goal" :use (:instance sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger)
           :in-theory (disable sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger))))

(defthm bvplus-of-bvuminus-same-diff-size
  (equal (bvplus 32 x (bvuminus 31 x))
         (if (equal 0 (bvchop 31 x))
             (bvcat 1 (getbit 31 x) 31 0)
           (bvcat 1 (bitnot (getbit 31 x)) 31 0)))
  :hints (("Goal" :in-theory (e/d (bvplus ;bvchop-of-sum-cases
                                          bvuminus
                                          getbit-of-plus
                                          bvchop-of-minus
                                          bvminus
                                          bvlt
                                          getbit-when-val-is-not-an-integer
                                          )
                                  (SLICE-OF-+
                                   anti-bvplus GETBIT-OF-+
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   collect-constants-over-<
                                   <-becomes-bvlt-alt)))))

(defthm getbit-of-bvplus-of-bvuminus-one-bigger
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (getbit 31 (bvplus '32 (bvuminus '32 x) y))
                  (bool-to-bit (bvlt 31 y x))))
  :hints (("Goal" :use (:instance sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger)
           :in-theory (disable GETBIT-WHEN-BVLT-OF-SMALL-HELPER
                               sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger
                               sbvlt-of-0-and-bvplus-of-bvuminus-one-bigger-alt))))

(defthm getbit-of-bvplus-of-bvuminus-one-bigger-alt
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (getbit 31 (bvplus '32 y (bvuminus '32 x)))
                  (bool-to-bit (bvlt 31 y x))))
  :hints (("Goal" :use (:instance getbit-of-bvplus-of-bvuminus-one-bigger)
           :in-theory (disable getbit-of-bvplus-of-bvuminus-one-bigger))))

(defthm getbit-of-bvplus-of-bvuminus-one-bigger-31-32-31
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (getbit 31 (bvplus '32 (bvuminus '31 x) y))
                  (if (equal 0 x)
                      (getbit 31 y)
                    (bool-to-bit (not (bvlt 31 y x))))))
  :hints (("Goal" :use (:instance getbit-of-bvplus-of-bvuminus-one-bigger)
           :in-theory (disable getbit-of-bvplus-of-bvuminus-one-bigger))))

(defthm getbit-of-bvplus-of-bvuminus-one-bigger-31-32-31-alt
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (getbit 31 (bvplus '32 y (bvuminus '31 x)))
                  (if (equal 0 x)
                      (getbit 31 y)
                    (bool-to-bit (not (bvlt 31 y x))))))
  :hints (("Goal" :use (:instance getbit-of-bvplus-of-bvuminus-one-bigger-31-32-31)
           :in-theory (disable getbit-of-bvplus-of-bvuminus-one-bigger-31-32-31))))

(defthm equal-of-bvcat-and-bvmult-32-3
  (equal (equal (bvcat 29 x 3 0) (bvmult 32 8 x))
         t))

(defthm equal-of-bvcat-and-bvmult-32-3-alt
  (equal (equal (bvcat 29 x 3 0) (bvmult 32 8 x))
         t)
  :hints (("Goal" :use (:instance equal-of-bvcat-and-bvmult-32-3)
           :in-theory (disable equal-of-bvcat-and-bvmult-32-3))))

;gen!
(defthm boolor-of-not-equal-and-not-bvlt-5-31-13
  (equal (boolor (not (equal 31 x)) (not (bvlt 5 13 x)))
         (not (equal 31 x))))

;move
(defthm equal-of-bv-array-write-same
  (implies (and (natp width)
                (natp index)
                (< index len)
                (integerp len))
           (equal (equal x (bv-array-write width len index val x))
                  (and (equal len (len x))
                       (true-listp x)
                       (all-unsigned-byte-p width x)
                       (equal (bvchop width val)
                              (bv-array-read width len index x)))))
  :hints (("Goal" :cases ((equal len (len x))))))

(defthm bvlt-cancel-for-sha1
  (implies (and (bvle 5 x 6)
                (unsigned-byte-p 5 x))
           (equal (BVLT '5 '15 (BVMULT '5 '5 x))
                  (BVLT '5 3 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*
                                   <-BECOMES-BVLT-FREE
                                   )))))

(defthm bvlt-of-bvmult-for-sha1
  (implies  (and (bvle 5 x 6)
                 (unsigned-byte-p 5 x))
            (equal (BVLT '5 '20 (BVMULT '5 '5 x))
                   (BVLT '5 4 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*
                                   <-BECOMES-BVLT-FREE
                                   )))))

;move
(defthm mod-of-*-same
  (implies (and (integerp i)
                (not (equal 0 j))
                (integerp j))
           (equal (MOD (* j i) j)
                  0))
  :hints (("Goal" :in-theory (enable MOD-IS-0-WHEN-MULTIPLE))))

(defthm SBVMODDOWN-of-bvmult-same-32-5-5-5
  (implies (and (bvle 5 x 6)
                (natp size)
                (equal 5 size)
;(<= 5 size)
;(<= size 31)
                (unsigned-byte-p 5 x))
           (equal (SBVMODDOWN '32 (BVMULT size '5 x) '5)
                  0))
  :hints (("Goal" :in-theory (e/d (SBVMODDOWN bvmult bvmod bvchop logext logapp getbit slice ;bvlt
                                              <-becomes-bvlt ;why?
                                              )
                                  ( ;MOD-NON-NEGATIVE-CONSTANT-POS-REWRITE
;
;MOD-X-Y-=-X
;MOD-X-Y-=-X+Y
                                   BVCHOP-OF-* MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                   anti-slice
                                   MOD-OF-EXPT-OF-2
                                   BVCHOP-1-BECOMES-GETBIT
                                   SLICE-BECOMES-GETBIT)))))


(defthm bvmod-of-bvmult-same
  (implies (and (bvle 5 x 6)
                (unsigned-byte-p 5 x))
           (equal (BVMOD '5 (BVMULT '5 '5 x) '5)
                  0))
  :hints (("Goal" :in-theory (e/d (SBVMODDOWN bvmult bvmod bvchop logext logapp getbit slice ;bvlt
                                              <-becomes-bvlt ;why?
                                              )
                                  ( ;MOD-NON-NEGATIVE-CONSTANT-POS-REWRITE
;
;MOD-X-Y-=-X
;MOD-X-Y-=-X+Y
                                   BVCHOP-OF-* MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                   anti-slice
                                   MOD-OF-EXPT-OF-2
                                   BVCHOP-1-BECOMES-GETBIT
                                   SLICE-BECOMES-GETBIT)))))

(defthm bvmod-of-bvplus
  (implies (and (bvlt size x (- (expt 2 size) n)) ;the bvplus doesn't overflow
                (natp n)
                (natp size)
                (< n (expt 2 size))
                (unsigned-byte-p size x))
           (equal (bvmod size (bvplus size n x) n)
                  (bvmod size x n)))
  :hints (("Goal" :in-theory (e/d (bvplus sbvmoddown bvmult bvmod bvchop logext logapp getbit slice
                                          bvlt)
                                  (anti-bvplus GETBIT-OF-+
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+ ;looped
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-free
                                   +-of-minus-1-and-bv2
                                   bvchop-of-* mod-of-expt-of-2-constant-version
                                   anti-slice
                                   mod-of-expt-of-2
                                   bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   <-BECOMES-BVLT-FREE)))))

;gen!
(defthm bvmult-of-bvplus-for-sha1
  (implies (and (unsigned-byte-p 3 x)
                (bvlt 3 x 7))
           (equal (bvmult 32 5 (bvplus 3 1 x))
                  (bvplus 32 (bvmult 32 5 1)
                          (bvmult 32 5 x))))
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D (BVCAT BVMULT LOGAPP BVPLUS bvlt)
         (PLUS-BECOMES-BVPLUS-FREE
          BVCHOP-OF-* BVCHOP-SHIFT-GEN BVPLUS-OF-BVCHOP-ARG2
          BVPLUS-OF-BVCHOP-ARG1
          ANTI-BVPLUS GETBIT-OF-+
          BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2
          PLUS-BECOMES-BVPLUS
          <-becomes-bvlt
          <-becomes-bvlt-alt
          <-of-bvplus-becomes-bvlt-arg1
          <-of-bvplus-becomes-bvlt-arg2
          <-BECOMES-BVLT-FREE)))))

(defthm bvmult-when-bvlt-6-5-3-4
  (implies (and (not (BVLT '3 '4 x))
                (UNSIGNED-BYTE-P '3 x))
           (equal (BVMULT '6 '5 x)
                  (BVMULT '5 '5 x)))
  :hints (("Goal" :in-theory (e/d (bvmult bvlt UNSIGNED-BYTE-P)
                                  (<-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   <-BECOMES-BVLT-FREE
                                   <-BECOMES-BVLT-FREE-ALT
;                                   <-BECOMES-BVLT-TABLE
;<-BECOMES-BVLT-TABLE-alt
                                   BVCHOP-OF-*)))))

(defthm mod-of-plus-when-multiple
  (implies (and (equal 0 (mod m n))
                (integerp m)
                (natp n)
                (integerp x))
           (equal (mod (+ m x) n)
                  (mod x n)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil)))
  :hints (("Goal" :cases ((equal 0 n)))))

(defthm <-of-mod-and-0
  (IMPLIES (IF (FORCE (RATIONALP X))
               (IF (FORCE (RATIONALP Y))
                   (FORCE (NOT (EQUAL '0 Y)))
                   'NIL)
               'NIL)
           (EQUAL (< (MOD X Y) 0)
                  (AND (< Y 0)
                       (NOT (INTEGERP (/ X Y)))))))

(defthm bvmod-of-bvplus-gen
  (implies (and (syntaxp (quotep m))
                (syntaxp (quotep n))
                (syntaxp (quotep size))
                (bvlt size x (- (expt 2 size) m)) ;the bvplus doesn't overflow
                (equal 0 (bvmod size m n)) ;m is a multiple of n
                (natp n)
                (natp m)
                (natp size)
                (unsigned-byte-p size m)
                (unsigned-byte-p size n)
                (unsigned-byte-p size x))
           (equal (bvmod size (bvplus size m x) n)
                  (bvmod size x n)))
  :hints (("Goal"
           :cases ((equal n 0)) ;or improve mod-bounded-by-modulus
           :in-theory (e/d (bvplus sbvmoddown bvmult bvmod bvchop logext logapp getbit slice
                                   bvlt)
                                  (MOD-BOUNDED-BY-MODULUS ;expensive!
                                   MOD-TYPE ;expensive!
                                   COLLECT-CONSTANTS-OVER-<
                                   BVLT-OF-MAX
                                   anti-bvplus GETBIT-OF-+
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+ ;looped
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-free
                                   +-of-minus-1-and-bv2
                                   bvchop-of-* mod-of-expt-of-2-constant-version
                                   anti-slice
                                   mod-of-expt-of-2
                                   bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   <-BECOMES-BVLT-FREE
                                   <-BECOMES-BVLT-FREE-ALT
                                   mod-sum-cases
                                   MOD-UPPER-BOUND-LINEAR
                                   ;MOD-TYPE ;improve this rule!
                                   )))))

;gen!
(defthm bvmult-tighten-hack-for-sha1
  (implies (UNSIGNED-BYTE-P '3 x)
           (equal (BVMULT '32 '5 x)
                  (BVMULT '6 '5 x)))
  :hints (("Goal" :in-theory (e/d (bvmult) (BVCHOP-OF-*)))))

;; (defun my-ceiling (x)
;;   (if (integerp x)
;;       x
;;     (+ 1 (floor x 1))))

(defthm bvlt-of-bvmult-for-sha1-gen
  (implies  (and (bvle 5 x 6)
                 (equal k 24)
                 (unsigned-byte-p 5 x)
                 (unsigned-byte-p 5 k))
            (equal (BVLT '5 (BVMULT '5 '5 x) k)
                   (BVLT '5 x 5)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*
                                   <-BECOMES-BVLT-FREE
                                   )))))

(defthm bvlt-of-bvmult-for-sha1-gen2
  (implies  (and (bvle 5 x 6)
                 (equal k 19)
                 (unsigned-byte-p 5 x)
                 (unsigned-byte-p 5 k))
            (equal (BVLT '5 (BVMULT '5 '5 x) k)
                   (BVLT '5 x 4;(ceiling k 5)
                         )))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*
                                   <-BECOMES-BVLT-FREE
                                   )))))

(defthm bvlt-of-bvmult-for-sha1-gen3
  (implies  (and (bvle 5 x 6)
                 (equal k 23)
                 (unsigned-byte-p 5 x)
                 (unsigned-byte-p 5 k))
            (equal (BVLT '5 (BVMULT '5 '5 x) k)
                   (BVLT '5 x 5;(ceiling k 5)
                         )))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*
                                   <-BECOMES-BVLT-FREE
                                   )))))

(defthm bvplus-of-bvmult-tigthen-for-sha1
  (implies (and (UNSIGNED-BYTE-P '3 x)
                (not (BVLT '3 '4 x)))
           (equal (BVPLUS '7 '40 (BVMULT '5 '5 x))
                  (BVPLUS '6 '40 (BVMULT '5 '5 x)))))

(defthm bvplus-of-bvmult-tigthen-for-sha1-2
  (implies (and (UNSIGNED-BYTE-P '3 x)
                (not (BVLT '3 '4 x)))
           (equal (BVPLUS '7 '41 (BVMULT '5 '5 x))
                  (BVPLUS '6 '41 (BVMULT '5 '5 x)))))

(defthm ceiling-in-terms-of-floor-alt
  (implies (and (rationalp i)
                (rationalp j))
           (equal (ceiling i j)
                  (if (integerp (/ i j))
                      (/ i j)
                    (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthmd floor-bound-hack-31
  (implies (and (<= X (FLOOR 31 J))
                (rationalp x)
                (posp j)
                (posp x)
                (rationalp j))
           (<= (* x j) 31))
  :hints (("Goal" :in-theory (e/d ()
                                  (FLOOR-BOUND-LEMMA2
                                   my-FLOOR-LOWER-BOUND-ALT
                                   MY-FLOOR-UPPER-BOUND
                                   FLOOR-BOUND-LEMMA3
                                   my-FLOOR-UPPER-BOUND-ALT
                                   <-*-/-LEFT))
           :use (:instance MY-FLOOR-UPPER-BOUND (i 31) (j j)))))

(defthmd bvlt-of-bvmult-for-sha1-gen4-helper
  (IMPLIES (AND (POSP J)
                (INTEGERP X)
                (INTEGERP K)
                (<= 0 K)
                (NOT (INTEGERP (* (/ J) K)))
                (<= K (* J X)))
           (< (FLOOR K J) X))
  :hints (("Goal" :in-theory (e/d (;floor-bounded-by-/
                                   FLOOR-TYPE-1
                                   ) (FLOOR-BOUND-LEMMA2
                                      my-FLOOR-LOWER-BOUND-ALT
                                      MY-FLOOR-UPPER-BOUND
                                      FLOOR-BOUND-LEMMA3
                                      my-FLOOR-UPPER-BOUND-ALT
;                                     <-*-/-LEFT
;                                    <-*-/-LEFT-COMMUTED
;                                   <-*-/-RIGHT-COMMUTED
                                      <-*-LEFT-CANCEL
                                      FLOOR-upper-BOUND-strict
                                      ))
           :use ((:instance FLOOR-upper-BOUND-strict (i k) (j j))
                 (:instance <-*-LEFT-CANCEL (x (FLOOR K J)) (y x) (z j) )))))


;gen the 5..
(defthm bvlt-of-bvmult-for-sha1-gen4
  (implies  (and                         ;(bvle 10 (bvmult '5 '5 x) 31)
             (bvle 5 x (floor 31 j))     ;the bvmult doesn't overflow
;                 (equal j 6)
             (posp j)
             (unsigned-byte-p 5 x)
             (unsigned-byte-p 5 j)
             (unsigned-byte-p 5 k))
            (equal (bvlt '5 (bvmult '5 j x) k)
                   (bvlt '5 x (ceiling k j))))
  :hints (("Subgoal 11.1''" :cases ((< x 0))) ;yuck!
          ("Goal"
           :use ((:instance floor-bound-hack-31)
;                 (:instance bvchop-identity (i (* J X)) (size 5))
 ;                (:instance bvchop-identity (i k) (size 5))
  ;               (:instance bvchop-identity (i (FLOOR K J)) (size 5))
   ;              (:instance bvchop-identity (i (* (/ J) K)) (size 5))
                 bvlt-of-bvmult-for-sha1-gen4-helper)
           :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                 bvmult bvchop-when-i-is-not-an-integer
                                 floor-type-1
                                 floor-bounded-by-/
                                 bvchop-when-top-bit-1)
                           (;bvchop-identity
                            ;bvchop-identity-cheap
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            bvchop-of-*
                            <-becomes-bvlt-free
                            PLUS-BECOMES-BVPLUS-FREE
;                            *-OF-2-BECOMES-BVMULT
                            COLLECT-CONSTANTS-OVER-<
                            +-OF-MINUS-1-AND-BV2
                            )))))

;gen!
(defthm bvmult-tigthen-for-sha1-1000
  (implies (and (UNSIGNED-BYTE-P '3 x)
                (not (BVLT '3 '4 x))
                (natp size)
                (< 5 size))
           (equal (BVmult size 5 x)
                  (BVmult 5 5 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvmult bvchop-when-i-is-not-an-integer
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*
                                   <-becomes-bvlt-free
                                   PLUS-BECOMES-BVPLUS-FREE
;                                   *-OF-2-BECOMES-BVMULT
                                   )))))


;use bind-from-rules instead?
(defthm bound-theorem-for-sha1-hack
  (implies (not (bvlt '32 '3 x)) ;wasteful?
           (equal (unsigned-byte-p '31 (bvplus '32 '1 x))
                  t))
  :hints (("Goal" :in-theory (enable bvlt-add-to-both-sides-constant-lemma-alt))))

(defthm getbit-of-bvplus-of-1-32
  (equal (GETBIT '31 (BVPLUS '32 '1 x))
         (if (equal (bvchop 31 x) (+ -1 (expt 2 31)))
             (bitnot (getbit 31 x))
           (getbit 31 x)))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p bvplus bvuminus bvminus bvchop-of-sum-cases sbvlt
                                        bvchop-when-i-is-not-an-integer
                                        GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                        bvchop-when-top-bit-1)
                                  ( ;<-becomes-bvlt
                                   plus-1-and-bvchop-becomes-bvplus ;fixme
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-of-bvplus-becomes-bvlt-arg1
                                   <-of-bvplus-becomes-bvlt-arg2
                                   <-becomes-bvlt-free
                                   anti-bvplus GETBIT-OF-+ plus-becomes-bvplus
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   slice-of-+
                                   getbit-of-+ ;looped
                                   bvchop-of-*

                                   PLUS-BECOMES-BVPLUS-FREE
                                   )))))




(defthmd <-when-unsigned-byte-p-and-not-unsigned-byte-p
  (implies (and (unsigned-byte-p n x)
                (natp y)
                (not (unsigned-byte-p n y)))
           (< x y))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm <-when-unsigned-byte-p
  (implies (and (unsigned-byte-p free x)
                (natp y)
                )
           (equal (< x y)
                  (if (unsigned-byte-p free y)
                      (bvlt free x y)
                    t)))
  :hints (("Goal" :in-theory (enable <-when-unsigned-byte-p-and-not-unsigned-byte-p bvlt))))

(defthm <-when-unsigned-byte-p-alt
  (implies (and (unsigned-byte-p free y)
                (natp free)
                (natp x))
           (equal (< x y)
                  (if (unsigned-byte-p free x)
                      (bvlt free x y)
                    nil)))
  :hints (("Goal" :in-theory (e/d (bvlt) (COLLECT-CONSTANTS-OVER-<)))))

;gen
(defthm unsigned-byte-p-of-plus-31-4
 (implies (integerp x)
          (equal (UNSIGNED-BYTE-P 31 (+ 4 X))
                 (and (<= -4 x)
                      (< x (+ (expt 2 31) (- 4))))))
 :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))

(defthm bvlt-hack-for-sha1
  (implies (and (not (bvlt '31 x16 x7))
                (unsigned-byte-p '31 x16)
                (unsigned-byte-p '31 x7)
                (not (bvlt '31 x7 '2147483644)))
           (equal (bvlt '31 (bvplus '31 (bvuminus '31 x7) x16) '4)
                  t))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (
                                   anti-bvplus GETBIT-OF-+
                                   SLICE-OF-+
                                   ;+-BECOMES-BVPLUS-HACK-GEN
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                   <-becomes-bvlt-alt
                                   UNSIGNED-BYTE-P-WHEN-BVLT-3-31)))))

(defthm bvlt-hack-for-sha1-alt
  (implies (and (not (bvlt '31 x16 x7))
                (unsigned-byte-p '31 x16)
                (unsigned-byte-p '31 x7)
                (not (bvlt '31 x7 '2147483644)))
           (equal (bvlt '31 (bvplus '31 x16 (bvuminus '31 x7)) '4)
                  t))
  :hints (("Goal" :use (:instance bvlt-hack-for-sha1)
           :in-theory (disable bvlt-hack-for-sha1))))

(defthmd bvlt-of-bvplus-of-bvuminus-other
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size))
           (equal (bvlt size (bvplus size (bvuminus size y) x) z)
                  (if (and (not (equal 0 (bvchop size x)))
                           (not (equal 0 (bvchop size y)))
                           (not (bvlt size x y)))
                      (if (bvlt size z (bvuminus size y))
                          (bvlt size x (bvplus size z y))
                        t)
                    (if (bvlt size z (bvuminus size y))
                        nil
                      (bvlt size x (bvplus size z y))))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides
                                  (x (bvplus size (bvuminus size y) x))
                                  (y z)
                                  (z y)))))

(defthmd bvlt-of-bvplus-of-bvuminus-other-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size))
           (equal (bvlt size (bvplus size x (bvuminus size y)) z)
                  (if (and (not (equal 0 (bvchop size x)))
                           (not (equal 0 (bvchop size y)))
                           (not (bvlt size x y)))
                      (if (bvlt size z (bvuminus size y))
                          (bvlt size x (bvplus size z y))
                        t)
                    (if (bvlt size z (bvuminus size y))
                        nil
                      (bvlt size x (bvplus size z y))))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-of-bvuminus-other))))

;gen
(defthm bvchop-of-+-of-expt-same
  (implies (natp n)
           (equal (bvchop n (+ (expt 2 n) y))
                  (bvchop n y)))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm getbit-of-bvplus-of-bvcat-lemma
  (implies (and (equal n+1 (+ 1 n))
                (natp n))
           (equal (getbit n (bvplus n+1 x (bvcat 1 1 n y)))
                  (bitnot (getbit n (bvplus n+1 x (bvchop n y))))))
  :hints (("Goal" :use (:instance getbit-of-bvplus-flip (x (+ x (bvchop n y))))
           :in-theory (e/d (bvcat logapp bvplus getbit-of-plus)
                           ( getbit-of-bvplus-flip

                                            anti-bvplus GETBIT-OF-+
                                            bvlt-of-plus-arg1
                                            bvlt-of-plus-arg2
                                            bvplus-of-plus-arg3
                                            getbit-of-+
                                            plus-becomes-bvplus
                                            <-OF-BVCHOP-HACK ;looped
                                            )))))

(in-theory (disable ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1)) ;new

(defthm bvlt-of-bvuminus-when-no-overflow
  (implies (and (unsigned-byte-p 31 i)
                (unsigned-byte-p 31 (+ i k)) ;move to conc?
                (unsigned-byte-p 31 k))
           (equal (BVLT 31 K (BVUMINUS 31 I))
                  (not (equal 0 i))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (
                                   anti-bvplus GETBIT-OF-+
                                   SLICE-OF-+
                                   BVPLUS-OF-PLUS-ARG3
;+-BECOMES-BVPLUS-HACK-GEN
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-WHEN-UNSIGNED-BYTE-P ;;
                                   minus-becomes-bv
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                   <-becomes-bvlt-alt
                                   UNSIGNED-BYTE-P-WHEN-BVLT-3-31)))))

;(in-theory (disable *-OF-2-BECOMES-BVMULT)) ;new

(defthm same-remainder-when-close-lemma-bv
  (implies (and (not (bvlt 31 j i))
                (bvlt 31 (bvplus 31 j (bvuminus 31 i)) k)
                (equal 0 (bvmod 31 i k))
                (unsigned-byte-p 31 i)
                (unsigned-byte-p 31 j)
                (unsigned-byte-p 31 k))
           (equal i (bvmult 31 k (bvdiv 31 j k))))
  :rule-classes nil
  :hints (("Goal"
           :use (:instance same-remainder-when-close-lemma)
           :in-theory (e/d (bvmod bvmult bvdiv BVLT-OF-BVPLUS-OF-BVUMINUS-OTHER-ALT
                                  BVPLUS-OF-UNARY-MINUS BVPLUS-OF-UNARY-MINUS-arg2)
                           (same-remainder-when-close-lemma
                            ;;SLICE-OF-+ BVLT-OF-PLUS-ARG2 ;can almost loop
                            )))))

;; (thm
;;  (IMPLIES (AND (BVLT 31 J 2147483644)
;;               (EQUAL (SLICE 30 2 J) 536870911))
;;          (NOT (UNSIGNED-BYTE-P 31 J))))

;gen! make sure things still match
(DEFTHM equal-of-bvmult-of-power-of-2
  (IMPLIES (AND (NATP 2)
                (NATP 29))
           (EQUAL (EQUAL X
                         (bvmult 31 4 HIGHVAL))
                  (AND (UNSIGNED-BYTE-P (+ 2 29) X)
                       (EQUAL (BVCHOP 2 X) 0)
                       (EQUAL (SLICE (+ -1 2 29)
                                     2 X)
                              (BVCHOP 29 HIGHVAL)))))
  :hints (("Goal" :use (:instance BVCAT-EQUAL-REWRITE (highsize 29) (lowsize 2) (lowval 0))
           :in-theory (e/d (bvcat bvmult)( BVCAT-EQUAL-REWRITE BVCAT-EQUAL-REWRITE-alt )

                           ))))

;gen!
;think about how we should rewrite this..
;expensive?
;ffixme this is like bvcat-equal-rewrite? remove hyp and add a conc about slices being equal?
;; (defthm same-remainder-when-close-lemma-bv-4
;;   (implies (and (bvlt 31 (bvplus 31 j (bvuminus 31 i)) 4) ;make this the lhs? ;this is not normalized
;;                 (unsigned-byte-p 31 i)
;;                 (unsigned-byte-p 31 j))
;;            (equal (equal i (bvmult 31 4 (slice 30 2 j)))
;;                   (and (equal 0 (bvchop 2 i)) ;same as the bvmod fact?
;;                        (not (bvlt 31 j i)))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :use (:instance same-remainder-when-close-lemma-bv (k 4)))))

;remove disables below
(defthmd bvlt-of-*-arg3
  (implies (and (integerp y)
                (integerp z))
           (equal (bvlt size x (* y z))
                  (bvlt size x (bvmult size y z))))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(theory-invariant (incompatible (:definition bvmult) (:rewrite bvlt-of-*-arg3)))
;(theory-invariant (incompatible (:definition bvmult) (:rewrite *-of-2-becomes-bvmult)))


;could be expensive
(defthmd unsigned-byte-p-when-unsigned-byte-p-free
  (implies (and (unsigned-byte-p size free)
                (<= x free)
                (natp x))
           (unsigned-byte-p size x)))


;i am using this instead of deftheory so that the runes don't have to exist yet (either when this form is submitted to define the list of runes or when it is used in a hint!)
;also, acl2's treatment of redundant deftheories is annoying
(defun anti-bvmult ()
  '((:rewrite bvchop-of-*)
    (:rewrite bvlt-of-*-arg3)
;    (:rewrite *-OF-2-BECOMES-BVMULT)
    ))

(defun anti-bvlt ()
  '((:rewrite <-OF-BVCHOP-ARG1)
    (:rewrite <-WHEN-UNSIGNED-BYTE-P-ALT)
    (:rewrite <-becomes-bvlt-free)
    (:rewrite <-becomes-bvlt-free-alt)
    (:rewrite <-becomes-bvlt)
    (:rewrite <-WHEN-UNSIGNED-BYTE-P)))

;could drop some hyps
(defthm bvlt-of-bvmult-of-bvdiv-helper
  (implies (and (unsigned-byte-p size y)
                (unsigned-byte-p size x)
                (natp size))
           (equal (bvlt size x (bvmult size y (bvdiv size x y)))
                  nil))
  :hints (("Goal" :cases ((equal y 0))
           :in-theory (set-difference-equal (e/d ( unsigned-byte-p-when-unsigned-byte-p-free
                                                   bvlt
                                                   bvmult
                                                   bvdiv
                                                   )
                                                 (

                                                  anti-bvplus GETBIT-OF-+
                                                  SLICE-OF-+
                                                  BVPLUS-OF-PLUS-ARG3
;+-BECOMES-BVPLUS-HACK-GEN
                                                  getbit-of-+ +-OF-MINUS-1-AND-BV2
                                                  BVLT-OF-*-ARG3
                                                  plus-becomes-bvplus-free
                                                  bvlt-of-plus-arg1
                                                  bvlt-of-plus-arg2
                                                  plus-becomes-bvplus
                                                  plus-becomes-bvplus-arg1-free
                                                  bvminus-becomes-bvplus-of-bvuminus
                                                  ;;
                                                  minus-becomes-bv
                                                  PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                                  <-becomes-bvlt-alt))
                                            (append (anti-bvlt)
                                                    (anti-bvmult))))))

(defthm bvlt-of-bvmult-of-bvdiv
  (implies (natp size)
           (equal (bvlt size x (bvmult size y (bvdiv size x y)))
                  nil))
  :hints (("Goal" :use (:instance bvlt-of-bvmult-of-bvdiv-helper (x (bvchop size x)) (y (bvchop size y)))
           :in-theory (disable bvlt-of-bvmult-of-bvdiv-helper))))

;gen
(defthm bvlt-of-bvplus-and-bvplus-lemma-sha1
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 32 (bvplus '32 '2147483648 x) (bvplus '32 '2147483648 y))
                  (bvlt 32 x y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (
                                   anti-bvplus GETBIT-OF-+
                                   SLICE-OF-+
                                   BVPLUS-OF-PLUS-ARG3
  ;+-BECOMES-BVPLUS-HACK-GEN
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-WHEN-UNSIGNED-BYTE-P ;;
                                   minus-becomes-bv
                                   PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                   <-becomes-bvlt-alt
                                   UNSIGNED-BYTE-P-WHEN-BVLT-3-31)))))

(defthm <-of-mod-same
  (implies (and (<= 0 x)
                (rationalp x)
                (<= 0 y)
                (rationalp y))
           (not (< x (mod x y))))
  :hints (("Goal"
           :cases ((equal 0 y))
           :in-theory (e/d (mod) (;mod-recollapse-lemma2 mod-recollapse-lemma
                                  )))))

(defthm times-of-mod-of-floor-bound
  (implies (and (natp i)
                (posp j)
                (posp k))
           (<= (* j (mod (floor i j) k))
               i))
  :hints (("Goal" :use ((:instance floor-upper-bound-alt-linear (j j))
                        (:instance <-*-left-cancel (y (mod (floor i j) k)) (x (floor i j)) (z j))
                        (:instance <-of-mod-same (x (FLOOR I J)) (y k))
                        )
           :in-theory (disable same-remainder-when-close-lemma
                               MOD-X-Y-=-X-FOR-RATIONALS
                               <-*-left-cancel
                               <-of-mod-same
                               floor-upper-bound-alt-linear
                               floor-bound-lemma3
                               my-floor-upper-bound-alt
                               mod-of-expt-of-2-constant-version))))

;gen
(defthm <-of-*-of-slice-of-same
  (implies (natp x)
           (not (< X (* 4 (SLICE 30 2 X)))))
  :hints (("Goal" :in-theory (e/d (slice logtail bvchop) (anti-slice MOD-OF-EXPT-OF-2-CONSTANT-VERSION)))))

(defthm <-of-floor-combine-constants
  (implies (and (rationalp i)
                (equal j 4) ;gen!
                (posp j))
           (equal (< (floor i j) 536870912)
                  (< i (* j 536870912))))
  :hints (("Goal" :use ((:instance my-floor-upper-bound)
                        (:instance my-floor-lower-bound-alt))
           :in-theory (disable <-*-/-LEFT
                               my-floor-lower-bound-alt
                               my-floor-lower-bound
                               FLOOR-BOUND-LEMMA2
                               my-floor-upper-bound
                               FLOOR-BOUND-LEMMA3
                               my-FLOOR-UPPER-BOUND-ALT))))

(defthm <-of-+-of-*-of-slice-sha1
  (implies (and (unsigned-byte-p 31 x)
                (not (equal (slice 30 2 x) 0)))
           (not (< (+ 3 (* 4 (slice 30 2 x))) x)))
  :hints (("Goal"
           :use ((:instance mod-when-< (x (floor x 4)) (y 536870912))
                 (:instance my-floor-lower-bound-alt (i x) (j 4)))
           :in-theory (e/d (slice logtail bvchop)
                           (my-floor-lower-bound-alt
                            floor-bound-lemma2
;                            mod-x-y-=-x
                            mod-when-<
                            <-when-unsigned-byte-p-alt
                            <-when-unsigned-byte-p
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            anti-slice
                            mod-of-expt-of-2-constant-version)))))

(defthm bvlt-of-bvplus-of-bvuminus-and-bvmult-of-bvdiv-sha1
  (implies (unsigned-byte-p 31 x)
           (equal (BVLT '32 '3 (BVPLUS '32 x (BVUMINUS '32 (BVMULT '31 '4 (BVDIV '31 x '4)))))
                  nil))
  :hints (("Goal" :use (:instance <-OF-+-OF-*-OF-SLICE-SHA1)
           :in-theory (set-difference-equal
                              (e/d (bvplus bvchop-of-sum-cases
                                           bvuminus
                                           bvminus
                                           bvlt
                                           bvmult
                                           SLICE-WHEN-VAL-IS-NOT-AN-INTEGER
                                           bvcat
                                           )
                                   (<-OF-+-OF-*-OF-SLICE-SHA1
                                    TIMES-4-OF-SLICE-BECOMES-LOGAPP ;rename, looped

                                    anti-bvplus GETBIT-OF-+
                                    SLICE-OF-+
                                    BVPLUS-OF-PLUS-ARG3
;+-BECOMES-BVPLUS-HACK-GEN
                                    getbit-of-+
                                    plus-becomes-bvplus-free
                                    bvlt-of-plus-arg1
                                    bvlt-of-plus-arg2
                                    plus-becomes-bvplus
                                    plus-becomes-bvplus-arg1-free
                                    bvminus-becomes-bvplus-of-bvuminus
                                    <-WHEN-UNSIGNED-BYTE-P-ALT
                                    <-becomes-bvlt-free
                                    <-becomes-bvlt-free-alt
                                    <-becomes-bvlt
;                                    <-OF-BVCHOP-ARG1
                                    <-WHEN-UNSIGNED-BYTE-P ;;
                                    minus-becomes-bv
                                    PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                                    <-becomes-bvlt-alt
                                    UNSIGNED-BYTE-P-WHEN-BVLT-3-31))
                              (anti-bvmult)))))

(in-theory (disable UNSIGNED-BYTE-P-WHEN-BVLT-3-31))

(defthm bvlt-of-bvplus-of-bvminus-expt-new
  (implies (and (unsigned-byte-p 31 x)
                (integerp y))
           (equal (bvlt 32 2147483648 (bvplus 32 x (bvuminus 31 y)))
                  (if (equal 0 (bvchop 31 y))
                      nil
                    (bvlt '31 y x))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (unsigned-byte-p-when-bound
                                   anti-bvplus getbit-of-+
                                   slice-of-+
                                   bvplus-of-plus-arg3
                                   +-of-minus-1-and-bv2
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-when-unsigned-byte-p
                                   <-when-unsigned-byte-p-alt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   ;<-of-bvchop-arg1
                                   <-becomes-bvlt-alt)))))

;whoa.
;make -alt version
(defthm equal-of-0-and-bvplus-of-bvuminus-32-31
  (implies (unsigned-byte-p 31 x)
           (equal (equal 0 (bvplus 32 x (bvuminus 31 y)))
                  (and (equal 0 x)
                       (equal 0 (bvchop 31 y)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt
                                          )
                                  (unsigned-byte-p-when-bound
                                   anti-bvplus getbit-of-+
                                   slice-of-+
                                   bvplus-of-plus-arg3
                                   +-of-minus-1-and-bv2
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-when-unsigned-byte-p
                                   <-when-unsigned-byte-p-alt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
;                                   <-of-bvchop-arg1
                                   <-becomes-bvlt-alt)))))




;more like this!
(defthm boolif-lemma-1
  (equal (boolif test (boolif test2 (boolif test x y) z) w)
         (boolif test (boolif test2 x z) w))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-lemma-2
  (equal (boolif test (boolif test2 z (boolif test x y)) w)
         (boolif test (boolif test2 z x) w))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolor-of-booland-of-not-same-1
  (equal (boolor x (booland y (not x)))
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-booland-of-not-same-2
  (equal (boolor x (booland (not x) y))
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolif-of-boolor-same-1
  (equal (boolif test (boolor test x) y)
         (boolor test y))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolif-of-boolor-same-2
  (equal (boolif test (boolor x test) y)
         (boolor test y))
  :hints (("Goal" :in-theory (enable boolor))))


;or should this be commuted (ignoring the not)?
(defthm booland-of-boolor-and-not-same-1
  (equal (booland (boolor x y) (not y))
         (booland x (not y))))

(defthm booland-of-boolor-and-not-same-2
  (equal (booland (boolor y x) (not y))
         (booland x (not y))))

(defthm booland-of-boolor-and-not-same-3
  (equal (booland (not y) (boolor x y))
         (booland x (not y))))

(defthm booland-of-boolor-and-not-same-4
  (equal (booland (not y) (boolor y x))
         (booland x (not y))))




;expensive?
(defthmd bvplus-tighten-when-no-overflow
  (implies (and (bvlt bigsize (bvplus bigsize k y) (expt 2 smallsize))
                (< smallsize bigsize)
                (natp smallsize)
                (natp bigsize))
           (equal (bvplus bigsize k y)
                  (bvplus smallsize k y)))
  :hints (("Goal" :in-theory (disable BVLT-TIGHTEN-WHEN-GETBIT-0))))

(defthm bvplus-commutative-2-sizes-differ
  (implies (and (syntaxp (quotep k)) ;gen?
                (bvlt bigsize (bvplus bigsize k y) (expt 2 smallsize)) ;can this loop or be expensive?
                (< smallsize bigsize)
                (natp smallsize)
                (natp bigsize))
           (equal (bvplus bigsize x (bvplus smallsize k y))
                  (bvplus bigsize k (bvplus bigsize x y))))
  :hints (("Goal" :use (:instance bvplus-commutative-2 (size bigsize) (z y) (y k))
           :in-theory (e/d (bvplus-tighten-when-no-overflow)
                           (bvplus-commutative-2
                            equal-of-bvplus-and-bvplus-cancel-arg3-and-arg3)))))

(defthm unsigned-byte-p-of-*-of-1/2
  (implies (and (natp size)
                (natp x))
           (equal (unsigned-byte-p size (* 1/2 x))
                  (and (INTEGERP (* 1/2 X))
                       (unsigned-byte-p (+ 1 size) x))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm bvchop-of-*-of-1/2-and-expt
  (implies (posp size)
           (equal (bvchop size (* 1/2 (expt 2 size)))
                  (* 1/2 (expt 2 size)))))

(defthm bvplus-associative-sizes-differ
  (implies (and (unsigned-byte-p bigsize z)
                (unsigned-byte-p smallsize x)
                (unsigned-byte-p smallsize y)
                (equal smallsize (+ -1 bigsize)) ;gen somehow?
                (natp smallsize)
                (natp bigsize)
                )
           (equal (bvplus bigsize (bvplus smallsize x y) z)
                  (if (bvlt bigsize (bvplus bigsize x y) (expt 2 smallsize))
                      (bvplus bigsize x (bvplus bigsize y z))
                    (bvplus bigsize (expt 2 smallsize) ;the carry
                            (bvplus bigsize x (bvplus bigsize y z)))
                    )))
  :hints (("Goal" :use (:instance bvplus-associative
                                  (size bigsize))
           :in-theory (e/d (expt-of-+
                            bvplus-tighten-when-no-overflow
                            unsigned-byte-p
                            bvplus bvmod bvchop-of-sum-cases
                            bvuminus
                            bvminus
                            bvlt
                            bvchop-identity
                            )
                           (bvplus-associative
                            unsigned-byte-p-when-bound
                            anti-bvplus getbit-of-+
                            slice-of-+
;+-BECOMES-BVPLUS-HACK-GEN
                            bvplus-of-plus-arg3
                            +-of-minus-1-and-bv2
                            plus-becomes-bvplus-free
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            plus-becomes-bvplus
                            plus-becomes-bvplus-arg1-free
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-becomes-bvlt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            minus-becomes-bv
                            plus-1-and-bvchop-becomes-bvplus
;                                   <-of-bvchop-arg1
                            <-becomes-bvlt-alt)))))

;use polarity?
(defthmd consp-when-true-listp
  (implies (true-listp x)
           (equal (consp x)
                  (not (equal x nil)))))

;use polarity?
(defthm bvlt-when-not-equal-2-3
  (implies (and (not (equal free (bvchop 2 x)))
                (equal free 3)) ;poor man's back chain limit
           (equal (bvlt 2 x 3)
                  t))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p


                                   bvlt
                                   bvchop-identity
                                   )
                                  (                                   unsigned-byte-p-when-bound
                                   anti-bvplus getbit-of-+
                                   slice-of-+
;+-BECOMES-BVPLUS-HACK-GEN
                                   bvplus-of-plus-arg3
                                   +-of-minus-1-and-bv2
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-when-unsigned-byte-p
                                   <-when-unsigned-byte-p-alt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   ;<-of-bvchop-arg1
                                   <-becomes-bvlt-alt)))))

;; (in-theory (disable ;<-BECOMES-BVLT-TABLE ;<-BECOMES-BVLT-TABLE-alt
;;                     ))

;move the minus to the other side
(defthm equal-of-0-and-bvplus-of-bvplus-of-bvuminus
  (implies (bvle 31 x y)
           (equal (equal '0 (bvplus '32 z (bvplus '31 (bvuminus '31 x) y)))
                  (equal (bvchop 31 x) (bvplus '32 z (bvchop 31 y)))))
  :hints (("Goal"
           :expand (bvlt 31 x y)
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
                            ;<-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            )))))

(defthm bvplus-of-bvuminus-same-3-2
  (implies (unsigned-byte-p 2 x)
           (equal (bvplus 3 x (bvuminus 2 x))
                  (if (equal 0 (bvchop 2 x))
                      0
                    4))))


;expensive?
(defthm bvlt-of-max-when-both-narrow
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y)
                )
           (equal (bvlt 32 (bvplus 32 x y) 4294967295)
                  t))
  :hints (("Goal"
           :expand ( ;(:with unsigned-byte-p (unsigned-byte-p 31 x))
;(:with unsigned-byte-p (unsigned-byte-p 32 y))
                    )
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
;                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            )))))


;this helps get the sizes to be equal
(defthmd bvplus-of-bvuminus-expand
  (implies (and (< smallsize size)
                (natp size)
                (natp smallsize)
                (unsigned-byte-p smallsize x)
                (unsigned-byte-p size y))
           (equal (bvplus size (bvuminus smallsize x) y)
                  (if (equal 0 (bvchop smallsize x))
                      (bvchop size y)
                    (bvplus size
                            (- (expt 2 smallsize) (expt 2 size))
                            (bvplus size (bvuminus size x) y)))))
  :hints (("Goal" ;:use (:instance bvplus-commutative-2 (size bigsize))
           :expand ((:with unsigned-byte-p (UNSIGNED-BYTE-P SIZE Y)))
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
;                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            ))           )))

;can get rid of this if we use bind-from-rules
(defthmd bvplus-when-<=-15-hack-for-sha1
  (implies (and (unsigned-byte-p 31 x)
                (bvle 32 x 15))
           (equal (BVPLUS '32 '1 x)
                  (BVPLUS 5 '1 x))))

;gen - do we already have something like this?
(DEFthm BVLT-OF-BVPLUS-31-14-5-1
  (equal (BVLT '31 '14 (BVPLUS '5 '1 x))
         (if (equal (bvchop 5 x) 31)
             nil
           (BVLT '31 '13 (bvchop 5 x))))
  :hints (("Goal" :in-theory (e/d (bvplus ;bvchop-of-sum-cases
                                   bvuminus
                                   bvchop-of-minus
                                   bvminus
                                   bvlt
                                   getbit-when-val-is-not-an-integer
                                   )
                                  (SLICE-OF-+
                                   anti-bvplus
                                   BVPLUS-OF-PLUS-ARG3
                                   getbit-of-+
                                   plus-becomes-bvplus-free
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   plus-becomes-bvplus
                                   plus-becomes-bvplus-arg1-free
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   minus-becomes-bv
                                   plus-1-and-bvchop-becomes-bvplus
                                   collect-constants-over-<
                                   <-becomes-bvlt-alt)))))


;move
(defthm bvchop-of-times-of-/-32
  (implies (rationalp x)
           (equal (bvchop 4 (* 1/32 x))
                  (if (integerp (* 1/32 x))
                      (slice 8 5 x)
                    0)))
  :hints (("Goal" :in-theory (e/d (slice logtail bvchop)
                                  (MOD-OF-EXPT-OF-2
                                   mod-of-expt-of-2-constant-version
                                   anti-slice
                                   )))))

;we may not want to do this if it's surrounded by a bvplus with a large size!
(defthmd bvplus-of-bvuminus-tighten-31-32
  (implies (and (bvle 31 x y)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvplus '32 (bvuminus '32 x) y)
                  (bvplus '31 (bvuminus '31 x) y))))

(defthmd sbvlt-of-bvplus-of-bvuminus-tighten-31-32
  (implies (and (bvle 31 x y)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (sbvlt 32 (bvplus '32 (bvuminus '32 x) y) z)
                  (sbvlt 32 (bvplus '31 (bvuminus '31 x) y) z)
                  ))
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-tighten-31-32)
           :in-theory (disable bvplus-of-bvuminus-tighten-31-32))))

;gen
(defthmd getbit-of-bvplus-of-bvuminus-when-bvle
  (implies (and (bvle 31 x y)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (getbit 31 (bvplus '32 (bvuminus '32 x) y))
                  0)))



(DEFTHM BVLT-WHEN-UNSIGNED-BYTE-P-BETTER-non-constant
  (IMPLIES (AND ;(SYNTAXP (QUOTEP K))
            (UNSIGNED-BYTE-P FREE X)
            (< FREE SIZE)
            (NATP SIZE)
            (NATP FREE))
           (EQUAL (BVLT SIZE X K)
                  (IF (BVLE SIZE (EXPT 2 FREE) K)
                      T (BVLT FREE X K))))
  :hints (("Goal" :use (:instance BVLT-WHEN-UNSIGNED-BYTE-P-BETTER)
           :in-theory (disable BVLT-WHEN-UNSIGNED-BYTE-P-BETTER))))

;do we need this?
(DEFTHM EQUAL-OF-BVPLUS-MOVE-BVMINUS-2-alt
  (IMPLIES (NATP SIZE)
           (EQUAL (EQUAL (BVPLUS SIZE K2 (BVPLUS SIZE (BVUMINUS SIZE K1) X))
                         (BVCHOP SIZE Y))
                  (EQUAL (BVPLUS SIZE K2 X)
                         (BVPLUS SIZE K1 Y))))
  :hints (("Goal" :use (:instance EQUAL-OF-BVPLUS-MOVE-BVMINUS-2)
           :in-theory (disable EQUAL-OF-BVPLUS-MOVE-BVMINUS-2))))

(DEFTHM EQUAL-OF-BVPLUS-MOVE-BVMINUS-2-alt-better
  (IMPLIES (NATP SIZE)
           (EQUAL (EQUAL y (BVPLUS SIZE K2 (BVPLUS SIZE (BVUMINUS SIZE K1) X)))
                  (and (unsigned-byte-p size y)
                       (EQUAL (BVPLUS SIZE K2 X)
                         (BVPLUS SIZE K1 Y)))))
  :hints (("Goal" :use (:instance EQUAL-OF-BVPLUS-MOVE-BVMINUS-2)
           :in-theory (disable EQUAL-OF-BVPLUS-MOVE-BVMINUS-2))))

(DEFTHM EQUAL-OF-BVPLUS-MOVE-BVMINUS-2-better
  (IMPLIES (NATP SIZE)
           (EQUAL (EQUAL y (BVPLUS SIZE K2 (BVPLUS SIZE X (BVUMINUS SIZE K1))))
                  (and (unsigned-byte-p size y)
                       (EQUAL (BVPLUS SIZE K2 X)
                         (BVPLUS SIZE K1 Y)))))
  :hints (("Goal" :use (:instance EQUAL-OF-BVPLUS-MOVE-BVMINUS-2)
           :in-theory (disable EQUAL-OF-BVPLUS-MOVE-BVMINUS-2))))



(defthm equal-of-bvplus-move-bvminus-alt-better
  (implies (natp size)
           (equal (equal y (bvplus size (bvuminus size k1) k2))
                  (and (unsigned-byte-p size y)
                       (equal (bvchop size k2)
                              (bvplus size k1 y)))))
  :hints (("Goal" :use (:instance equal-of-bvplus-move-bvminus)
           :in-theory (disable equal-of-bvplus-move-bvminus))))

(defthm <-of-bvchop-arg1
  (implies (unsigned-byte-p size y)
           (equal (< (bvchop size x) y)
                  (bvlt size x y)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt
                                          <-becomes-bvlt-alt
                                          <-of-bvplus-becomes-bvlt-arg1
                                          <-of-bvplus-becomes-bvlt-arg2
                                          <-becomes-bvlt-free
                                          )))))

(defthm bound-hack-for-sha1
  (implies (and (unsigned-byte-p 31 x)
                (< 0 x)
                (bvle 31 x x42)
;these show it doesn't overflow
                (unsigned-byte-p 31 x42)
                (unsigned-byte-p 2 x57)
                )
           (equal (equal (bvplus '32 x42 x57) (bvplus 32 4294967295 x))
                  nil))
  :hints (("Goal"
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            +-OF-MINUS-1-AND-BV2
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            ))           )))




;should always be a win
;make sure this doesn't unify -5 etc with x? - add not quotep x hyp?
(defthm <-of-negative-constant-and-unary-minus
  (implies (and (syntaxp (quotep k))
                (< k 0))
           (equal (< k (- x))
                  (< x (- k)))))

;ffixme just use this one (mot the one above)?
(defthm <-of-constant-and-unary-minus
  (implies (syntaxp (quotep k))
           (equal (< k (- x))
                  (< x (- k)))))

;introduces bv op
(defthmd minus-becomes-bv-2
  (implies (and (syntaxp (quotep x))
                (natp x)
                (unsigned-byte-p (+ 1 (lg x)) y)
                (not (bvlt (+ 1 (lg x)) x y)))
           (equal (+ x (- y))
                  (bvplus (+ 1 (lg x)) x (bvuminus (+ 1 (lg x)) y))))
  :hints (("Goal" :use (:instance minus-becomes-bv (free (+ 1 (lg x))))
           :in-theory (e/d (lg)( minus-becomes-bv)))))


;gen
(defthm another-bound-hack-for-sha1
  (implies (and (not (bvlt '31 x8 '2147483644)) ;x8 is large
                (unsigned-byte-p '31 x8)
                (unsigned-byte-p '31 x0)
                (bvlt '32 (bvplus '32 x0 x8) '2147483648)) ;adding x0 doesn't make it much bigger
           (equal (bvlt '31 x0 '4) ;so x0 is small
                  t))
  :hints (("Goal"
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            +-of-minus-1-and-bv2
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            ))           )))

;gen!
(defthm bvlt-of-bvplus-and-bvplus-of-bvchop-same
  (implies (and (unsigned-byte-p 31 x8)
                (unsigned-byte-p 31 y)
                (unsigned-byte-p 31 x11))
           (equal (BVLT '32 (BVPLUS '32 y x8) (BVPLUS '32 x11 (BVCHOP '2 x8)))
                  (BVLT '32 (BVPLUS '32 y (bvmult 31 4 (bvdiv 31 x8 4))) x11)))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y x8) (n 31) (m 2))

           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (
                            bvchop-of-* BVLT-OF-*-ARG3
                                         ;*-OF-2-BECOMES-BVMULT
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

(defthm bvlt-of-bvplus-and-bvplus-of-bvchop-same-another
  (implies (and (unsigned-byte-p 31 x8)
                (unsigned-byte-p 31 y))
           (equal (BVLT '32 (BVPLUS '32 y (bvchop 2 x8)) x8)
                  (BVLT '32 y (bvmult 31 4 (bvdiv 31 x8 4)))))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y x8) (n 31) (m 2))

           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

(defthm bvlt-of-bvplus-and-bvplus-of-bvchop-same-another2
  (implies (and (unsigned-byte-p 31 x11)
                (bvlt '32 (bvplus '32 x11 (bvplus '2 '1 x8)) '2147483648) ;no overflow
                )
           (equal (equal x8 (bvplus '31 x11 (bvplus '2 '1 x8)))
                  (and (unsigned-byte-p 31 x8)
                       (if (equal 3 (BVCHOP 2 X8))
                           (equal x8 (bvplus '31 x11 0))
                         (equal (bvmult 31 4 (bvdiv 31 x8 4)) (bvplus '31 x11 1))))))
  :hints (("Goal"
           :use (:instance split-bv (y x8) (n 31) (m 2))
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1
                            UNSIGNED-BYTE-P-FROM-BOUNDS)
                           (BVCHOP-OF-MINUS
                            PLUS-BECOMES-BVPLUS-FREE ;+-BECOMES-BVPLUS-HACK-GEN
                            PLUS-OF-MINUS-3-BV-5
                                                     bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT
                                                      TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                                     BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                                     getbit-of-plus
                                                     <-of-bvchop-arg1
                                                     <-becomes-bvlt-free
                                                     <-becomes-bvlt-free-alt
                                                     <-when-unsigned-byte-p
                                                     <-when-unsigned-byte-p-alt
                                                     <-becomes-bvlt
                                                     +-of-minus-1-and-bv2
                                                     minus-becomes-bv
                                                     plus-becomes-bvplus-arg1-free
                                                     bvuminus-of-+
                                                     bvplus-of-plus-arg3
                                                     plus-1-and-bvchop-becomes-bvplus ;fixme
                                                     bvminus-becomes-bvplus-of-bvuminus
                                                     <-becomes-bvlt
                                                     <-becomes-bvlt-alt
                                                     <-of-bvplus-becomes-bvlt-arg1
                                                     <-of-bvplus-becomes-bvlt-arg2
                                                     anti-bvplus getbit-of-+ plus-becomes-bvplus
                                                     bvlt-of-plus-arg1
                                                     bvlt-of-plus-arg2
                                                     slice-of-+
                                                     getbit-of-+ ;looped
                                                     ))           )))

;gen
(defthm bvlt-of-slice-and-slice
  (implies (and (not (bvlt free y x))
                (equal free 31) ;poor man's limit
                (unsigned-byte-p 31 y)
                )
           (equal (bvlt 29 (slice 30 2 y) (slice 30 2 x))
                  nil))
  :hints (("Goal"
           :use (:instance split-bv (y y) (n 31) (m 2))
           :in-theory (e/d (bvlt slice-bound-lemma-gen slice-bound-lemma-gen2
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (PLUS-BECOMES-BVPLUS-FREE ;+-BECOMES-BVPLUS-HACK-GEN
                            PLUS-OF-MINUS-3-BV-5 MINUS-BECOMES-BV-2
                                                     bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT
                                                      TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                                     BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                                     getbit-of-plus
                                                     <-of-bvchop-arg1
                                                     <-becomes-bvlt-free
                                                     <-becomes-bvlt-free-alt
                                                     <-when-unsigned-byte-p
                                                     <-when-unsigned-byte-p-alt
                                                     <-becomes-bvlt
                                                     +-of-minus-1-and-bv2
;                            minus-becomes-bv-2
                                                     minus-becomes-bv
                                                     plus-becomes-bvplus-arg1-free
                                                     bvuminus-of-+
                                                     bvplus-of-plus-arg3
                                                     plus-1-and-bvchop-becomes-bvplus ;fixme
                                                     bvminus-becomes-bvplus-of-bvuminus
                                                     <-becomes-bvlt
                                                     <-becomes-bvlt-alt
                                                     <-of-bvplus-becomes-bvlt-arg1
                                                     <-of-bvplus-becomes-bvlt-arg2
                                                     anti-bvplus getbit-of-+ plus-becomes-bvplus
                                                     bvlt-of-plus-arg1
                                                     bvlt-of-plus-arg2
                                                     slice-of-+
                                                     getbit-of-+ ;looped
                                                     ))           )))

(defthm bvlt-of-bvplus-and-bvplus-of-bvchop-same3
  (implies (and (unsigned-byte-p 31 x8)
                (unsigned-byte-p 31 y)
                (unsigned-byte-p 31 x11))
           (equal (BVLT '32 (BVPLUS '32 y x8) (BVPLUS '32 x11 (bvplus 2 1 x8)))
                  (if (equal 3 (BVCHOP 2 X8))
                      (BVLT '32 (BVPLUS '32 y x8) (BVPLUS '32 x11 0))
                    (BVLT '32 (BVPLUS '32 y (bvmult 31 4 (bvdiv 31 x8 4))) (bvplus 32 1 x11)))))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y x8) (n 31) (m 2))

           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;gen
(defthm <-of-x-and-pieces
  (implies (unsigned-byte-p 31 x)
           (not (< (+ 3 (* 4 (slice 30 2 x))) x)))
  :hints (("Goal" :use (:instance split-bv (y x) (n 31) (m 2))
           ;;           :use (:instance <-of-bvcat
           ;;                           (x (+ 3 (* 4 (slice 30 2 x))))
           ;;                           (HIGHSIZE 29)
           ;;                           (HIGHVAL (slice 30 2 x))
           ;;                           (LOWSIZE 2)
           ;;                           (LOWVAL (bvchop 2 x)))
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         )))))


(defthm <-of-+-and-+-cancel-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (< (+ k2 X) (+ k1 y))
                  (if (<= k1 k2)
                      (< (+ (- k2 k1) x) y)
                    (< x (+ (- k1 k2) y))))))

;gen
(defthm <-of-times-of-slice-same
  (implies (unsigned-byte-p 31 x)
           (equal (< (+ y x) (* 4 (slice 30 2 x)))
                  (< (+ y (bvchop 2 x)) 0)))
  :hints (("Goal" :use (:instance split-bv (y x) (n 31) (m 2))
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (
                            bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                             times-4-of-slice-becomes-logapp
                            bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                            getbit-of-plus
                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            +-of-minus-1-and-bv2
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            )))))

(defthm slice-linear
  (implies (unsigned-byte-p 31 x)
           (<= (+ 3 (* 4 (slice 30 2 x))) (+ 4 x)))
  :rule-classes ((:linear))
  :hints (("Goal" :use (:instance split-bv (y x) (n 31) (m 2))
           ;;           :use (:instance <-of-bvcat
           ;;                           (x (+ 3 (* 4 (slice 30 2 x))))
           ;;                           (HIGHSIZE 29)
           ;;                           (HIGHVAL (slice 30 2 x))
           ;;                           (LOWSIZE 2)
           ;;                           (LOWVAL (bvchop 2 x)))
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         )))))

(defthm sha1-helper-100
  (implies (and (BVLT '32 (BVPLUS '32 '4 x8) x11)
                (unsigned-byte-p 31 x8)
                (unsigned-byte-p 31 x11))
           (equal (BVLT '32 (BVPLUS '32 '3 (BVMULT '31 '4 (SLICE '30 '2 x8))) x11)
                  t))
  :hints (("Goal"
           :cases ((< (+ 4 X8) (+ 3 (* 4 (SLICE 30 2 X8)))))
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         )))))

(defthm bvlt-of-bvplus-and-bvplus-cancel-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (unsigned-byte-p 31 k1)
                (unsigned-byte-p 31 k2)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 32 (bvplus 32 k2 x) (bvplus 32 k1 y))
                  (if (<= k1 k2)
                      (bvlt 32 (bvplus 32 (- k2 k1) x) y)
                    (bvlt 32 x (bvplus 32 (- k1 k2) y)))))
  :hints (("Goal"
           :cases ((< (+ 4 X8) (+ 3 (* 4 (SLICE 30 2 X8)))))
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           ( bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                          PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

(defthm bvlt-of-bvplus-and-bvplus-of-bvchop-same4
  (implies (and (equal y 1) ;gen
                (unsigned-byte-p 31 x8)
                (unsigned-byte-p 31 y)
                (unsigned-byte-p 31 x11))
           (equal (BVLT '32 (BVPLUS '32 x11 (bvplus 2 y x8)) x8)
                  (if (equal 3 (BVCHOP 2 X8))
                      (BVLT '32 x11 x8)
                    (BVLT '32 (bvplus 32 y x11) (bvmult 31 4 (bvdiv 31 x8 4))))))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y x8) (n 31) (m 2))

           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

(defthm bvlt-of-bvplus-and-bvplus-of-bvchop-same5
  (implies (and (equal y 1) ;gen
                (unsigned-byte-p 31 x8)
                (unsigned-byte-p 31 y)
                (unsigned-byte-p 31 x11)
                ;no overflow:
                (BVLT '32 (BVPLUS '32 x11 (BVPLUS '2 '1 x8)) '2147483648)
                )
           (equal (BVLT '31 (BVPLUS '31 x11 (bvplus 2 y x8)) x8)
                  (if (equal 3 (BVCHOP 2 X8))
                      (BVLT '32 x11 x8)
                    (BVLT '32 (bvplus 32 y x11) (bvmult 31 4 (bvdiv 31 x8 4))))))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y x8) (n 31) (m 2))

           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;gen
(defthm sha1-lemma-7
  (implies (and (not (bvlt '31 x11 x8))
                (unsigned-byte-p 31 x11)
                (unsigned-byte-p 31 x8))
           (equal (bvlt '32 (bvplus '32 '1 x11) (bvmult '31 '4 (slice '30 '2 x8)))
                  nil))
  :hints (("Goal"
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;; (BVLT 31 (BVMULT 31 4 X) 2147483645)

(defthm bvplus-of-bvmult-tighten
  (equal (bvplus '32 '3 (bvmult '31 '4 x))
         (bvplus '31 '3 (bvmult '31 '4 x)))
  :hints (("Goal"
           :in-theory (e/d (bvlt
                            bvcat logapp
                            bvplus
                            bvmult
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))




(defthm lg-of-expt-gen
  (implies (integerp n)
           (equal (lg (expt 2 n))
                  (if (natp n)
                      n
                    -1)))
  :hints (("Goal" :in-theory (enable lg))))

(defthm bvchop-of-lg
  (implies (and (POWER-OF-2P K)
                (posp k))
           (equal (bvchop (LG K) K)
                  0))
  :hints (("Goal"
           :in-theory (e/d (POWER-OF-2P
                            lg
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           ()))))


(defthm bvlt-of-lg
  (implies (and (POWER-OF-2P K)
                (posp k))
           (equal (BVLT (LG K) Y K)
                  nil))
  :hints (("Goal"
           :in-theory (e/d (POWER-OF-2P
                            bvlt
                            bvplus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;alternate phrasing for the bvcat
(defthm bvlt-of-bvcat-arg2-lemma
  (implies (and (equal size (+ lowsize highsize))
                (natp lowsize)
                (unsigned-byte-p lowsize y)
                (unsigned-byte-p highsize x)
                (natp highsize))
           (equal (bvlt size
                        (bvplus size y (bvmult size (expt 2 lowsize) x))
                        k)
                  (or (bvlt highsize
                            x (slice (+ -1 size) lowsize k))
                      (and (equal (bvchop highsize x)
                                  (slice (+ -1 size) lowsize k))
                           (bvlt lowsize y k)))))
  :hints (("Goal" :use (:instance bvlt-of-bvcat-arg2)
           :in-theory (e/d (bvcat logapp bvmult)
                           ( <-WHEN-UNSIGNED-BYTE-P-ALT ;looped
                            bvplus-subst-value ;looped
                            bvplus-trim-leading-constant ;looped
                             bvlt-of-bvcat-arg2 bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult
                            )))))

(defthm bvlt-of-bvcat-arg2-lemma-constant-version
  (implies (and (syntaxp (quotep kk))
                (power-of-2p kk)
                (integerp size)
                (natp (lg kk))
                (unsigned-byte-p (lg kk) y)
                (unsigned-byte-p (- size (lg kk)) x)
                (natp (- size (lg kk))))
           (equal (bvlt size
                        (bvplus size y (bvmult size kk x))
                        k)
                  (or (bvlt (- size (lg kk))
                            x (slice (+ -1 size) (lg kk) k))
                      (and (equal (bvchop (- size (lg kk)) x)
                                  (slice (+ -1 size) (lg kk) k))
                           (bvlt (lg kk) y k)))))
  :hints (("Goal" :use (:instance bvlt-of-bvcat-arg2-lemma
                                  (highsize (- size (lg kk)))
                                  (lowsize (lg kk)))
           :in-theory (e/d (;POWER-OF-2P
                            )
                           (bvlt-of-bvcat-arg2-lemma
                               <-WHEN-UNSIGNED-BYTE-P ;looped
                               SLICE-TIGHTEN-TOP-FREE
                               BVPLUS-SUBST-VALUE
                               BVPLUS-TRIM-LEADING-CONSTANT
                               )))))

(defthm bvlt-of-bvcat-arg3-lemma
  (implies (and (equal size (+ lowsize highsize))
                (natp lowsize)
                (unsigned-byte-p lowsize y)
                (unsigned-byte-p highsize x)
                (natp highsize))
           (EQUAL (BVLT SIZE K (bvplus size y (bvmult size (expt 2 lowsize) x)))
                  (OR (BVLT HIGHSIZE (SLICE (+ -1 SIZE) LOWSIZE K)
                            X)
                      (AND (EQUAL (BVCHOP HIGHSIZE X)
                                  (SLICE (+ -1 SIZE) LOWSIZE K))
                           (BVLT LOWSIZE K Y)))))
  :hints (("Goal" :use (:instance bvlt-of-bvcat-arg3)
           :in-theory (e/d (bvcat logapp bvmult)
                           (<-WHEN-UNSIGNED-BYTE-P ;looped
                            bvplus-subst-value           ;looped
                            bvplus-trim-leading-constant ;looped
                             bvlt-of-bvcat-arg3
                            bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult
                            )))))

(defthm bvlt-of-bvcat-arg3-lemma-constant-version
  (implies (and (syntaxp (quotep kk))
                (power-of-2p kk)
                (natp (lg kk))
                (integerp size)
                (unsigned-byte-p (lg kk) y)
                (unsigned-byte-p (- size (lg kk)) x)
                (natp (- size (lg kk))))
           (EQUAL (BVLT SIZE K (bvplus size y (bvmult size kk x)))
                  (OR (BVLT (- SIZE (LG KK)) (SLICE (+ -1 SIZE) (LG KK) K)
                            X)
                      (AND (EQUAL (BVCHOP (- SIZE (LG KK)) X)
                                  (SLICE (+ -1 SIZE) (LG KK) K))
                           (BVLT (LG KK) K Y)))))
  :hints (("Goal" :use (:instance bvlt-of-bvcat-arg3-lemma (lowsize (lg kk))
                                  (highsize (- size (lg kk))))
           :in-theory (e/d ( ;POWER-OF-2P
                            )
                           (bvlt-of-bvcat-arg3-lemma
                            <-WHEN-UNSIGNED-BYTE-P ;looped
                            SLICE-TIGHTEN-TOP-FREE
                            BVPLUS-SUBST-VALUE
                            BVPLUS-TRIM-LEADING-CONSTANT
                            )))))

(in-theory (disable BVLT-OF-PLUS-1-ARG2))

;if slice x not <  slice y
;then x < y becomes slices equal and low bits <

(defthm bvlt-when-not-bvlt-of-slice-and-slice
  (implies (and (not (bvlt free (slice 30 2 x) (slice 30 2 y))) ;do we correcty match free vars in hyps of the form (not x) ?
                (equal 29 free) ;poor man's limit - hope we can still match the free var
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 31 x y)
                  (and (equal (slice 30 2 x)
                              (slice 30 2 y))
                       (bvlt 2 (bvchop 2 x) (bvchop 2 y)))))
  :hints (("Goal"
           :use ((:instance split-bv (y y) (n 31) (m 2))
                 (:instance split-bv (y x) (n 31) (m 2)))
           :in-theory (e/d (POWER-OF-2P
                            bvlt
                            bvplus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1
                            bvcat logapp)
                           (;sbvlt-rewrite
                            BVCHOP-IDENTITY-CHEAP
                            bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                            PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                             TIMES-4-OF-SLICE-BECOMES-LOGAPP
                            BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                            getbit-of-plus
                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            +-of-minus-1-and-bv2
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            ))           )))

(in-theory (disable <-WHEN-UNSIGNED-BYTE-P <-BECOMES-BVLT-FREE <-BECOMES-BVLT-ALT))

(defthm slice-is-max2
  (implies (and (unsigned-byte-p 31 x)
                (<= 2147483644 x))
           (equal (slice 30 2 x)
                  (+ -1 (expt 2 29))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p slice logtail) (anti-slice)))))

(in-theory (disable <-OF-BVPLUS-BECOMES-BVLT-ARG2
                    <-OF-BVCHOP-ARG1
                    <-WHEN-UNSIGNED-BYTE-P-ALT
                    <-BECOMES-BVLT-FREE-ALT))

;; (thm
;;  (implies (and (<= 4 y)
;;                (<= (* 4 (slice 30 2 y)) x)
;;                (unsigned-byte-p 31 x)
;;                (unsigned-byte-p 31 y)
;;                (<= 4 x)
;;                (<= (* 4 (slice 30 2 x)) y)
;;                (<= x y))
;;           (equal (slice 30 2 y) (slice 30 2 x)))
;;  :hints (("Goal"
;;           :in-theory (disable slice-bound-lemma-gen))))

(defthmd bvlt-split
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 31 x y)
                  (or (bvlt 29
                            (slice 30 2 x)
                            (slice 30 2 y))
                      (and (equal (slice 30 2 x)
                                  (slice 30 2 y))
                           (bvlt 2 (bvchop 2 x)
                                 (bvchop 2 y))))))
  :hints (("Goal"
           :use ((:instance split-bv (y y) (n 31) (m 2))
                 (:instance split-bv (y x) (n 31) (m 2)))
           :in-theory (e/d (POWER-OF-2P
                            bvcat logapp
                            bvlt
                            bvplus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* BVLT-OF-*-ARG3 ;*-OF-2-BECOMES-BVMULT ;+-BECOMES-BVPLUS-HACK-GEN
                                         PLUS-BECOMES-BVPLUS-FREE PLUS-OF-MINUS-3-BV-5
                                          TIMES-4-OF-SLICE-BECOMES-LOGAPP
                                         BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE LOGAPP-EQUAL-REWRITE
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))


(defthm bvlt-when-not-bvlt-of-slice-and-slice2
  (implies (and (not (bvlt free (slice 30 2 x) (slice 30 2 y))) ;do we correctly match free vars in hyps of the form (not x) ?
                (equal free 29) ;poor man's limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 31 y x)
                  (or (bvlt 29
                            (slice 30 2 y)
                            (slice 30 2 x))
                      (bvlt 2 (bvchop 2 y)
                            (bvchop 2 x)))))
  :hints (("Goal" :in-theory (disable EQUAL-OF-BVPLUS-CONSTANT-AND-CONSTANt-ALT
                                      SLICE-BOUND-LEMMA-GEN2
                                      BVLT-OF-SLICE-29-30-2
                                      SLICE-BOUND-LEMMA-GEN
                                      ;BVMULT-OF-EXPT2
                                      )
           :use (:instance bvlt-split (x y) (y x)))))

;use polarity
(defthm bvlt-of-max-2
  (equal (BVLT '2 x '3)
         (not (equal 3 (bvchop 2 x)))))

;use polarity??
(defthm equal-of-slice-and-slice-when-bvchops-same
  (implies (and (equal free1 (bvchop 2 x))
                (equal Free2 (bvchop 2 y))
                (equal free1 free2)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y)
                )
           (equal (equal (slice 30 2 x) (slice 30 2 y))
                  (equal x y)))
  :hints (("Goal" :use ((:instance split-bv (y y) (n 31) (m 2))
                        (:instance split-bv (y x) (n 31) (m 2)))
           :in-theory (disable BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE))))


(defthmd +-becomes-bvplus-hack-gen
  (implies (and (unsigned-byte-p freesize x)
                (natp freesize) ;drop?
                )
           (equal (binary-+ 1 x)
                  (bvplus (+ 1 freesize) 1 x)))
  :hints
  (("Goal" :in-theory (e/d (bvplus)
                           (anti-bvplus bvplus-opener
                                        GETBIT-OF-+
                                        BVPLUS-OF-PLUS-ARG3
                                        bvlt-of-plus-arg1
                                        bvlt-of-plus-arg2
                                        plus-becomes-bvplus)))))

(defthm sha1-lemma-8
  (implies (and (not (bvlt 31 x11 x8))
                (not (equal 0 x8))
                (unsigned-byte-p 31 x11)
                (unsigned-byte-p 31 x8))
           (equal (equal (bvplus '31 '1 x11) (bvmult '31 '4 (slice '30 '2 x8)))
                  (if (equal (bvchop 31 x11) 2147483647)
                      (equal 0 (bvmult '31 '4 (slice '30 '2 x8)))
                    nil)))
  :hints (("Goal"
           :use ((:instance split-bv (y x8) (n 31) (m 2)))
           :in-theory (e/d (power-of-2p
                            bvmult
                            bvcat logapp
                            bvlt
                            bvplus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;gen
(defthm slice-when-bvlt-30-2-31-4
  (implies (and (bvlt 31 x free)
                (unsigned-byte-p 31 free)
                (bvle 31 free 4))
           (equal (slice '30 '2 x)
                  0))
  :hints (("Goal"
           :in-theory (e/d (bvlt
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;gen!
(defthm equal-of-0-and-bvchop-when-large
  (implies (and (not (BVLT '31 x5 '2147483644))
                (unsigned-byte-p 31 x5))
           (equal (EQUAL '0 (BVCHOP '2 x5))
                  (equal x5 2147483644)))
  :hints (("Goal"
           :cases ((EQUAL X5 2147483645)
                   (EQUAL X5 2147483646)
                   (EQUAL X5 2147483647))


           :in-theory (e/d (bvlt
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

;gen
;crud. i found a case where we need free-match all for this rule...  well, now i have that feature!
;expensive?
(defthm slice-when-large
  (implies (and (not (bvlt '31 x free)) ;bvlt version? or use polarity on (not (bvlt x constant))?
                (bvle 31 2147483644 free)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 free))
           (equal (slice 30 2 x)
                  536870911))
  :hints (("Goal"
           :cases ((equal x5 2147483645)
                   (equal x5 2147483646)
                   (equal x5 2147483647))
           :in-theory (e/d (bvlt
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         ))           )))

(defthm slice-when-large-alt
  (implies (and (syntaxp (quotep y))
                (bvle 31 2147483644 y)
                (not (equal free (slice 30 2 x)))
                (equal 536870911 free) ;poor man's limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt '31 x y)
                  t))
  :hints (("Goal" :use (:instance slice-when-large (free y))
           :in-theory (disable slice-when-large))))

;prove by opening up less?
;better phrasing
;two values are close and the smaller has low bits of 0, then their slices are equal
(defthm sha1-lemma-9
  (implies (and (bvlt 31 x24 (bvplus 31 free x5))
                (syntaxp (quotep free))
                (bvle 31 free 4)
                (bvle 31 x5 x24) ;limit?!
                (equal 0 (bvchop 2 x5)) ;limit?! gen (but if the bvchop is higher, they must be closer to have the same top slices?)
                (unsigned-byte-p 31 x5)
                (unsigned-byte-p 31 x24))
           (equal (equal (slice 30 2 x5)
                         (slice 30 2 x24))
                  t))
  :hints (("Goal"
           :cases ((equal x5 2147483645)
                   (equal x5 2147483646)
                   (equal x5 2147483647))
           :in-theory (e/d (MOD-SUM-CASES
                            bvlt bvplus slice logtail bvchop
                                 bvchop-of-sum-cases sbvlt
                                 bvchop-when-i-is-not-an-integer
                                 bvchop-when-top-bit-1)
                           (anti-slice
                            MOD-OF-EXPT-OF-2
                            mod-of-expt-of-2-constant-version
                            bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                            plus-becomes-bvplus-free plus-of-minus-3-bv-5
                             times-4-of-slice-becomes-logapp
                            bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                            getbit-of-plus
                            <-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt
                            <-when-unsigned-byte-p
                            <-when-unsigned-byte-p-alt
                            <-becomes-bvlt
                            +-of-minus-1-and-bv2
                            minus-becomes-bv
                            plus-becomes-bvplus-arg1-free
                            bvuminus-of-+
                            bvplus-of-plus-arg3
                            plus-1-and-bvchop-becomes-bvplus ;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2
                            anti-bvplus getbit-of-+ plus-becomes-bvplus
                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2
                            slice-of-+
                            getbit-of-+ ;looped
                            ))           )))

(defthm sha1-lemma-9-alt
  (implies (and (bvlt 31 x24 (bvplus 31 free x5))
                (syntaxp (quotep free))
                (bvle 31 free 4)
                (bvle 31 x5 x24)
                (equal 0 (bvchop 2 x5))
                (unsigned-byte-p 31 x5)
                (unsigned-byte-p 31 x24))
           (equal (equal (slice 30 2 x24)
                         (slice 30 2 x5))
                  t))
  :hints (("Goal" :use (:instance sha1-lemma-9)
           :in-theory (disable sha1-lemma-9))))

(in-theory (disable <-OF-BVPLUS-BECOMES-BVLT-ARG1 <-BECOMES-BVLT
                    BVLT-OF-PLUS-ARG1
                    BVLT-OF-PLUS-ARG2
                    PLUS-BECOMES-BVPLUS
                    GETBIT-OF-+
                    BVPLUS-OF-PLUS-ARG3
                    ))

;free vars!
(defthm UNSIGNED-BYTE-P-of-+-when-both-smaller
  (implies (and (unsigned-byte-p x-size x)
                (unsigned-byte-p y-size y)
                (< x-size 31)
                (< y-size 31)
                (natp x-size)
                (natp y-size)
                )
           (equal (UNSIGNED-BYTE-P '31 (+ x y))
                  t))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p bvlt bvplus UNSIGNED-BYTE-P-FORCED)
                                  (anti-bvplus)))))


;gen!
;restrict?
(defthmd sha1-lemma-0
  (implies (and (not (bvlt '31 x8 '2147483644))
                (not (bvlt '31 x0 '4))
                (equal x38 (bvplus '31 x0 x8))
                (unsigned-byte-p 31 x0)
                (unsigned-byte-p 31 x8)
                )
           (equal (bvlt '31 x38 x8)
                  t))
  :hints (("Goal"
           :use ((:instance split-bv (y x8) (n 31) (m 2)))
           :in-theory (e/d (power-of-2p
                            bvmult
                            bvcat logapp
                            bvlt
                            bvplus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         )))))

;would like to substitute instead of using this rule directly?
(defthmd sha1-lemma-0b
  (implies (and ;(not (bvlt '31 x8 '2147483644))
;(not (bvlt '31 x0 '4))
            (not (BVLT '32 (BVPLUS '32 x0 x8) '2147483648)) ;overflow
            (equal x38 (bvplus '31 x0 x8))
            (unsigned-byte-p 31 x0)
            (unsigned-byte-p 31 x8)
            )
           (equal (bvlt '31 x38 x8)
                  t))
  :hints (("Goal"
           :use ((:instance split-bv (y x8) (n 31) (m 2)))
           :in-theory (e/d (power-of-2p
                            bvmult
                            bvcat logapp
                            bvlt
                            bvplus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (bvchop-of-* bvlt-of-*-arg3 ;*-of-2-becomes-bvmult ;+-becomes-bvplus-hack-gen
                                         plus-becomes-bvplus-free plus-of-minus-3-bv-5
                                          times-4-of-slice-becomes-logapp
                                         bvcat-slice-same bvcat-equal-rewrite-alt bvcat-equal-rewrite logapp-equal-rewrite
                                         getbit-of-plus
                                         <-of-bvchop-arg1
                                         <-becomes-bvlt-free
                                         <-becomes-bvlt-free-alt
                                         <-when-unsigned-byte-p
                                         <-when-unsigned-byte-p-alt
                                         <-becomes-bvlt
                                         +-of-minus-1-and-bv2
                                         minus-becomes-bv
                                         plus-becomes-bvplus-arg1-free
                                         bvuminus-of-+
                                         bvplus-of-plus-arg3
                                         plus-1-and-bvchop-becomes-bvplus ;fixme
                                         bvminus-becomes-bvplus-of-bvuminus
                                         <-becomes-bvlt
                                         <-becomes-bvlt-alt
                                         <-of-bvplus-becomes-bvlt-arg1
                                         <-of-bvplus-becomes-bvlt-arg2
                                         anti-bvplus getbit-of-+ plus-becomes-bvplus
                                         bvlt-of-plus-arg1
                                         bvlt-of-plus-arg2
                                         slice-of-+
                                         getbit-of-+ ;looped
                                         )))))
;would like to just substitute...
;seemed to loop!
(defthmd bvlt-of-bvplus-same-subst
  (implies (and (equal var (bvplus size x y))
                (natp size))
           (equal (bvlt size var x)
                  (if (equal 0 (bvchop size y))
                      nil (bvle size (bvuminus size y) x))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-same)
           :in-theory (disable bvlt-of-bvplus-same))))

;gen!
(defthm equal-of-constant-and-bv-array-read-of-bv-array-write-of-constant
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (not (equal k2 k1))
                (unsigned-byte-p 8 k1)
                (equal 4 (len data))
                (natp index)
                (< index 4))
           (equal (equal k2 (bv-array-read '8 '4 '3 (bv-array-write '8 '4 index k1 data)))
                  (and (unsigned-byte-p 8 k2)
                       (not (equal (bvchop 2 index) 3))
                       (equal k2 (bv-array-read '8 '4 '3 data)))))
  :hints (("Goal" :in-theory (enable bv-array-read-of-bv-array-write-both))))

;does this subsume some stuff?
(defthm bvlt-when-not-max
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 n)))
                (not (equal k free))
                (equal free x) ;poor man's limit
                (unsigned-byte-p n x)
                (natp n))
           (equal (bvlt n x k)
                  t))
  :hints (("Goal" :in-theory (enable bvlt))))

;move up?
(in-theory (disable bvchop-of-*))

;; (defthm slice-of-bvmult-of-expt
;;   (implies (and (equal k (expt 2 n)) ;to match better
;;                 (<= (+ 1 size2) size)
;;                 (<= n size2)
;;                 (natp n)
;;                 (integerp size)
;;                 (natp size2))
;;            (equal (slice size2 n (bvmult size k x)) ;let the n's differ
;;                   (bvchop (- (+ 1 size2) n) x)))
;;   :hints (("Goal" :in-theory (enable bvmult))))

(in-theory (disable PLUS-BECOMES-BVPLUS-FREE))

(in-theory (disable BVPLUS-OF-PLUS BVPLUS-OF-PLUS2 SLICE-OF-+ PLUS-1-AND-BVCHOP-BECOMES-BVPLUS
                    BVUMINUS-OF-+
                    ;BVUMINUS-OF-PLUS
                    MINUS-BECOMES-BV
                    TIMES-4-OF-SLICE-BECOMES-LOGAPP))

;gen
(defthm +-of-minus-of-shifted-slice-of-same
  (implies (and (equal k (expt 2 smallsize))
                (unsigned-byte-p bigsize y) ;can't really drop..
                (natp bigsize)
                (natp smallsize)
                (<= smallsize bigsize))
           (equal (+ y (- (* k (slice (+ -1 BIGSIZE) smallsize y))))
                  (bvchop smallsize y)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp natp) ( LOGAPP-EQUAL-REWRITE))
            :use (:instance split-bv (n bigsize) (m smallsize)))))

(defthm +-of-minus-of-shifted-slice-of-same-alt
  (implies (and (equal k (expt 2 smallsize))
                (unsigned-byte-p bigsize y) ;can't really drop..
                (natp bigsize)
                (natp smallsize)
                (<= smallsize bigsize))
           (equal (+ y x (- (* k (slice (+ -1 BIGSIZE) smallsize y))))
                  (+ x (bvchop smallsize y))))
  :hints (("Goal" :use (:instance +-of-minus-of-shifted-slice-of-same)
           :in-theory (disable +-of-minus-of-shifted-slice-of-same))))

(defthm +-of-minus-of-shifted-slice-of-same-alt2
  (implies (and (equal k (expt 2 smallsize))
                (unsigned-byte-p bigsize y) ;can't really drop..
                (natp bigsize)
                (natp smallsize)
                (<= smallsize bigsize))
           (equal (+ y x z (- (* k (slice (+ -1 BIGSIZE) smallsize y))))
                  (+ x z (bvchop smallsize y))))
  :hints (("Goal" :use (:instance +-of-minus-of-shifted-slice-of-same)
           :in-theory (disable +-of-minus-of-shifted-slice-of-same))))

(defthm equal-of-slice-and-constant-when-equal-of-bvchop-and-constant
  (implies (and (syntaxp (or (want-to-strengthen (equal k2 (slice high low y)))
                             (want-to-strengthen (equal (slice high low y) k2))))
                (syntaxp (quotep k2))
                (equal (bvchop low y) k1)
                (syntaxp (quotep k1))
                (natp low)
                (natp high)
                (<= low high))
           (equal (equal k2 (slice high low y))
                  (and (unsigned-byte-p (- (+ 1 high) low) k2)
                       (equal (bvchop (+ 1 high) y) (bvcat (- (+ 1 high) low) k2 low k1)))))
  :hints (("Goal" :in-theory (disable BVCHOP-SUBST-CONSTANT SLICE-SUBST-CONSTANT))))

(in-theory (disable PLUS-BECOMES-BVPLUS-ARG1-FREE))

;gen
(defthm bvchop-of-+-of-*-lemma
  (implies (and (Integerp x)
                (Integerp k))
           (equal (BVCHOP 2 (+ K (* 4 x)))
                  (BVCHOP 2 K))))

;gen
(defthm slice-of-+-of-*-lemma
  (implies (and (integerp x)
   ;             (natp size)
;                (integerp k)
                )
           (equal (slice (+ -1 size) 2 (+ (bvchop 2 k) (* 4 x)))
                  ;simp:
                  (slice (+ -1 size) 2 (* 4 x))))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

;prove by opening less
(defthm slice-of-*-of-expt
  (implies (and (integerp x)
                (integerp size))
           (equal (slice size 2 (* 4 x))
                  (slice (+ -2 size) 0 x)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (anti-slice))))
  )

(defthm equal-of-bvchop-cancel-slice-rule
  (implies (and (integerp z1)
                (integerp z2)
                (integerp z3)
                (integerp k)
                (natp size)
                (unsigned-byte-p size k)
                )
           (equal (EQUAL (BVCHOP SIZE (+ K z1)) (BVCHOP SIZE (+ (BVCHOP 2 K) z3)))
                  (EQUAL (BVCHOP SIZE (+ z1 (* (expt 2 2) (slice (+ -1 size) 2 k))))
                         (BVCHOP SIZE (+ z3)))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp natp) ( LOGAPP-EQUAL-REWRITE))
           :use (:instance split-bv (y k) (n size) (m 2)))))

(defthm equal-of-bvchop-cancel-slice-rule-alt
  (implies (and (integerp z1)
                (integerp z2)
                (integerp z3)
                (integerp k)
                (unsigned-byte-p size k)
                )
           (equal (EQUAL (BVCHOP SIZE (+ z1 K z2)) (BVCHOP SIZE (+ (BVCHOP 2 K) z3)))
                  (EQUAL (BVCHOP SIZE (+ z1 (* (expt 2 2) (slice (+ -1 size) 2 k)) z2))
                         (BVCHOP SIZE (+ z3)))))
  :hints (("Goal" :use (:instance equal-of-bvchop-cancel-slice-rule (z1 (+ z1 z2)))
           :in-theory (disable equal-of-bvchop-cancel-slice-rule))))

;easier proof?
;; ;combine with other case?
;; ;gen!
;; (defthm bvplus-commutative-2-sizes-differ-other-case
;;   (implies (and (syntaxp (quotep k)) ;gen?
;;                 (not (bvlt bigsize (bvplus bigsize k y) (expt 2 smallsize))) ;there is overflow
;;                 (< smallsize bigsize)

;;                 (unsigned-byte-p bigsize y) ;okay?
;;                 (unsigned-byte-p bigsize k) ;okay?
;;                 ;(equal 32 bigsize) ;gen!
;;                 (natp bigsize)
;;                 (<= smallsize bigsize)
;;                 (equal 2 smallsize) ;gen!
;;                 ;(equal 1 k) ;gen!
;;                 (integerp x)
;;                 (natp smallsize)
;;                 (natp bigsize))
;;            (equal (bvplus bigsize x (bvplus smallsize k y))
;;                   (bvplus bigsize k
;;                           (bvplus bigsize
;;                                   ;have to subtract this back out:
;;                                   (bvuminus bigsize (bvmult bigsize (expt 2 smallsize)
;;                                                                     (slice (+ -1 bigsize) smallsize (bvplus bigsize k y))))
;;                                   (bvplus bigsize
;;                                           x y)))))
;;   :otf-flg t
;;   :hints (("Goal" ;:use (:instance bvplus-commutative-2 (size bigsize) (z y) (y k))
;; ;;            :use (:instance bvchop-of-sum-cases (size 30)
;; ;;                            (i1 (SLICE 31 2 K))
;; ;;                            (i2 (SLICE 31 2 Y)))
;;            :restrict ((bvchop-of-sum-cases ((size 30) (i1 (SLICE 31 2 K)) (i2 (SLICE 31 2 Y)))
;;                                             ((size (+ -2 BIGSIZE)) (i1 (SLICE (+ -1 BIGSIZE) 2 K)) (i2 (SLICE (+ -1 BIGSIZE) 2 Y)))
;;                                             ((size 2) (i1 k) (i2 y))))
;;            :in-theory (e/d (bvplus-tighten-when-no-overflow bvplus bvlt SLICE-OF-SUM-CASES bvmult
;;                                                             bvuminus
;;                                                             bvminus
;;                                                             bvchop-of-sum-cases
;;                                                             )
;;                            (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
;;                             bvplus-commutative-2
;;                             BVMULT-OF-4
;;                             equal-of-bvplus-and-bvplus-cancel-arg3-and-arg3)))
;; ;          (if stable-under-simplificationp
;;  ;;             '(:in-theory (enable bvchop-of-sum-cases))
;;    ;         nil)
;;           ))

;gen
(defthm bvplus-of-bvuminus-of-bvmult-of-slice-same
  (implies (unsigned-byte-p 31 x)
           (equal (BVPLUS '32 x (BVUMINUS '32 (BVMULT '31 '4 (SLICE '30 '2 x))))
                  (bvchop 2 x)))
  :hints (("Goal" :in-theory (enable BVMULT-OF-4-GEN))))

;gen
(defthm equal-of-slice-and-slice-of-bvplus-of-1
  (equal (equal (SLICE '5 '2 x) (SLICE '5 '2 (BVPLUS '6 '1 x)))
         (not (equal 3 (bvchop 2 x)))))

(defthm equal-of-bvplus-and-bvplus-hack-sha1
  (equal (EQUAL (BVPLUS '5 '1 (BVCHOP '2 x)) (BVPLUS '2 '1 x))
         (not (equal 3 (bvchop 2 x)))
         ))

(defthm unsigned-byte-p-of-bvplus-of-1-sha1
  (implies (unsigned-byte-p 31 x)
           (equal (unsigned-byte-p '32 (bvplus '64 '1 x))
                  t)))

(defthm bvlt-of-bvif-same-1
  (equal (bvlt size (bvif size test x y) x) ;x appears twice
         (boolif test nil (bvlt size y x)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm unsigned-byte-p-of-+-of-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p (+ -1 size) k)
                (unsigned-byte-p (+ -1 size) x)
                (posp size)
                )
           (equal (unsigned-byte-p size (binary-+ k x))
                  t))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     expt-of-+
                                     ))))

(defthm unsigned-byte-p-of-floor-30-4
  (implies (natp x)
           (equal (unsigned-byte-p '30 (floor x '4))
                  (unsigned-byte-p '32 x)))
  :hints (("Goal"
           :use ((:instance my-floor-upper-bound (i x) (j 4))
                 (:instance my-floor-lower-bound (i x) (j 4)))
           :in-theory (e/d (unsigned-byte-p) (FLOOR-BOUND-LEMMA2 FLOOR-BOUND-LEMMA3 MY-FLOOR-LOWER-BOUND-ALT my-FLOOR-upper-BOUND-ALT)))))

(defthm bvlt-of-bvplus-of-bvcat-of-slice-sha1
  (implies (unsigned-byte-p 32 x) ;gen
           (equal (bvlt 64 (bvplus '64 '4 (bvcat '62 (slice '63 '2 x) '2 '0)) x)
                  nil))
  :hints (("Goal" :use ((:instance my-floor-upper-bound (i x) (j 4))
                        (:instance my-floor-lower-bound (i x) (j 4)))
           :in-theory (e/d (bvlt bvplus bvcat slice logtail
                                 )
                           (FLOOR-BOUND-LEMMA2
                            FLOOR-BOUND-LEMMA3
                            MY-FLOOR-LOWER-BOUND-ALT
                            my-FLOOR-upper-BOUND-ALT

                            anti-slice)))))

(defthm bvlt-of-bvmult-6-5-20
  (implies (and (unsigned-byte-p 6 x)
                (bvlt '6 x '4) ;move to conclusion? ;tighten the 6?
                )
           (equal (bvlt '6 (bvmult '6 '5 x) '20)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult) (bvlt-of-4)))))

(defthm bvlt-of-bvmult-6-5-20-alt
  (implies (and (unsigned-byte-p 3 x)
                (not (bvlt '3 '4 x)) ;move to conclusion? ;tighten the 6?
                )
           (equal (bvlt '6 (bvmult '6 '5 x) '20)
                  (not (equal 4 (bvchop 3 x)))))
  :hints (("Goal" :in-theory (e/d (bvlt bvmult UNSIGNED-BYTE-P) (bvlt-of-4)))))

;gen!
(defthmd equal-of-bvmult-of-expt
  (implies (and (not (equal 0 (mod k (expt 2 n))))
                (natp n))
           (equal (equal k (bvmult size (expt 2 n) x))
                  nil))
  :hints (("Goal" :in-theory (enable bvmult ;bvchop
                                     MOD-OF-EXPT-OF-2
                                     ))))

(defthm <-of-lg
  (implies (natp x)
           (equal (< (LG x) 0)
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable lg))))

(defthmd equal-of-bvmult-of-expt-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (not (equal 0 (mod k k2)))
                (power-of-2p k2)
                (posp k2))
           (equal (equal k (bvmult size k2 x))
                  nil))
  :hints (("Goal" :use (:instance equal-of-bvmult-of-expt (n (lg k2))))))

(defthm bvuminus-of-*
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (bvuminus size (* x y))
                  (bvuminus size (bvmult size x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

;gen! ;gen the bvchop to any bv op
(defthm bvmult-tighten-6-8-2
  (equal (BVMULT '6 '8 (BVCHOP '2 z))
         (BVMULT '5 '8 (BVCHOP '2 z)))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm equal-of-0-and-bvmult-of-expt
  (implies (and (natp n)
                (natp size)
                (integerp x))
           (equal (equal 0 (bvmult size (expt 2 n) x))
                  (equal 0 (bvchop (- size n) x))))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm equal-of-0-and-bvmult-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (posp k)
                (natp size)
                (integerp x))
           (equal (equal 0 (bvmult size k x))
                  (equal 0 (bvchop (- size (lg k)) x))))
  :hints (("Goal" :use (:instance equal-of-0-and-bvmult-of-expt (n (lg k))))))

;; (thm
;;  (equal (BVLT '5 (BVMULT '5 '8 x) '31)
;;         (BVLT '5 (BVMULT '5 '8 x) '31)


;; (<= -32 (LEN BITS))

;; (<= (* 512 x)
;;     (* 32 y))

;;(BVCAT (+ -5 SIZE) 0 5 0)

;gen
(defthm bvmult-32
  (implies (and (natp size)
                (<= 5 size))
           (equal (bvmult size 32 x)
                  (bvcat (- size 5)
                         (slice (+ -1 size -5) 0 x)
                         5
                         0)))
  :hints (("Goal"
           :cases ((equal 5 size)) ;drop
           :in-theory  (set-difference-equal (e/d (bvmult SLICE-WHEN-VAL-IS-NOT-AN-INTEGER)
                                                  ())
                                             (anti-bvmult)))))


;; (UNSIGNED-BYTE-P 22
;;                             (FLOOR (+ 1 (FLOOR (LEN BITS) 32))
;;                                    16))

;newly disabled:
(defthmd floor-of-32-when-usb
  (implies (unsigned-byte-p 31 x)
           (equal (floor x 32)
                  (slice 30 5 x)))
  :hints (("Goal" :in-theory (e/d (slice logtail unsigned-byte-p
                                         floor-bounded-by-/)
                                  (anti-slice)))))

;drop?
(defthm unsigned-byte-p-of-floor-27-16
  (implies (unsigned-byte-p 31 x)
           (unsigned-byte-p 27 (floor x 16)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p floor))))

(defthm floor-of-16-when-usb-31
  (implies (unsigned-byte-p 31 x)
           (equal (floor x 16)
                  (slice 31 4 x)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (anti-slice)))))

;gen
(defthm integerp-of-1-times-1/32
  (implies (integerp x)
           (equal (integerp (* 1/32 x))
                  (equal 0 (bvchop 5 x))))
  :hints (("Goal" :in-theory (e/d (bvchop
                                   MOD-IS-0-WHEN-MULTIPLE)
                                  (MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                   MOD-OF-EXPT-OF-2)))))



;improve?
;freesize isn't free?
(defthm unsigned-byte-p-of-one-more
  (implies (unsigned-byte-p freesize x)
           (unsigned-byte-p (+ 1 freesize)
                            (+ 1 x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm rationalp-of-myif
  (equal (rationalp (myif test x y))
         (myif test (rationalp x)
               (rationalp y)))
  :hints (("Goal" :in-theory (enable myif))))

;(BVLT '10 22 (BVPLUS '6 '32 9))



;commute instead?
(defthm booland-of-not-same2
  (equal (booland (not x) x)
         nil))



(defthm *-of-1/32-and-bvcat-of-0
  (equal (* 1/32 (bvcat size y 5 0))
         (bvchop size y))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced slice logtail bvcat)
                                  ( anti-slice)))))

;; (thm
;;  (equal (REPEAT (+ x (- y))) ,,))

(defthm unary---of-bvif
  (equal (unary-- (bvif size test x y))
         (myif test (unary-- (bvchop size x))
               (unary-- (bvchop size y))))
  :hints (("Goal" :in-theory (enable myif))))

(defthm +-of-myif-arg2
  (equal (+ z (myif test x y))
         (myif test (+ z x)
               (+ z y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm +-of-myif-arg1
  (equal (+ (myif test x y) z)
         (myif test (+ x z)
               (+ y z)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm repeat-of-myif-arg1
  (equal (repeat (myif test x y) z)
         (myif test (repeat x z) (repeat y z)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm integerp-of-ceiling
  (equal (integerp (ceiling x y))
         t))

(defthm rationalp-of-ceiling
  (equal (rationalp (ceiling x y))
         t))

;gen
(defthm bvlt-of-bvuminus-5-4
  (equal (BVLT '5 '0 (BVUMINUS '4 x))
         (not (equal 0 (bvchop 4 x)))))

;gen
(defthm boolor-hack-sha1
  (equal (BOOLOR (EQUAL '0 (BVCHOP '5 (LEN BITS)))
                 (BVLT '5 (LEN BITS) '31))
         (BVLT '5 (LEN BITS) '31)))

(defthm booland-of-not-of-boolor
  (equal (booland (not (boolor x y)) z)
         (booland (not x) (booland (not y) z)))
  :hints (("Goal" :in-theory (enable booland boolor))))

 (defthm booland-of-boolor-and-not-same-5
  (equal (booland (not y) (booland z (boolor x y)))
         (booland x (booland z (not y))))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-of-boolor-and-not-same-5-alt
  (equal (booland (not y) (booland z (boolor y x)))
         (booland x (booland z (not y))))
    :hints (("Goal" :in-theory (enable booland))))

;can we gen the power of 2 to any number?
(defthm equal-of-bvmult-and-expt-of-2
  (implies (and (<= n size)
                (natp n)
                (natp size))
           (equal (equal k (bvmult size (expt 2 n) x))
                  (and (unsigned-byte-p size k)
                       (equal (/ k (expt 2 n)) (bvchop (- size n) x)))))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm equal-of-bvmult-and-expt-of-2-constant-version
  (implies (and (syntaxp (and (quotep j)
                              (quotep k)
                              (quotep size)))
                (power-of-2p j)
                (<= (lg j) size)
                (natp (lg j))
                (natp size))
           (equal (equal k (bvmult size j x))
                  (and (unsigned-byte-p size k)
                       (equal (/ k j) (bvchop (- size (lg j)) x)))))
  :hints (("Goal" :use (:instance equal-of-bvmult-and-expt-of-2 (n (lg j)))
           :in-theory (disable equal-of-bvmult-and-expt-of-2))))

(in-theory (disable BVLT-4-WHEN-UNSIGNED-BYTE-P-BACK))

;can this loop?
;use polarity?
;this seems bad.  (equal nil x) is about the strogest statement you could have over x...
(defthmd equal-of-nil-when-true-listp
  (implies (true-listp x)
           (equal (equal nil x)
                  (equal 0 (len x)))))

(defthmd consp-when-true-listp2
  (implies (true-listp x)
           (equal (consp x)
                  (not (equal 0 (len x))))))

(defthm bvdiv-tighten
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (< (max xsize ysize) size)
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                (natp size)
                (posp xsize))
           (equal (bvdiv size x y)
                  (bvdiv (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced bvdiv)
                                  ()))))



(defthm equal-of-bv-array-write-and-bv-array-write-same
  (implies (and (natp width)
                (natp index)
                (natp index2)
                (< index len)
                (< index2 len)
                (integerp len)
                (true-listp data)
                (all-unsigned-byte-p width data)
                (equal len (len data)))
           (equal (equal (bv-array-write width len index2 val2 data)
                         (bv-array-write width len index val data))
                  (if (equal index index2)
                      (equal (bvchop width val)
                             (bvchop width val2))
                    (and (equal (bvchop width val2)
                                (bv-array-read width len index2 data))
                         (equal (bvchop width val)
                                (bv-array-read width len index data))))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-of-bv-array-write-both) (BV-ARRAY-READ-OF-BV-ARRAY-WRITE)))))

;(in-theory (disable boolif))

(defthm bvlt-of-bvmult-of-expt-arg2
  (implies (and (natp lowsize)
                (<= lowsize size)
                (natp size))
           (equal (bvlt size (bvmult size (expt 2 lowsize) x)
                        k)
                  (or (bvlt (- size lowsize)
                            x (slice (+ -1 size) lowsize k))
                      (and (equal (bvchop (- size lowsize) x)
                                  (slice (+ -1 size) lowsize k))
                           (bvlt lowsize 0 k)))))
  :hints (("Goal" :use (:instance bvlt-of-bvcat-arg2 (y 0) (highsize (- size lowsize)))
           :in-theory (e/d (bvcat bvmult bvlt natp)
                           (bvlt-of-bvcat-arg2
                            )))))

(defthm bvlt-of-bvmult-of-expt-arg2-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (natp (lg k))
                (<= (lg k) size)
                (natp size))
           (equal (bvlt size (bvmult size k x)
                        y)
                  ;can we avoid this case split? (maybe just when y is constant?):
                  (or (bvlt (- size (lg k))
                            x (slice (+ -1 size) (lg k) y))
                      (and (equal (bvchop (- size (lg k)) x)
                                  (slice (+ -1 size) (lg k) y))
                           (bvlt (lg k) 0 y)))))
    :hints (("Goal" :use (:instance bvlt-of-bvmult-of-expt-arg2 (k y) (lowsize (lg k)))
           :in-theory (disable bvlt-of-bvmult-of-expt-arg2))))

;no real case split on this rule (except maybe the bvle?)
(defthm bvlt-of-bvmult-of-expt-arg2-constant-version2
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep size)))
                (power-of-2p k)
                (natp (lg k))
                (<= (lg k) size)
                (natp size))
           (equal (bvlt size (bvmult size k x) k2)
                  ;might be able to use ceiling..
                  (if (bvlt (lg k) 0 k2) ;gets computed
                      ;better phrasing than bvle?
                      (bvle (- size (lg k))
                            x (slice (+ -1 size) (lg k) k2))
                    (bvlt (- size (lg k))
                          x (slice (+ -1 size) (lg k) k2)))))
  :hints (("Goal" :use (:instance bvlt-of-bvmult-of-expt-arg2-constant-version (y k2))
           :in-theory (disable bvlt-of-bvmult-of-expt-arg2-constant-version))))

(defthm bvlt-of-bvmult-of-expt-arg3
  (implies (and (natp size)
                (<= lowsize size)
                (natp lowsize))
           (equal (bvlt size k (bvmult size (expt 2 lowsize) x))
                  (bvlt (- size lowsize) (slice (+ -1 size) lowsize k)
                        x)))
  :hints (("Goal" :use (:instance bvlt-of-bvcat-arg3 (y 0) (highsize (- size lowsize)))
           :in-theory (e/d (bvcat bvmult bvlt)
                           ( bvlt-of-bvcat-arg3
                             )))))

(defthm bvlt-of-bvmult-of-expt-arg3-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= (lg k) size)
                (natp size)
                (natp (lg k)))
           (equal (bvlt size y (bvmult size k x))
                  (bvlt (- size (lg k)) (slice (+ -1 size) (lg k) y)
                        x)))
  :hints (("Goal" :use (:instance bvlt-of-bvmult-of-expt-arg3 (k y) (lowsize (lg k)))
           :in-theory (disable bvlt-of-bvmult-of-expt-arg3))))

(defthm append-of-take-and-subrange-alt
  (implies (and (natp n)
                (< m n) ;gen?
                (natp m))
           (equal (append (take m x) (subrange m n x) y)
                  (append (take (+ 1 n) x) y)))
  :hints (("Goal" :use (:instance append-of-take-and-subrange)
           :in-theory (e/d (;list::car-append list::cdr-append LIST::NTH-APPEND
                            )
                           (append-of-take-and-subrange
                            ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                            )))))

(DEFTHM APPEND-SUBRANGE-SUBRANGE-ADJACENT-alt
  (IMPLIES (AND (< E2 (LEN LST))
                (EQUAL S2 (+ 1 E1))
                (<= S1 E1)
                (<= S2 E2)
                (NATP E1)
                (NATP S1)
                (NATP S2)
                (NATP E2))
           (EQUAL (APPEND (SUBRANGE S1 E1 LST) (SUBRANGE S2 E2 LST) y)
                  (append (SUBRANGE S1 E2 LST) y)))
  :hints (("Goal" :in-theory (enable  ;LIST::EQUAL-APPEND-REDUCTION!-ALT ;why isn't the non-alt one enough?
                              equal-of-append
                                      ))))

(defthm equal-of-+-of-unary-minus
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal '0 (binary-+ x (unary-- y)))
                  (equal y x))))



;see LIST::NTHCDR-WHEN-<=
;seemed quite slow!  do we need it?
(defthmd nthcdr-is-nil
  (implies (and (<= (len x) n)
                (integerp n)
                (true-listp x))
           (equal (NTHCDR n x)
                  nil)))

;gen!
(defthm plus-of-minus-of-slice-and-bvmult-of-slice
  (equal (+ (- (slice 30 2 x)) (bvmult 30 16 (slice 30 6 x)))
         (- (slice 5 2 x))
         )
  :hints (("Goal"
           :use (:instance SPLIT-BV (y (slice 30 2 x)) (n 29) (m 4))
           :in-theory (e/d (bvmult bvcat logapp) (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE
                                                                          )))))

(defthm plus-of-slice-and-minus-of-bvmult-of-slice
  (equal (+ (slice 30 2 x) (- (bvmult 30 16 (slice 30 6 x))))
         (slice 5 2 x)
         )
  :hints (("Goal"
           :use (:instance SPLIT-BV (y (slice 30 2 x)) (n 29) (m 4))
           :in-theory (e/d (bvmult bvcat logapp) (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE
                                                                          )))))


;gen!
(defthm bvmult-of-16-becomes-bvcat
  (equal (BVMULT 29 16 x)
         (bvcat 25 x
                4 0)))

;gen!
(defthm bvlt-of-bvmult-of-slice-and-slice
  (equal (bvlt '30 (bvmult '30 '16 (slice '30 '6 x)) (slice '30 '2 x))
         (not (equal 0 (slice 5 2 x)))))

(defthm slice-of-bvplus-cases-no-split-case-no-carry-constant-version
  (implies (and (syntaxp (and (quotep x)
                              (quotep size)
                              (quotep high)
                              (quotep low)))
                (equal size (+ 1 high))
                (equal 0 (bvchop low x))
                (<= low high)
                (natp low)
                (integerp high))
           (equal (slice high low (bvplus size x y))
                  (bvplus (+ 1 high (- low))
                          (slice high low x)
                          (slice high low y))))
  :hints (("Goal" :use (:instance slice-of-bvplus-cases-no-split-case-no-carry)
           :in-theory (disable slice-of-bvplus-cases-no-split-case-no-carry))))

;kill?
;gen the 1
(defthm <-of-bvplus-same-32-1
  (implies (unsigned-byte-p 32 x)
           (equal (< (bvplus '32 '1 x) x)
                  (equal (+ -1 (expt 2 32))
                         x)))
  :hints (("Goal" :in-theory (enable bvplus))))

;gen!
;also a version for subrange?
(defthm take-of-bv-array-write-irrel
  (implies (and (<= m 80)
                (<= m n)
                (< n 80) ;Mon Jul 19 21:04:50 2010
                (natp m)
                (natp n))
           (equal (take m (bv-array-write '32 '80 n val lst))
                  (bvchop-list 32 (take m lst))))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2)
                                  (update-nth-becomes-update-nth2-extend-gen)))))


(defthm +-of-minus1-and-bvplus-of-1
  (equal (+ -1 (BVPLUS '32 '1 x))
         (if (EQUAL (BVCHOP 32 X) 4294967295)
             -1
           (bvchop 32 x)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(in-theory (disable NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ))

;gen!
(defthm bv-array-read-trim-index
  (equal (BV-ARRAY-READ '32 '80 (BVPLUS '32 x y) lst)
         (BV-ARRAY-READ '32 '80 (BVPLUS '7 x y) lst))
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-READ) (NTH-BECOMES-BV-ARRAY-READ2)))))

;Mon Jul 19 21:06:14 2010
;; (defthm bv-array-write-with-index-and-len-same
;;   (equal (bv-array-write elem-width len len val lst)
;;          (bvchop-list elem-width (take len lst)))
;;   :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))


(defthmd bvchop-tighten
  (implies (and (< YSIZE SIZE)
                (NATP SIZE)
                (<= 0 YSIZE)
                (UNSIGNED-BYTE-P YSIZE (BVCHOP SIZE X)))
           (equal (BVCHOP SIZE X)
                  (BVCHOP ySIZE X))))

(defthm <-of-0-and-integer-length
  (implies (natp x)
           (equal (< 0 (integer-length x))
                  (< 0 x)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm bvmult-of-bvplus-hack-gen
  (implies (and (<= (+ n size2) size)
                (natp size)
                (natp size2)
                (natp n))
           (equal (bvmult size (expt 2 n) (bvplus size2 1 x))
                  (bvplus (+ size2 n) (expt 2 n) (bvmult (+ size2 n) (expt 2 n) x))))
  :hints
  (("Goal"
    :in-theory (e/d (bvmult bvplus bvchop-of-sum-cases) (BVPLUS-OF-PLUS2 BVPLUS-OF-PLUS BVCHOP-OF-* EXPONENTS-ADD
                                                                         MOVE-NEGATIVE-ADDEND-2
                                                                         EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT)))))

(defthm bvmult-of-bvplus-hack-gen-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= (+ (lg k) size2) size)
                (natp size)
                (natp size2)
                (natp (lg k)) ;drop?
                )
           (equal (bvmult size k (bvplus size2 1 x))
                  (bvplus (+ size2 (lg k)) k (bvmult (+ size2 (lg k)) k x))))
  :hints (("Goal" :in-theory (e/d ()
                                  (bvmult-of-bvplus-hack-gen))
           :use (:instance bvmult-of-bvplus-hack-gen (n (lg k))))))

(defthm <-of-len-and-constant
  (implies (and (syntaxp (quotep k))
                (<= k 0))
           (not (< (len x) k))))

(defthm bv-array-write-of-bv-array-write-tighten-len
  (implies (and (< len1 len2)
                (< index1 len1) ;Mon Jul 19 21:07:23 2010
                (< index2 len1) ;Mon Jul 19 21:07:23 2010
                (< index2 len2) ;Mon Jul 19 21:07:23 2010
                (natp index1) ;Mon Jul 19 21:07:23 2010
                (natp index2) ;Mon Jul 19 21:07:23 2010
                (natp len1)
                (natp len2))
           (equal (bv-array-write element-size1 len1 index1 val1 (bv-array-write element-size2 len2 index2 val2 lst))
                  (bv-array-write element-size1 len1 index1 val1 (bv-array-write element-size2 len1 index2 val2 lst))))
  :hints
  (("Goal" :in-theory (e/d (bv-array-write-opener
                            update-nth2 len-update-nth
                            ) (update-nth-becomes-update-nth2-extend-gen)))))

;gen the 4
(defthm floor-becomes-slice-when-unsigned-byte-p
  (implies (and (unsigned-byte-p free x)
                (posp free)
                (integerp x))
           (equal (floor x 4)
                  (slice (+ -1 free) 2 x)))
  :hints (("Goal" :in-theory (e/d (slice logtail UNSIGNED-BYTE-P natp)
                                  (anti-slice)))))



;new:
(in-theory (disable BLAST-BVXOR-32-INTO-8 BLAST-BVAND-32-INTO-8))

;;
;; PICK-A-BIT proofs
;;

;returns a bit where x and y differ (if any)
(defund differing-bit (n x y)
  (declare (xargs :measure (nfix (+ 1 n))))
  (if (not (natp n))
      -1
    (if (not (equal (getbit n x) (getbit n y)))
        n
      (differing-bit (+ -1 n) x y))))

(defthm differing-bit-bad-guy-lemma-helper
  (implies (and (equal (getbit (differing-bit m x y) x)
                       (getbit (differing-bit m x y) y))
                (< m n)
                (natp m)
                (natp n))
           (equal (slice m 0 x)
                  (slice m 0 y)))

  :rule-classes nil
  :hints (("Goal" :in-theory (enable differing-bit))))

;; (defthm natp-of-differing-bit
;;   (natp (differing-bit n x y)))

(defthm <-of-differing-bit
  (implies (natp n)
           (not (< n (differing-bit n x y))))
  :hints (("Goal" :expand ((DIFFERING-BIT 0 X Y))
           :in-theory (enable differing-bit))))

(defthm <-of-differing-bit2
  (implies (and (natp n)
                (integerp k)
                (<= (+ 1 n) k))
           (< (differing-bit n x y) k))
  :hints (("Goal" :expand ((DIFFERING-BIT 0 X Y))
           :in-theory (enable differing-bit))))

(defthm differing-bit-bad-guy-lemma
  (implies (and (equal (getbit (differing-bit (+ -1 n) x y) x)
                       (getbit (differing-bit (+ -1 n) x y) y))
                (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (natp n))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use (:instance differing-bit-bad-guy-lemma-helper (m (+ -1 n)))))
  )

(defthm <-of-differing-bit-and-0
  (implies (natp n)
           (equal (< (differing-bit n x y) 0)
                  (equal (bvchop (+ 1 n) x)
                         (bvchop (+ 1 n) y))))
  :hints (("Goal" :in-theory (enable differing-bit))))

;;(local (in-theory (enable BVOR-1-BECOMES-BITOR)))         ;Thu Mar 31 16:45:29 2011

;; (thm
;;  (implies (and (equal m (differing-bit n x y))
;;                (<= m n)
;;                (natp n)
;;                (natp m))
;;           (not (equal (getbit n x) (getbit n y))))
;;  :hints (("Goal" :in-theory (enable differing-bit))))

(defthm not-0-when-bit-not-0
  (implies (and (not (equal 0 (getbit free x)))
                (natp free)
                )
           (not (equal 0 x))))

(defthmd getbit-of-bvand-core
  (implies (and (< n size) (posp size))
           (equal (getbit n (bvand size x y))
                  (bvand 1 (getbit n x) (getbit n y))))
  :hints
  (("Goal"
    :in-theory
    (e/d
     (getbit bvand bvchop-of-logtail slice)
     (slice-becomes-getbit bvchop-1-becomes-getbit
                           bvchop-of-logtail-becomes-slice
                           LOGTAIL-OF-BVCHOP-BECOMES-SLICE)))))

(local (in-theory (enable bvand-1-becomes-bitand
                           getbit-of-bvand-core)))

(defthm not-equal-of-0-and-bvand
  (implies (and (not (equal 0 (bitand (getbit n x) (getbit n y))))
                (natp n)
                (< n size)
                (natp size))
           (not (equal 0 (bvand size x y))))
  :hints (("Goal" :use (:instance getbit-of-bvand-core (size size))
           :in-theory (disable not-0-when-bit-not-0))))

(defthmd not-equal-bvxor-and-bvor
  (implies (and (equal 1 (getbit n y))
                (equal 1 (getbit n x))
                (< n size)
                (natp n)
                (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (equal (equal (bvxor size x y) (bvor size x y))
                  nil))
  :hints (("Goal" ;:cases ((equal 0 (getbit n (bvxor 32 x y))))
           :use (:instance getbit-of-bvxor-core (size size))
           )))

(defthm equal-of-bvxor-and-bvor-helper
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                (posp size))
           (equal (equal (bvxor size x y) (bvor size x y))
                  (equal 0 (bvand size x y))))
  :hints (("Goal" :cases
           ((and (equal 0 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) y))
                 (equal 0 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) X))
                 )
            (and (equal 0 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) y))
                 (equal 1 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) X))
                 )
            (and (equal 0 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) y))
                 (equal 0 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) X))
                 )
            (and (equal 0 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) y))
                 (equal 1 (GETBIT (DIFFERING-BIT (+ -1 size) 0 (BVAND size X Y)) X))
                 ))
           :in-theory (e/d (BVOR-1-BECOMES-BITOR GETBIT-OF-BVXOR-CORE not-equal-bvxor-and-bvor) ( GETBIT-OF-BVXOR))
           :use ((:instance differing-bit-bad-guy-lemma (x (bvxor size x y)) (y (bvor size x y)) (n size))
                 (:instance differing-bit-bad-guy-lemma (x 0) (y (bvand size x y)) (n size))
                 ))))

(defthm equal-of-bvxor-and-bvor
  (equal (equal (bvxor size x y) (bvor size x y))
         (equal 0 (bvand size x y)))
  :hints (("Goal"
           :cases ((not (integerp size))
                   (natp size))
           :use (:instance equal-of-bvxor-and-bvor-helper (x (bvchop size x)) (y (bvchop size y))))))

;maybe don't need this if bvxor and bvor commute their args the same way?
(defthm equal-of-bvxor-and-bvor-alt
  (equal (equal (bvxor size y x) (bvor size x y))
         (equal 0 (bvand size x y)))
  :hints (("Goal" :use (:instance equal-of-bvxor-and-bvor)
           :in-theory (disable equal-of-bvxor-and-bvor))))

(defthm equal-of-bvor-and-bvxor
  (equal (equal (bvor size x y) (bvxor size x y))
         (equal 0 (bvand size x y)))
  :hints (("Goal" :use (:instance equal-of-bvxor-and-bvor)
           :in-theory (disable equal-of-bvxor-and-bvor))))

;maybe don't need this if bvxor and bvor commute their args the same way?
(defthm equal-of-bvor-and-bvxor-alt
  (equal (equal (bvor size x y) (bvxor size y x))
         (equal 0 (bvand size x y)))
  :hints (("Goal" :use (:instance equal-of-bvxor-and-bvor)
           :in-theory (disable equal-of-bvxor-and-bvor))))

;move this stuff?

;sort of a trim rule?
;disabled Thu Mar 31 17:49:35 2011
(defthmd bitxor-of-bvand
  (implies (posp size)
           (equal (bitxor (bvand size x y) z)
                  (bitxor (bitand x y) z)))
  :hints (("Goal" :in-theory (e/d (bitand bitxor) (bvxor-1-becomes-bitxor BVAND-1-BECOMES-BITAND)))))

;different idioms for majority:
;i think stp would be faster on this if we were cutting the proofs (implement clause mitering?)
;which way should this go?
;ffixme several more possibilites for this..
(defthm majority-idiom1
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size x z) (bvand size y z)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d (BVAND-1-BECOMES-BITAND BVOR-1-BECOMES-BITOR bitxor-of-bvand)
                           (;GETBIT-OF-BVOR-ERIC
                            GETBIT-OF-BVand-ERIC))
           :cases ((and (equal 0 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) x)) (equal 0 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) y)))
                   (and (equal 0 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) x)) (equal 1 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) y)))
                   (and (equal 1 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) x)) (equal 0 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) y)))
                   (and (equal 1 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) x)) (equal 1 (getbit (DIFFERING-BIT (+ -1 size)
                                                        (BVXOR size (BVAND size X Y)
                                                               (BVXOR size (BVAND size X Z)
                                                                      (BVAND size Y Z)))
                                                        (BVOR size (BVAND size X Y)
                                                              (BVOR size (BVAND size X Z)
                                                                    (BVAND size Y Z)))) y)))
                   )
           :use (:instance differing-bit-bad-guy-lemma (n size)
                           (x (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z))))
                           (y (bvor size (bvand size x y) (bvor size (bvand size x z) (bvand size y z))))))))

(defthmd majority-idiom2
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size z x) (bvand size y z)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthmd majority-idiom3
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size x z) (bvand size z y)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthmd majority-idiom4
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size z x) (bvand size z y))) ;swapped y and z Wed Jun 30 13:08:48 2010
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthmd majority-idiom5
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size y z) (bvand size x z)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthmd majority-idiom6
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size y z) (bvand size z x)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthmd majority-idiom7
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size z y) (bvand size x z)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthmd majority-idiom8
  (implies (posp size)
           (equal (bvor size (bvand size x y) (bvor size (bvand size z y) ;swapped y and z Wed Jun 30 13:06:06 2010
                                                    (bvand size z x)))
                  (bvxor size (bvand size x y) (bvxor size (bvand size x z) (bvand size y z)))))
  :hints (("Goal" :use (:instance majority-idiom1) :in-theory (disable majority-idiom1))))

(defthm take-of-bytes-to-bits
  (implies (and (natp m)
                (<= (floor m 8) (len lst))
                (equal 0 (mod m 8))
;                (consp lst)
                )
           (equal (take m (bytes-to-bits lst))
                  (bytes-to-bits (take (floor m 8) lst))))
  :hints (("Goal" :use (:instance take-of-times-8-and-bytes-to-bits (n (floor m 8)))
           :in-theory (e/d (natp bytes-to-bits)
                           (take-of-times-8-and-bytes-to-bits
                            mod-of-expt-of-2-constant-version)))))

;gen the 0!
(defthmd bound-when-low-bits-0-helper
  (implies (and (syntaxp (quotep size))
                (equal 0 (bvchop free x))
                (syntaxp (quotep free))
                (natp size)
                (natp free)
                (unsigned-byte-p size x))
           (bvle size x (+ (expt 2 size) (- (expt 2 free)))))
  :hints (("Goal"
           :use ((:instance split-bv (y x) (n size) (m free))
                 (:instance slice-upper-bound-linear (high (+ -1 size)) (low free)))
           :in-theory (e/d ( bvmult bvcat logapp bvlt slice-of-sum-cases bvchop-of-sum-cases)
                           (bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite

                            bvminus-becomes-bvplus-of-bvuminus)))))

(defthm bound-when-low-bits-0
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal 0 (bvchop free x))
                (syntaxp (quotep free))
                (bvle size (+ (expt 2 size) (- (expt 2 free))) k)
                (natp size)
                (natp free))
           (equal (bvlt size k x)
                  nil))
  :hints (("Goal" :use (:instance bound-when-low-bits-0-helper (x (bvchop size x)))
           :in-theory (disable bound-when-low-bits-0-helper))))

(defthm bound-when-low-bits-0-alt
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal 0 (bvchop free x))
                (syntaxp (quotep free))
                (bvle size (+ 1 (expt 2 size) (- (expt 2 free))) k)
                (natp size)
                (<= free size)
                (posp free))
           (equal (bvlt size x k)
                  t))
  :hints (("Goal" :use (:instance bound-when-low-bits-0-helper (x (bvchop size x)))
           :in-theory (e/d (bvlt bvchop-of-sum-cases) (bound-when-low-bits-0-helper)))))


(defthm bvmult-becomes-bvcat-31-64
  (equal (bvmult '31 '64 x)
         (bvcat 25 x 6 0)))

;gen!
(defthm <-of-*-of-constant-and-*-of-constant
  (implies (and (syntaxp (quotep k))
                (equal k 8) ;gen!!
;                (< k 32)
 ;               (rationalp k)
                (< 0 k))
           (equal (< (* k x) (* 32 y))
                  (< x (* (/ 32 k) y)))))

;gen
(defthm *-becomes-bvmult-8
  (implies (unsigned-byte-p free x)
           (equal (* 8 x)
                  (bvmult (+ 3 free) 8 x)))
  :hints (("Goal" :in-theory (enable bvmult natp))))

;introduces!
(defthm ceiling-in-terms-of-floor2
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)) ;fixme
                )
           (equal (ceiling i j)
                  (if (equal 0 (mod i j))
                      (/ i j)
                      (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor))))



;gen
(defthm integerp-of-/-of-64
  (implies (integerp x)
           (equal (integerp (/ x 64))
                  (equal 0 (slice 5 0 x))))
  :hints (("Goal" :in-theory (e/d (bvchop mod-is-0-when-multiple)
                                  (mod-of-expt-of-2
                                   mod-of-expt-of-2-constant-version)))))

(defthmd floor-of-64-when-usb-64
  (implies (unsigned-byte-p 64 x)
           (equal (floor x 64)
                  (slice 63 6 x)))
  :hints (("Goal" :in-theory (e/d (slice logtail unsigned-byte-p floor-bounded-by-/)
                                  (anti-slice)))))

;gen!  we also have a version for 32
(defthmd floor-of-64-when-usb-31
  (implies (unsigned-byte-p 31 x)
           (equal (floor x 64)
                  (slice 30 6 x)))
  :hints
  (("Goal" :expand (slice 30 6 x)
    :in-theory (e/d (slice logtail unsigned-byte-p floor-bounded-by-/)
                    (anti-slice bvchop-of-slice bvchop-of-slice-both
                                FLOOR-BECOMES-SLICE-WHEN-UNSIGNED-BYTE-P ;looped
                                )))))

;gen to any bv op
;use a natp-forced?
(defthm <-OF-SLICE-AND-constant-when-not-positive
  (implies (and (syntaxp (quotep k))
                (<= k 0))
           (not (< (slice high low x) k))))


(in-theory (disable FLOOR-BECOMES-SLICE-WHEN-UNSIGNED-BYTE-P)) ;looped

(defthm integerp-of-*-of-1/64
  (implies (integerp x)
           (equal (integerp (* 1/64 x))
                  (equal 0 (slice 5 0 x))))
  :hints
  (("Goal"
    :in-theory (e/d (bvchop mod-is-0-when-multiple)
                    (mod-of-expt-of-2 mod-of-expt-of-2-constant-version)))))

(defthmd *-of-1/64-when-multiple
  (implies (and (equal 0 (bvchop 6 x))
                (unsigned-byte-p 64 x))
           (equal (BINARY-* '1/64 x)
                  (slice 63 6 x)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (FLOOR-OF-64-WHEN-USB-64
                                                   anti-slice)))))

;compare to natp-*
(defthmd natp-of-*
  (implies (and (natp a) (natp b))
           (equal (natp (* a b))
                  t)))

(defthm bvmult-of-bvmult-hack
  (implies (and (natp highsize)
                (natp lowsize))
           (equal (bvmult highsize '4 (bvmult lowsize '16 x))
                  (bvmult highsize '64 (bvchop (- lowsize 4) x))))
  :hints (("Goal" :in-theory (enable bvmult))))

;tighten first?!
(defthm bvmult-of-bvplus-hack
;;   (implies (and ;(Natp highsize)
;;                 ;(<= 64 highsize)
;;                 )
           (equal (bvmult 66 64 (bvplus 58 1 x))
                  (bvplus 64 64 (bvmult 64 64 x)))
;           )
  :hints (("Goal" :in-theory (enable bvmult bvplus bvchop-of-sum-cases))))

;tighten first?!
(defthm bvmult-of-bvplus-hack2
;;   (implies (and ;(Natp highsize)
;;                 ;(<= 64 highsize)
;;                 )
           (equal (bvmult 67 64 (bvplus 59 1 x))
                  (bvplus 65 64 (bvmult 65 64 x)))
           ;)
  :hints (("Goal" :in-theory (enable bvmult bvplus bvchop-of-sum-cases))))

;just tightens
;gen!
(defthm bvmult-of-bvplus-hack3
;;   (implies (and ;(natp highsize)
;;                 ;(<= 64 highsize)
;;                 )
           (equal (bvmult '34 '4 (bvplus '31 '16 x))
                  (bvmult '33 '4 (bvplus '31 '16 x)))
           ;)
  :hints (("Goal" :in-theory (enable bvmult bvplus bvchop-of-sum-cases))))

(defthm bvmult-of-bvplus-hack4
;  (implies (and ;(natp highsize)
            ;;(<= 64 highsize)
;            )
           (equal (bvmult 33 4 (bvplus 31 16 x))
                  (bvplus 33 64 (bvmult 33 4 x)))
;)
  :hints (("Goal" :in-theory (enable bvmult bvplus bvchop-of-sum-cases))))

;gen
(defthm bvmult-of-slice-tighten
  (implies (and (natp highsize)
                (< 64 highsize)
                )
           (equal (BVMULT highsize '64 (SLICE '63 '6 x))
                  (BVMULT '64 '64 (SLICE '63 '6 x))))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvmult-tighten-hack
  (implies (and (natp highsize)
                (< 31 highsize)
                )
           (equal (bvmult highsize 64 (slice 30 6 x))
                  (bvmult '31 64 (slice 30 6 x))))
  :hints (("Goal" :in-theory (enable bvmult bvplus bvchop-of-sum-cases))))

;bad?
(defthm bvplus-tighten-hack100
  (implies (and (natp highsize)
                (< 32 highsize)
                )
           (equal (bvplus highsize 64 (bvmult 31 x y))
                  (bvplus 32 64 (bvmult 31 x y))))
  :hints (("Goal" :in-theory (enable bvmult bvplus bvchop-of-sum-cases))))

(defthm bvlt-of-bvmult-hack200
  (equal (BVLT '31 '0 (BVMULT '31 '64 x))
         (BVLT '31 '0 (bvchop 25 x))))

;gen!
(defthm equal-of-bvmult-of-slice
  (equal (equal x (bvmult '31 '64 (slice '30 '6 x)))
         (and (unsigned-byte-p 31 x)
              (equal 0 (bvchop 6 x))))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y (bvchop 31 x)) (n 31) (m 6))
           :in-theory (e/d (bvmult bvcat logapp) (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE
                                                                          )))))

;gen!
(defthm bvmult-of-bvcat
  (equal (bvmult '31 '4 (bvcat '25 x '4 '0))
         (bvmult '31 '64 x)))

;gen!
;can be expensive
(defthm bvlt-of-slice-and-slice2
  (implies (and (not (bvlt 31 x y))
                (<= 6 n)
                (<= n 30)
                (natp n))
           (equal (bvlt 25 (slice 30 n x) (slice 30 n y))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt slice BVCHOP-OF-LOGTAIL
                                        ) (LOGTAIL-LESSP anti-slice)))))

(defthm bvmult-of-slice-when-bvchop-0
  (implies (and (equal free (bvchop 6 x))
                (syntaxp (quotep free))
                (equal 0 free))
           (equal (bvmult '31 '64 (slice '30 '6 x))
                  (bvchop 31 x)))
  :hints (("Goal"
           :in-theory (e/d (bvcat logapp) (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE ))
           :use (:instance split-bv (y (bvchop 31 x))
                           (n 31)
                           (m 6)))))


;do we already have something like this?
;rename?
(defthm bvplus-of-bvuminus-trim
  (implies (and (not (bvlt '31 x y))
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvplus '32 x (bvuminus '32 y))
                  (bvplus '31 x (bvuminus '31 y))))
  :hints (("Goal" :in-theory (disable BVLT-OF-BVPLUS-CONSTANT-AND-CONSTANT-OTHER ;looped..
                                      ))))

;use this?
(defthm bvlt-hack-for-sha1-two
  (implies (and (not (bvlt '31 (bvplus '31 x3 (bvuminus '31 x29)) '64)) ;not really simplified?
                (not (bvlt 31 x3 x29))
                (unsigned-byte-p 31 x3)
                (unsigned-byte-p 31 x29))
           (equal (bvlt '32 x3 (bvplus '32 '4 x29))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvminus bvlt BVLT-OF-BVPLUS-OF-BVUMINUS-OTHER-ALT bvplus bvchop-of-sum-cases bvuminus)
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm equal-of-0-when-bvlt-of-slice
  (implies (bvlt size y (slice high low x)) ;lots of free vars
           (equal (equal 0 x)
                  nil)))

(defthm bvlt-of-bvplus-constant-when-not-bvlt-of-bvplus-constant
  (implies (and (syntaxp (quotep k2))
                (natp size)
                (equal size 31) ;gen!
                (not (bvlt size x (bvplus size free y)))
                (syntaxp (quotep free))
                (<= k2 free)
                (bvlt size y (- (expt 2 size) free))
                (unsigned-byte-p size free)
                (unsigned-byte-p size k2))
           (equal (bvlt size x (bvplus 31 k2 y))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvminus bvlt BVLT-OF-BVPLUS-OF-BVUMINUS-OTHER-ALT bvplus bvchop-of-sum-cases bvuminus)
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;gen
;newly disabled
(defthmd bvlt-of-slice-and-slice2-back
  (implies (and (bvlt 25 (slice 30 n x) (slice 30 n y))
                (<= 6 n)
                (<= n 30)
                (natp n))
           (equal (bvlt 31 x y)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt slice bvchop-of-logtail)
                                  (logtail-lessp anti-slice)))))

(in-theory (disable LOGTAIL-OF-ONE-MORE)) ;add syntaxp hyp

;gen
(defthm bound-gap-theorem
  (implies (and (syntaxp (want-to-strengthen (< x (* 64 y))))
                (equal 0 (bvchop 6 x))
                (integerp y)
                (integerp x))
           (equal (< x (* 64 y))
                  (<= x (+ -64 (* 64 y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil nil)))
  :hints (("Goal" :in-theory (enable bvchop mod))))


;gen
(defthm bvlt-of-bvplus-when-bvlt-of-slices
  (implies (and (syntaxp (quotep k))
                (bvlt 31 k 64)
                (unsigned-byte-p 31 k)
                (bvlt 25 (slice 30 6 x) (slice 30 6 y))
                (equal 0 (bvchop 6 x))
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 32 (bvplus 32 k x) y)
                  t))
  :hints (("Goal"
           :use ((:instance split-bv (y (bvchop 31 x))
                            (n 31)
                            (m 6))
                 (:instance split-bv (y (bvchop 31 y))
                            (n 31)
                            (m 6)))
           :in-theory (e/d (bvlt slice bvchop-of-logtail bvplus bvcat logapp logtail FLOOR-OF-SUM bvchop-of-sum-cases
                                 )
                           (logtail-lessp anti-slice )))))

(defthm bvplus-tighten-free-1
  (implies (and (unsigned-byte-p free y)
                (unsigned-byte-p free x)
                (< (+ 1 free) size)
                (natp free)
                (natp size))
           (equal (bvplus size y x)
                  (bvplus (+ 1 free) y x)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthm bvplus-tighten-free-2
  (implies (and (unsigned-byte-p free x)
                (unsigned-byte-p free y)
                (< (+ 1 free) size)
                (natp free)
                (natp size))
           (equal (bvplus size y x)
                  (bvplus (+ 1 free) y x)))
  :hints (("Goal" :use (:instance bvplus-tighten-free-1)
           :in-theory (disable bvplus-tighten-free-1))))

(defthm bvplus-of-slice-and-bvuminus-of-bvmult
  (equal (BVPLUS '30 (SLICE '34 '5 x) (BVUMINUS '30 (BVMULT '30 '16 (SLICE '34 '9 x))))
         (slice 8 5 x))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y (slice 34 5 x)) (n 30) (m 4))
           :in-theory (e/d (bvplus bvuminus bvminus bvmult bvcat logapp)
                           (BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE

                            BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;gen!
(defthm bvmult-of-bvcat-hack
  (equal (bvmult '34 '32 (bvcat '25 x '4 0))
         (bvcat '25 x 9 0)))

(defthm bvmult-of-bvcat-hack2
  (equal (bvmult 5 8 (bvcat 3 x 2 0))
         0))

(defthm bvmult-of-bvcat-hack3
  (equal (bvmult '34 '8 (bvcat '29 x '2 0))
         (bvcat '29 x 5 0)))


(defthm bvmult-of-bvcat-hack4
  (equal (bvmult 9 '8 (bvcat 3 x 6 0))
         0))

(defthm ceiling-of-bvcat-hack
  (equal (ceiling (bvcat '29 x '5 '0) '32)
         (bvchop 29 x))
  :hints (("Goal" :in-theory (enable bvcat))))

(defthm equal-of-bvnot-and-bvnot
  (implies (and ;(unsigned-byte-p size x)
                ;(unsigned-byte-p size y)
                (natp size))
           (equal (equal (bvnot size x) (bvnot size y))
                  (equal (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable bvnot lognot
                                     bvchop-of-sum-cases))))

;; (defthm equal-of-bvnot-and-bvnot
;;   (implies (and (unsigned-byte-p size x)
;;                 (unsigned-byte-p size y)
;;                 (natp size))
;;            (equal (equal (bvnot size x) (bvnot size y))
;;                   (equal (bvchop size x) (bvchop size y))))
;;   :hints (("Goal" :in-theory (enable bvnot lognot
;;                                      bvchop-of-sum-cases))))

(in-theory (disable PLUS-OF-4-AND-BV-BECOMES-BVPLUS))

(defthm <-of-bvchop-and-bvchop-when-<-of-slice-and-slice
  (implies (and (< (slice kminus1 n y) (slice kminus1 n x))
                (equal kminus1 (+ -1 k))
                (natp n)
                (natp k)
                (<= n k))
           (not (< (bvchop k x) (bvchop k y))))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail) (anti-slice)))))

(in-theory (disable FLOOR-OF-64-WHEN-USB-31 FLOOR-OF-64-WHEN-USB-64))

;gen!
(defthm equal-of-floor-and-floor-when-<-of-floor-and-floor
  (implies (and (rationalp x)
                (rationalp y)
                (< (floor x 64)
                   (floor y 64)))
           (not (equal (floor x 4)
                       (floor y 4))))
  :hints (("Goal" :use ((:instance FLOOR-FLOOR-INTEGER (x x) (i 4) (j 16))
                        (:instance FLOOR-FLOOR-INTEGER (x y) (i 4) (j 16)))
           :in-theory (disable FLOOR-FLOOR-INTEGER FLOOR-BOUNDED-BY-/))))

;gen!
(defthm <-of-floor-and-floor-when-<-of-floor-and-floor
  (implies (and (rationalp x)
                (rationalp y)
                (< (floor x 64)
                   (floor y 64)))
           (< (floor x 4)
              (floor y 4)))
  :hints (("Goal" :use ((:instance FLOOR-FLOOR-INTEGER (x x) (i 4) (j 16))
                        (:instance FLOOR-FLOOR-INTEGER (x y) (i 4) (j 16))
                        (:instance floor-weak-monotone (i1 (FLOOR Y 4)) (i2 (FLOOR x 4)) (j 16))
                        )
           :in-theory (disable FLOOR-FLOOR-INTEGER floor-weak-monotone floor-bounded-by-/))))

(defthm equal-of-logtail-and-logtail-when-<-of-logtail-and-logtail
  (IMPLIES (AND (rationalp x)
                (rationalp y)
                (< (LOGTAIL 6 y)
                   (LOGTAIL 6 x)))
           (NOT (EQUAL (LOGTAIL 2 y)
                       (LOGTAIL 2 x))))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm <-of-logtail-and-logtail-when-<-of-logtail-and-logtail
  (IMPLIES (AND (rationalp x)
                (rationalp y)
                (< (LOGTAIL 6 y)
                   (LOGTAIL 6 x)))
           (< (LOGTAIL 2 y)
              (LOGTAIL 2 x)))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm equal-of-slice-and-slice-when-<-of-slice-and-slice
  (implies (and (INTEGERP X)
                (INTEGERP Y)
                (< (SLICE 30 6 Y) (SLICE 30 6 X)))
           (equal (EQUAL (SLICE 30 2 Y) (SLICE 30 2 X))
                  nil))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail) (anti-slice LOGTAIL-LESSP)))))

(defthm <-of-slice-and-slice-when-<-of-slice-and-slice
  (implies (and (INTEGERP X)
                (INTEGERP Y)
                (< (SLICE 30 6 Y) (SLICE 30 6 X)))
           (< (SLICE 30 2 Y) (SLICE 30 2 X)))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail) (anti-slice LOGTAIL-LESSP)))))

(defthmd split-hack-lemma
  (equal (SLICE 30 2 X)
         (+ (SLICE 5 2 X) (* 16 (SLICE 30 6 X))))
  :hints (("Goal" :use ((:instance SPLIT-BV (y (slice 30 2 x)) (n 29) (m 4)))
          :in-theory (e/d (bvplus bvuminus bvminus bvmult bvcat logapp bvlt SLICE-OF-SUM-CASES bvchop-of-sum-cases)
                          (BVCAT-EQUAL-REWRITE-ALT
                           BVCAT-EQUAL-REWRITE

                           BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))


(defthm bvcat-of-bvmult-hack-another
  (equal (BVCAT 30 (BVMULT 30 16 x) 5 0)
         (BVCAT 26 x 9 0)))

(defthm sha1-hack-123434
  (implies (and (bvlt 25 (slice 30 6 y) (slice 30 6 x))
                (equal 0 (bvchop 6 y))
                (integerp x) ;(unsigned-byte-p 31 x)
                (integerp y) ;(unsigned-byte-p 31 y)
                )
           (equal (equal 0 (slice 30 2 (bvplus 31 x (bvuminus 31 y))))
                  nil))
  :hints (("Goal"
           :use ((:instance SPLIT-BV (y (slice 30 2 x)) (n 29) (m 4))
                 (:instance SPLIT-BV (y (slice 30 2 y)) (n 29) (m 4))
    ;(:instance <-of-slice-and-slice-when-<-of-slice-and-slice)
                 )

           :in-theory (e/d ( ;split-hack-lemma
                            bvplus bvuminus bvminus bvmult bvcat logapp bvlt SLICE-OF-SUM-CASES)
                           (BVCAT-EQUAL-REWRITE-ALT
    ;<-of-slice-and-slice-when-<-of-slice-and-slice
                            BVCAT-EQUAL-REWRITE

                            BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))


;gen!
(defthm unsigned-byte-p-of-bvmult-29-30-16
  (equal (unsigned-byte-p '29 (bvmult '30 '16 x))
         (equal 0 (getbit 25 x)))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 26 x)) (n 26) (m 25))
           :in-theory (e/d (getbit-when-val-is-not-an-integer
                            bvmult)
                           (bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite

                            bvminus-becomes-bvplus-of-bvuminus
                            bvcat-of-getbit-and-x-adjacent)))))

;gen!!!!
(defthm bvlt-of-bvmult-9-8-400
  (equal (BVLT 9 (BVMULT 9 8 x) 400)
         (bvlt 6 x 50))
  :hints (("Goal" :in-theory (enable bvlt bvmult))))


;gen the 64
(defthm bvdiv-of-64
  (implies (natp n)
           (equal (bvdiv n x 64)
                  (slice (+ -1 n) 6 x)))
  :hints (("Goal"
           :use (:instance FLOOR-WHEN-USB-BIND-FREE (x (bvchop n x)) (xsize n) (n 6))
           :in-theory (e/d (bvdiv ;slice logtail bvchop
                            UNSIGNED-BYTE-P-FORCED
                            )
                           (FLOOR-WHEN-USB-BIND-FREE
                            ;CANCEL-MOD-+
                            anti-slice MOD-OF-EXPT-OF-2-CONSTANT-VERSION MOD-OF-EXPT-OF-2)))))

(defthm bvplus-of-bvuminus-of-bvcat-same-helper
  (implies (and (<= m low)
                (< low size)
                (natp size)
                (natp m)
                (natp low)
                (equal bigsize (+ 2 size (- m))))
           (equal (bvplus bigsize
                          (slice (+ 1 size) m x)
                          (bvuminus bigsize
                                    (bvcat (+ 2 (- low) size)
                                           (slice (+ 1 size) low x)
                                           (- low m)
                                           0)))
                  (slice (+ -1 low) m x)))
  :hints (("Goal" :cases ((equal m low)))))

;clean this up!
(defthm bvplus-of-bvuminus-of-bvcat-same
  (implies (and (<= m low)
                (< low (+ bigsize m -2))
                (natp (+ bigsize m -2))
                (equal k (+ -1 bigsize m))
                (equal j (+ (- low) bigsize m))
                (equal l (- low m))
                (natp m)
                (natp low))
           (equal (bvplus bigsize
                          (slice k m x)
                          (bvuminus bigsize
                                    (bvcat j
                                           (slice k low x)
                                           l
                                           0)))
                  (slice (+ -1 low) m x)))
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-of-bvcat-same-helper (size (+ bigsize m -2)))
           :in-theory (disable bvplus-of-bvuminus-of-bvcat-same-helper))))

(defthmd expt-hack-2000
  (implies (and (unsigned-byte-p (- size lowsize) x)
                (<= lowsize size)
                (natp size)
                (natp lowsize)
                )
           (not (< (expt 2 size)
                   (+ (expt 2 lowsize)
                      (* x (expt 2 lowsize))))))
  :hints (("Goal"
           ;; :cases ((< (+ 1 X) (* (/ (EXPT 2 LOWSIZE)) (EXPT 2 SIZE)))
           ;;         (> (+ 1 X) (* (/ (EXPT 2 LOWSIZE)) (EXPT 2 SIZE)))
           ;;         (equal (+ 1 X) (* (/ (EXPT 2 LOWSIZE)) (EXPT 2 SIZE))))
           :use (:instance <-*-LEFT-CANCEL (x (expt 2 (- size lowsize))) (y (+ 1 x)) (z (expt 2 lowsize)))
           :in-theory (e/d (unsigned-byte-p) (EXPT-MINUS <-*-/-RIGHT-COMMUTED
;exponents-add
                                                         <-*-LEFT-CANCEL
                                                         <-*-/-LEFT-COMMUTED
                                                         )))))

;compare to bvplus-of-bvcat-constants
(defthm bvplus-of-bvcat-constants-hack
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep lowsize)))
                (< k (- (expt 2 lowsize) k2)) ;use bvlt? ;(bvlt lowsize k k2)
                (unsigned-byte-p lowsize k) ;drop?
                (unsigned-byte-p lowsize k2) ;drop!?
                (unsigned-byte-p highsize x) ;drop
                (posp lowsize)
                (posp highsize)
                (<= (+ highsize lowsize) size)
                (natp size))
           (equal (bvplus size k2 (bvcat highsize x lowsize k))
                  (bvcat highsize x lowsize (+ k2 k))))
  :hints (("Goal" :cases ((<= (* X (EXPT 2 LOWSIZE)) (- (EXPT 2 size) (expt 2 lowsize))))
           :use (expt-hack-2000
                 (:instance EXPT-BOUND-LINEAR-WEAK (size (+ highsize LOWSIZE)) (free size)))
           :in-theory (e/d (;expt-hack-2000
                            bvlt
                            bvchop-of-sum-cases bvcat bvplus logapp)
                           (bvplus-of-bvcat-hack6-gen-low-open ;looped
;NATP-MEANS-NON-NEG

;UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP
                            ;;                                    EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                            ;;                                    <-OF-EXPT-AND-EXPT
                            ;;                                    <-OF-EXPT-WHEN-FREE
                            ;;                                    PLUS-OF-TIMES-EXPT-BOUND2
                            )))))

;just use BVMULT-OF-4-GEN ?
(defthm bvmult-of-bvcat-hack100
  (implies (and (natp k)
                (equal size 4) ;gen
                (Natp size))
           (equal (bvmult (+ 25 size 2) 4 (bvcat 25 x size k))
                  (bvcat 25 x (+ 2 size) (* k 4)))))

;move
(defthm all-true-listp-of-nthcdr
  (implies (all-true-listp x)
           (equal (all-true-listp (nthcdr n x))
                  t))
  :hints (("Goal" :in-theory (e/d (nthcdr) (nthcdr-of-cdr-combine nthcdr-of-cdr-combine-strong)))))

;gen
(defthm bvlt-of-one-less-than-max-25
  (equal (bvlt 25 33554430 x)
         (equal (bvchop 25 x)
                33554431))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvplus-and-bvcat-hack
  (implies (and (syntaxp (quotep k))
                (equal 0 (bvchop free x))
                (unsigned-byte-p free k)
                (unsigned-byte-p size x) ;drop
                (natp free)
                (< free size)
                (natp size))
           (equal (bvplus size k x)
                  (bvcat (- size free) (slice (+ -1 size) free x) free k)))
  :hints (("Goal" ;:expand ((:with (:definition unsigned-byte-p) (unsigned-byte-p free2 (+ k x))))
           :use (:instance split-bv (y (bvchop size x)) (n size) (m free))
           :in-theory (e/d (;bvplus bvcat logapp
                            )
                           (bvcat-equal-rewrite-alt
                            bvcat-equal-rewrite

                            bvminus-becomes-bvplus-of-bvuminus
                            bvcat-of-getbit-and-x-adjacent)))))

;; (defthm bvplus-and-bvcat-hack
;;   (implies (and (syntaxp (quotep k))
;;                 (equal 0 (bvchop free x))
;;                 (unsigned-byte-p free k)
;;                 (unsigned-byte-p free2 x) ;get rid of free?
;;                 (natp free)
;;                 (< free free2)
;;                 (natp size)
;;                 (<= free2 size))
;;            (equal (bvplus size k x)
;;                   (bvcat (- free2 free) (slice (+ -1 free2) free x) free k)))
;;   :hints (("Goal" ;:expand ((:with (:definition unsigned-byte-p) (unsigned-byte-p free2 (+ k x))))
;;            :use (:instance split-bv (y x) (n free2) (m free))
;;            :in-theory (e/d ()
;;                            (bvcat-equal-rewrite-alt
;;                             bvcat-equal-rewrite
;;
;;                             bvminus-becomes-bvplus-of-bvuminus
;;                             bvcat-of-getbit-and-x-adjacent)))))

;lhs out of order
(defthm one-fourth-hack
  (equal (BINARY-* (BVCAT '25 x '6 '0) '1/4)
         (BVCAT '25 x '4 '0))
  :hints (("Goal" :in-theory (e/d (slice bvcat) ( anti-slice)))))

(defthm ceiling-in-terms-of-floor3
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (ceiling i j)
                  (if (equal 0 (mod i j))
                      (floor i j)
                      (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthm getbit-when-not-bvlt-constant
  (implies (and (not (bvlt '32 x k))
                (syntaxp (quotep k))
                (bvle 32 (expt 2 31) k))
           (equal (getbit '31 x)
                  1))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvcat-of-slice-onto-constant
  (implies (and (syntaxp (quotep k))
                (equal free (bvchop 6 x))
                (syntaxp (quotep free))
                (equal free k))
           (equal (bvcat '25 (slice '30 '6 x) '6 k)
                  (bvchop 31 x))))

(in-theory (disable sbvlt-of-+-arg2 sbvlt-of-+-arg1))

(defthm getbit-when-bound
  (implies (and (< x free)
                (syntaxp (quotep free))
                (<= free (expt 2 n))
                (natp n)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  0))
  :hints (("Goal"
           :use (:instance slice-too-high-is-0 (high n) (low n))
           :in-theory (e/d (getbit) (slice-becomes-getbit bvchop-1-becomes-getbit)))))

(defthm getbit-when-bound2
  (implies (and (not (< free x))
                (syntaxp (quotep free))
                (< free (expt 2 n))
                (natp n)
                (natp free)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use (:instance getbit-when-bound (free (+ 1 free)))
           :in-theory (disable getbit-when-bound))))

(defthmd getbit-when-bound3-helper
  (implies (and (<= (expt 2 n) x)
                (unsigned-byte-p (+ 1 n) x)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal"
;           :use (:instance slice-too-high-is-0 (high n) (low n))
           :in-theory (e/d (getbit slice logtail floor-must-be-1)
                           (slice-becomes-getbit bvchop-1-becomes-getbit
                                                 anti-slice)))))

(defthm getbit-when-bound3
  (implies (and (< free x)
                (syntaxp (quotep free))
                (<= (+ -1 (expt 2 n)) free)
                (unsigned-byte-p (+ 1 n) x)
                (natp n)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when-bound3-helper)
           :in-theory (disable getbit-when-bound3-helper))))

(defthm getbit-when-bound4
  (implies (and (not (< x free))
                (syntaxp (quotep free))
                (<= (expt 2 n) free)
                (unsigned-byte-p (+ 1 n) x)
                (natp n)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when-bound3-helper)
           :in-theory (disable getbit-when-bound3-helper))))

(defthm boolor-of-sbvlt-combine-gen
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (natp k)
                (< (+ k2 (expt 2 31)) (bvchop 32 k))
                (unsigned-byte-p 31 k2))
           (equal (boolor (sbvlt 32 (bvplus 32 k x) k2)
                          (sbvlt 32 x k2) ;allow k3 here?
                          )
                  (sbvlt 32 x (+ k2 (- k)))))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 32 k)) (n 32) (m 31))
           :cases ((equal 0 (getbit 31 k)))
           :in-theory (e/d (sbvlt bvlt getbit-of-bvplus-split bvplus bvchop-of-sum-cases boolor
                                  bvcat getbit-of-plus
                                  logapp)
                           (bvcat-of-getbit-and-x-adjacent
                            bvcat-equal-rewrite-alt
                            )))))

(defthm boolor-of-sbvlt-combine-gen-alt
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (natp k)
                (< (+ k2 (expt 2 31)) (bvchop 32 k))
                (unsigned-byte-p 31 k2))
           (equal (boolor (sbvlt 32 x k2)
                          (sbvlt 32 (bvplus 32 k x) k2))
                  (sbvlt 32 x (+ k2 (- k)))))
  :hints (("Goal" :use (:instance boolor-of-sbvlt-combine-gen)
           :in-theory (union-theories (theory 'minimal-theory)
                                      ;;equal-of-bvchop-extend ;looped!
                                      '(boolor)))))

(defthm boolor-of-sbvlt-combine-gen-extra-disjunct
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (natp k)
                (< (+ k2 (expt 2 31)) (bvchop 32 k))
                (unsigned-byte-p 31 k2))
           (equal (boolor (sbvlt 32 (bvplus 32 k x) k2)
                          (boolor (sbvlt 32 x k2) ;allow k3 here?
                                  extra))
                  (boolor (sbvlt 32 x (+ k2 (- k))) extra)))
  :hints (("Goal" :use (:instance boolor-of-sbvlt-combine-gen)
           :in-theory (disable boolor-of-sbvlt-combine-gen))))

(defthm boolor-of-sbvlt-combine-gen-alt-extra-disjunct
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (natp k)
                (< (+ k2 (expt 2 31)) (bvchop 32 k))
                (unsigned-byte-p 31 k2))
           (equal (boolor (sbvlt 32 x k2)
                          (boolor (sbvlt 32 (bvplus 32 k x) k2)
                                  extra))
                  (boolor (sbvlt 32 x (+ k2 (- k)))
                          extra)))
  :hints (("Goal" :use (:instance boolor-of-sbvlt-combine-gen-alt)
           :in-theory (disable boolor-of-sbvlt-combine-gen-alt))))


;kill special cases of this?
(defthm bvplus-of-bvuminus-of-bvcat-of-0
  (implies (and (equal diff (- size2 size))
                (equal size2minus1 (+ -1 size2))
                (< size size2)
                (natp size)
                (natp size2))
           (equal (bvplus size2 x (bvuminus size2 (bvcat diff (slice size2minus1 size x) size 0)))
                  (bvchop size x)))
  :hints (("Goal" :cases ((equal size size2)))))

(defthm nth-when-equal-of-firstn-and-constant
  (implies (and (equal k (firstn m x))
                (syntaxp (and (quotep k)
                              (not (quotep x)))) ;gen to that k is a smaller term?
                (< n m)
                (natp n)
                (natp m))
           (equal (nth n x)
                  (nth n k))))

(defthm nth-when-equal-of-take-and-constant
  (implies (and (equal k (take m x))
                (syntaxp (and (quotep k)
                              (not (quotep x)))) ;gen to that k is a smaller term?
                (< n m)
                (natp n)
                (natp m))
           (equal (nth n x)
                  (nth n k))))

(defthm bv-array-read-when-equal-of-firstn-and-constant
  (implies (and (equal k (firstn m x))
                (syntaxp (and (quotep k)
                              (not (quotep x))))
                (< n m)
                (< n len)
                (natp len)
                (natp n)
                (natp m)
                )
           (equal (bv-array-read size len n x)
                  (bv-array-read size len n k)))
  :hints (("Goal" :in-theory (e/d ( bv-array-read-opener) (NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bv-array-read-when-equal-of-take-and-constant
  (implies (and (equal k (take m x))
                (syntaxp (and (quotep k)
                              (not (quotep x))))
                (< n m)
                (< n len)
                (natp len)
                (natp n)
                (natp m)
                )
           (equal (bv-array-read size len n x)
                  (bv-array-read size len n k)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener) (NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm equal-of-slice-and-constant-when-equal-of-bvchop-and-constant2
  (implies (and (syntaxp (quotep k))
                (equal (bvchop size x) k2)
                (syntaxp (quotep k2))
                (not (equal (bvchop (- size low) k) (slice (+ -1 size) low k2)))
                (<= size high)
                (<= low size)
                (natp low)
                (natp k)
                (natp k2)
                (natp high))
           (equal (equal k (slice high low x))
                  nil))
  :hints (("Goal" :use (:instance split-bv (y (slice high low x)) (n (- (+ 1 high) low)) (m (- size low)))
           :in-theory (e/d (split-hack-lemma bvplus bvuminus bvminus bvmult ;bvcat logapp
                                             natp
                                             bvlt slice-of-sum-cases bvchop-of-sum-cases)
                           (bvcat-equal-rewrite-alt
;<-of-slice-and-slice-when-<-of-slice-and-slice
                            bvcat-equal-rewrite

                            bvminus-becomes-bvplus-of-bvuminus)))))

;note that we don't usually want to trim array reads
(defthmd getbit-of-bv-array-read-trim
  (implies (and (natp n)
                (< (+ 1 n) element-size) ;prevents loops
                (integerp element-size)
                )
           (equal (getbit n (bv-array-read element-size len index data))
                  (getbit n (bv-array-read (+ 1 n) len index data))))
  :hints (("Goal" :in-theory (e/d (getbit slice BVCHOP-OF-LOGTAIL bvchop-of-bv-array-read)
                                  (anti-slice)))))

;gen!
(defthm bvcat-of-slice-of-bv-array-read-and-bvcat-of-getbit-of-bv-array-read
  (equal (bvcat '5 (slice '7 '3 (bv-array-read '8 len index lst)) '3 (bvcat '1 (getbit '2 (bv-array-read '3 len index lst)) '2 x))
         (bvcat '6 (slice '7 '2 (bv-array-read '8 len index lst)) '2 x))
  :hints (("Goal" :in-theory (enable getbit-of-bv-array-read-trim))))

;kill
;; (defthm bvcat-of-slice-and-bvcat-of-getbit
;;   (equal (bvcat 29 (slice 31 3 y) 3 (bvcat 1 (getbit 2 y) 2 x))
;;          (bvcat 30 (slice 31 2 y) 2 x)))

;move
(defthm getbit-of-leftrotate32-high
  (implies (and (<= amt n) ;other case!
                (<= n 31)
                (unsigned-byte-p 5 amt)
                (natp n)
                (natp amt))
           (equal (getbit n (leftrotate32 amt x))
                  (getbit (- n amt) x)))
  :hints (("Goal" :in-theory (e/d (getbit) (bvchop-1-becomes-getbit
                                            leftrotate32
                                            slice-becomes-getbit)))))

;used to simplify the exit test for md5
(defthm boolor-of-sbvlt-combine-gen-better
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep k3)))
;                (natp k)
                (bvlt 32 k2 k3)
                ;;(equal k3 8)
                ;;(equal k2 4)
                (bvle 32 k (- k3))
                ;; (equal k 4294967288)
                (unsigned-byte-p 32 k)
                (< (+ k2 (expt 2 31)) k)
                (unsigned-byte-p 31 k2)
                (unsigned-byte-p 31 k3))
           (equal (boolor (sbvlt 32 (bvplus 32 k x) k2)
                          (sbvlt 32 x k3)
                          )
                  (sbvlt 32 x (+ k2 (- (expt 2 32) k)))))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 32 k)) (n 32) (m 31))
           :cases ((equal 0 (getbit 31 k)))
           :in-theory (e/d (sbvlt bvlt getbit-of-bvplus-split bvplus bvchop-of-sum-cases boolor
                                  bvcat getbit-of-plus
                                  logapp)
                           (bvcat-of-getbit-and-x-adjacent
                            bvcat-equal-rewrite-alt
                            )))))

(defthm boolor-of-sbvlt-combine-gen-better-alt
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep k3)))
                (bvlt 32 k2 k3) ;allow equal?
                ;;(equal k3 8)
                ;;(equal k2 4)
                (bvle 32 k (- k3))
                ;; (equal k 4294967288)
                (unsigned-byte-p 32 k)
                (< (+ k2 (expt 2 31)) k)
                (unsigned-byte-p 31 k2)
                (unsigned-byte-p 31 k3))
           (equal (boolor (sbvlt 32 x k3)
                          (sbvlt 32 (bvplus 32 k x) k2)
                          )
                  (sbvlt 32 x (+ k2 (- (expt 2 32) k)))))
  :hints (("Goal" :use (:instance boolor-of-sbvlt-combine-gen-better)
           :in-theory (union-theories '(boolor-commutative)
                                      (theory 'minimal-theory))
;;            :in-theory (disable boolor-of-sbvlt-combine-gen-better
;;                                EQUAL-OF-BVCHOP-EXTEND ;looped
;;                                )
           )))

(defthm boolor-of-sbvlt-combine-gen-better-extra-disjunct
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep k3)))
                (bvlt 32 k2 k3)
                (bvle 32 k (- k3))
                (unsigned-byte-p 32 k)
                (< (+ k2 (expt 2 31)) k)
                (unsigned-byte-p 31 k2)
                (unsigned-byte-p 31 k3))
           (equal (boolor (sbvlt 32 (bvplus 32 k x) k2)
                          (boolor (sbvlt 32 x k3)
                                  extra))
                  (boolor (sbvlt 32 x (+ k2 (- (expt 2 32) k)))
                          extra)))
  :hints (("Goal" :use (:instance boolor-of-sbvlt-combine-gen-better)
           :in-theory (disable boolor-of-sbvlt-combine-gen-better sbvlt-rewrite))))

(defthm boolor-of-sbvlt-combine-gen-better-alt-extra-disjunct
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)
                              (quotep k3)))
                (bvlt 32 k2 k3) ;allow equal?
                (bvle 32 k (- k3))
                (unsigned-byte-p 32 k)
                (< (+ k2 (expt 2 31)) k)
                (unsigned-byte-p 31 k2)
                (unsigned-byte-p 31 k3))
           (equal (boolor (sbvlt 32 x k3)
                          (boolor (sbvlt 32 (bvplus 32 k x) k2)
                                  extra))
                  (boolor (sbvlt 32 x (+ k2 (- (expt 2 32) k))) extra)))
  :hints (("Goal" :use (:instance boolor-of-sbvlt-combine-gen-better-alt)
           :in-theory (disable boolor-of-sbvlt-combine-gen-better-alt sbvlt-rewrite))))

(defthmd sha1-hack-a-million
  (implies (and ;unfortunately, this gets simplified before it can match.. change how the rewriter works in that case? - putting it first now!
                (not (sbvlt 32
                            (bvplus 32
                                    x (bvuminus 32 y))
                            64))
                (not (bvlt 31 x y)) ;y is a free var (try all matches?) ;;ffixme think about (not x) vs (equal nil x) vs (equal x nil) in a free var hyp...
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (equal 0 (slice 30 6 x))
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus bvuminus bvminus)
                                  (BVPLUS-ASSOCIATIVE-SIZES-DIFFER
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))
;can this loop?
(defthmd sha1-hack-a-million2
  (implies (and (not (sbvlt 32
                            (bvplus 32
                                    x (bvuminus 32 y))
                            64))
                (not (bvlt 31 x y)) ;y is a free var (try all matches?) ;;ffixme think about (not x) vs (equal nil x) vs (equal x nil) in a free var hyp...
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y)
                )
           (equal (equal 0 x)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus bvuminus bvminus)
                                  (BVPLUS-ASSOCIATIVE-SIZES-DIFFER
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))


;for sha1
;gen!
(defthm bvlt-of-bvplus-of-bvcat-of-slice
  (equal (bvlt '31 (bvplus '31 '2147483647 (bvcat '29 (slice '30 '2 x) '2 '0)) x)
         (not (equal 0 (slice '30 '2 x))))
  :hints (("Goal"
           :use (:instance split-bv (y (SLICE 30 0 X)) (n 31) (m 2))
           :in-theory (e/d (bvlt bvplus bvmult bvchop-of-sum-cases slice-of-sum-cases
                                 bvcat logapp)
                           (BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE

                            <-OF-BVCAT)))))

;was very slow!
(in-theory (disable BVPLUS-OF-BVCAT-HACK6-GEN-LOW-OPEN))

;gen!
(defthm sha1-hack-two-million
  (equal (bvlt 31 x
               (BVPLUS 31 2147483647
                       (BVCAT 25
                              (SLICE 30 6 x)
                              6 0)))
         (equal 0 (slice 30 6 x)))
  :hints (("Goal" :in-theory (enable bvlt bvplus bvchop-of-sum-cases slice-of-sum-cases))))

(defthm sha1-hack-two-million-alt
  (equal (bvlt 31 (BVPLUS 31 2147483647
                          (BVCAT 25
                                 (SLICE 30 6 x)
                                 6 0))
               x)
         (not (equal 0 (slice 30 6 x))))
  :hints (("Goal" :in-theory (enable bvlt bvplus bvchop-of-sum-cases slice-of-sum-cases))))

(defthm sha1-hack-three-million
  (implies (not (bvlt 31 x y))
           (equal (bvlt '25 (slice '30 '6 x) (bvplus '25 '1 (slice '30 '6 y)))
                  (if (equal (slice 30 6 y) 33554431)
                      nil
                    (equal (slice '30 '6 x) (slice '30 '6 y)))))
  :hints (("Goal"
           :use (:instance slice-monotone (x (bvchop 31 y)) (y (bvchop 31 x)) (low 6) (high 30))
           :in-theory (enable bvlt bvplus bvchop-of-sum-cases slice-of-sum-cases))))

(defthmd equal-of-slice-and-max-30-6
  (implies (unsigned-byte-p 31 x)
           (equal (equal (slice 30 6 x) 33554431)
                  (<= (* 64 33554431) (bvchop 31 x))))
  :hints (("Goal" :in-theory (e/d (slice logtail FLOOR-BOUNDED-BY-/)
                                  (UNSIGNED-BYTE-P-FROM-BOUND-CONSTANT-VERSION
                                   anti-slice)))))

(defthm slice-monotone-strong-30-6-helper
  (implies (and ;(not (equal (slice 30 6 x) 33554431))
            (<= (+ 64 y) x)
            (unsigned-byte-p 31 x)
            (unsigned-byte-p 31 y))
           (< (slice 30 6 y) (slice 30 6 x)))
  :hints (("Goal"
           :use (slice-bound-hack-31-64-6
                 (:instance slice-monotone (x (+ 64 Y)) (y x) (high 30) (low 6))
                 )
           :in-theory (e/d (SLICE-BOUND-LEMMA-GEN ;slice
                            equal-of-slice-and-max-30-6
                            slice-of-sum-cases
                            ) (anti-slice slice-monotone
                            slice-bound-hack-31-64-6
                            )))))

(defthmd logtail-when-huge-31-6
  (implies (and (<= 2147483584 y)
                (unsigned-byte-p 31 y))
           (equal (logtail 6 y)
                  33554431))
  :hints (("Goal" :in-theory (enable logtail))))

(defthmd slice-when-huge-31-6
  (implies (and (<= 2147483584 y)
                (unsigned-byte-p 31 y))
           (equal (slice 30 6 y)
                  33554431))
  :hints (("Goal" :in-theory (e/d (slice logtail-when-huge-31-6)
                                  (anti-slice bvchop-of-logtail)))))

;gen the 64?
(defthm slice-monotone-strong-30-6
  (implies (and (not (bvlt 31 x (bvplus 31 free y)))
                (equal free 64) ;poor man's limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (< (slice 30 6 y) (slice 30 6 x))
                  (not (equal (slice 30 6 y) 33554431))))
  :hints (("Goal" :use (:instance slice-monotone-strong-30-6-helper)
           :in-theory (e/d (slice-when-huge-31-6 bvlt bvplus bvchop-of-sum-cases)
                           (slice-monotone-strong-30-6-helper)))))

(defthm slice-monotone-strong-30-6-bv
  (implies (and (not (bvlt 31 x (bvplus 31 free y)))
                (equal free 64) ;poor man's limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 25 (slice 30 6 y) (slice 30 6 x))
                  (not (equal (slice 30 6 y) 33554431))))
  :hints (("Goal" :use (:instance slice-monotone-strong-30-6)
  :in-theory (e/d (bvlt) (slice-monotone-strong-30-6)))))


;y+64<=x
;rename
(defthmd equal-of-slice-and-slice-when
  (implies (and (not (bvlt 31 x (bvplus 31 free ;64
                                        y)))
                (equal free 64) ;poor man's limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (equal (slice 30 6 y) (slice 30 6 x))
                  (and (equal (slice 30 6 y) 33554431)
                       (equal 33554431 (slice 30 6 x)))))
  :hints (("Goal"
           :in-theory (enable bvlt bvplus bvchop-of-sum-cases slice-when-huge-31-6  equal-of-slice-and-max-30-6)
           :use (:instance slice-monotone-strong-30-6))))

(defthmd equal-of-slice-and-slice-when-alt
  (implies (and (not (bvlt 31 x (bvplus 31 free ;64
                                        y)))
                (equal free 64) ;poor man's limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (equal (slice 30 6 x) (slice 30 6 y))
                  (and (equal (slice 30 6 y) 33554431)
                       (equal 33554431 (slice 30 6 x)))))
  :hints (("Goal" :use (:instance equal-of-slice-and-slice-when)
           :in-theory (disable equal-of-slice-and-slice-when))))

;gen
(defthm bvlt-when-slice-known-hack
  (implies (and (EQUAL k (SLICE '30 '2 x))
                (equal k '536870911)  ;poor mans' limit
                (unsigned-byte-p 31 x) ;drop
                )
           (equal (BVLT '31 '2147483583 x)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt slice logtail floor-bounded-by-/) (anti-slice)))))

(defthm items-have-len-of-myif
  (equal (items-have-len n (myif test x y))
         (myif test
               (items-have-len n x)
               (items-have-len n y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm bvlt-of-huge-when-slice-not-max
  (implies (and (syntaxp (quotep k))
                (bvle 31 (- (expt 2 31) 5) k)
                (not (equal free (slice 30 2 x)))
                (equal free 536870911) ;poor man's limit
                (unsigned-byte-p 31 x) ;drop?
                )
           (equal (bvlt 31 k x)
                  nil))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthmd <-of-slice-and-1-30-6
  (implies (unsigned-byte-p 31 x)
           (equal (< (slice 30 6 x) 1)
                  (< x 64))))

(defthm slice-of-nth-becomes-bv-array-read
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp high)
                (Natp n)
                (<= low high)
                (natp low))
           (equal (slice high low (nth n data))
                  (if (< n (len data))
                      (slice high low (bv-array-read (+ 1 high) (len data) n data))
                    0)))
  :hints (("Goal"
;           :use (:instance bvchop-of-nth-becomes-bv-array-read (size (+ 1 high)))
           :in-theory (e/d (slice BVCHOP-OF-LOGTAIL BV-ARRAY-READ ;LIST::NTH-WITH-LARGE-INDEX
                                  ceiling-of-lg)
                           ( ;bvchop-of-nth-becomes-bv-array-read
                            NTH-BECOMES-BV-ARRAY-READ2
                            anti-slice)))))

;more like this?!
(defthm bvxor-of-nth-arg2
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bvxor size (nth n data) y)
                  (if (< n (len data))
                      (bvxor size (bv-array-read size (len data) n data) y)
                    (bvchop size y))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bvxor-of-nth-arg3
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bvxor size y (nth n data))
                  (if (< n (len data))
                      (bvxor size y (bv-array-read size (len data) n data))
                    (bvchop size y))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bitxor-of-nth-arg1
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bitxor (nth n data) y)
                  (if (< n (len data))
                      (bitxor (bv-array-read 1 (len data) n data) y)
                    (getbit 0 y))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER)
                                  (
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bitxor-of-nth-arg2
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bitxor y (nth n data))
                  (if (< n (len data))
                      (bitxor y (bv-array-read 1 (len data) n data))
                    (getbit 0 y))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bvcat-of-nth-arg2
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bvcat highsize (nth n data) lowsize lowval)
                  (if (< n (len data))
                      (bvcat highsize (bv-array-read highsize (len data) n data) lowsize lowval)
                    (bvcat highsize 0 lowsize lowval))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bvcat-of-nth-arg4
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bvcat highsize highval lowsize (nth n data))
                  (if (< n (len data))
                      (bvcat highsize highval lowsize (bv-array-read lowsize (len data) n data))
                    (bvcat highsize highval lowsize 0))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthmd bvplus-of-myif-arg3
  (equal (bvplus size x (myif test a b))
         (bvplus size x (bvif size test a b)))
  :hints (("Goal" :in-theory (enable bvplus myif))))

(defthmd bvplus-of-myif-arg2
  (equal (bvplus size (myif test a b) x)
         (bvplus size (bvif size test a b) x))
  :hints (("Goal" :in-theory (enable bvplus myif))))

(defthm getbit-of-nth-becomes-bv-array-read
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp m)
                (natp n))
           (equal (getbit m (nth n data))
                  (if (< n (len data))
                      (getbit m (bv-array-read (+ 1 m) (len data) n data))
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bvif-of-nth-arg4
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bvif size test y (nth n data))
                  (if (< n (len data))
                      (bvif size test y (bv-array-read size (len data) n data))
                    (bvif size test y 0))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   boolor)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bvif-of-nth-arg3
  (implies (and ;(all-unsigned-byte-p free data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists
                (natp n))
           (equal (bvif size test (nth n data) y)
                  (if (< n (len data))
                      (bvif size test (bv-array-read size (len data) n data) y)
                    (bvif size test 0 y))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   boolor)
                                  (BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   ;NTH-BECOMES-BV-ARRAY-READ2
                                   ;NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2
                                   )))))

(defthm nth-becomes-bv-array-read-strong
  (implies (and (all-unsigned-byte-p free data)
                (natp n))
           (equal (nth n data)
                  (if (< n (len data))
                      (bv-array-read free (len data) n data)
                    nil)))
  :hints (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg ;LIST::NTH-WITH-LARGE-INDEX
                                                 )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                                   BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ ;looped
                                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm sha1-hack-four-million
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt '25 (bvplus '25 '33554431 (slice '30 '6 y)) (slice '30 '6 x))
                  nil))
  :hints (("Goal"
           :use (:instance slice-monotone (x (+ 64 x)) (high 30) (low 6))
           :in-theory (e/d (bvlt sbvlt bvplus bvchop-of-sum-cases bvuminus bvminus slice-of-sum-cases
                                 equal-of-slice-and-max-30-6)
                           (sbvlt-rewrite bvminus-becomes-bvplus-of-bvuminus)))))

(defthm sha1-hack-four-million-one
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (BVLT '31 '2147483583 x)
                  nil))
  :hints (("Goal"
           :use (:instance slice-monotone (x (+ 64 x)) (high 30) (low 6))
           :in-theory (e/d (bvlt sbvlt bvplus bvchop-of-sum-cases bvuminus bvminus slice-of-sum-cases
                                 equal-of-slice-and-max-30-6)
                           (sbvlt-rewrite bvminus-becomes-bvplus-of-bvuminus)))))

(defthm sha1-hack-four-million-three
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (EQUAL '33554431 (SLICE '30 '6 5))
                  nil))
  :hints (("Goal"
           :use (:instance slice-monotone (x (+ 64 x)) (high 30) (low 6))
           :in-theory (e/d (bvlt sbvlt bvplus bvchop-of-sum-cases bvuminus bvminus slice-of-sum-cases
                                 equal-of-slice-and-max-30-6)
                           (sbvlt-rewrite bvminus-becomes-bvplus-of-bvuminus)))))

(defthm sha1-hack-four-million-five
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
;                (EQUAL (BVCHOP '6 x) '0)
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (equal (SLICE '30 '6 Y) (SLICE '30 '6 x))
                  nil))
  :hints (("Goal"
           :use (:instance slice-monotone (x (+ 64 x)) (high 30) (low 6))
           :expand ((UNSIGNED-BYTE-P 31 (+ 64 X)))
           :in-theory (e/d (bvlt sbvlt bvplus bvchop-of-sum-cases bvuminus bvminus slice-of-sum-cases
                                 bvcat
                                 equal-of-slice-and-max-30-6)
                           (sbvlt-rewrite bvminus-becomes-bvplus-of-bvuminus)))))

(defthm sha1-hack-four-million-five-alt
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
;                (EQUAL (BVCHOP '6 x) '0)
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (equal (SLICE '30 '6 x) (SLICE '30 '6 Y))
                  nil))
  :hints (("Goal" :use (:instance sha1-hack-four-million-five)
           :in-theory (disable sha1-hack-four-million-five))))

(defthm sha1-hack-four-million-four
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
                (EQUAL (BVCHOP '6 x) '0)
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y)
                (natp k) (<= k 63)
                (unsigned-byte-p 31 k) ;drop
                )
           (equal (BVLT '31
                        k
                        (BVPLUS '31
                                (BVCAT '25 (SLICE '30 '6 Y) '6 '0)
                                (BVUMINUS '31
                                          (BVCAT '25 (SLICE '30 '6 X) '6 '0))))
                  t))
  :hints (("Goal"
           :use (:instance slice-monotone (x (+ 64 x)) (high 30) (low 6))
           :expand ((UNSIGNED-BYTE-P 31 (+ 64 X)))
           :in-theory (e/d (bvlt sbvlt bvplus bvchop-of-sum-cases bvuminus bvminus slice-of-sum-cases
                                 bvcat
                                 equal-of-slice-and-max-30-6)
                           (sbvlt-rewrite bvminus-becomes-bvplus-of-bvuminus)))))

(defthm sha1-hack-four-million-six
  (implies (and (not (sbvlt '32
                            (bvplus '32
                                    y
                                    (bvuminus '32 x))
                            free))
                (equal free 64) ;poor man's limit
                (EQUAL (BVCHOP '6 x) '0)
                (equal (bvlt '31 y x) 'nil)
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (EQUAL '0
                         (SLICE '30
                                '6
                                (BVPLUS '31
                                        (BVCAT '25 (SLICE '30 '6 Y) '6 '0)
                                        (BVUMINUS '31
                                                  (BVCAT '25 (SLICE '30 '6 X) '6 '0)))))
                  nil))
  :hints (("Goal"
           :use (:instance slice-monotone (x (+ 64 x)) (high 30) (low 6))
           :expand ((UNSIGNED-BYTE-P 31 (+ 64 X)))
           :in-theory (e/d (bvlt sbvlt bvplus bvchop-of-sum-cases bvuminus bvminus slice-of-sum-cases
                                 bvcat
                                 equal-of-slice-and-max-30-6)
                           (sbvlt-rewrite bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd usb-hack-100
  (implies (AND (<= Y X)
                (NATP Y)
                (UNSIGNED-BYTE-P XSIZE X))
           (UNSIGNED-BYTE-P XSIZE Y))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))



(defthm bv-array-read-of-+
  (implies (and (power-of-2p len) ;require syntaxp?
                (integerp x)
                (integerp y))
           (equal (bv-array-read size len (+ x y) data)
                  (bv-array-read size len (bvplus (lg len) x y) data)))
  :hints (("Goal"
           :use (:instance bv-array-read-of-bvchop (n (lg len)) (index (+ x y)) (vals data))
           :in-theory (e/d ( ;bv-array-read
                            bvplus
                            power-of-2p
                            ) (bv-array-read-of-bvchop)))))



(defthm getbit-of-bvmult-of-expt
  (implies (and (< n (+ 1 size))
                (>= size2 (+ 1 size))
                (integerp x)
                (natp size)
                (natp size2)
                (natp n))
           (equal (getbit size (bvmult size2 (expt 2 n) x))
                  (getbit (- size n) x)))
  :hints (("Goal" :in-theory (e/d (bvmult getbit
                                          natp ;yuck
                                          )
                                  (slice-becomes-getbit bvchop-1-becomes-getbit)))))

(defthm getbit-of-bvmult-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (< (lg k) (+ 1 size))
                (>= size2 (+ 1 size))
                (integerp x)
                (natp size)
                (natp size2)
                (natp (lg k)))
           (equal (getbit size (bvmult size2 k x))
                  (getbit (- size (lg k)) x)))
  :hints (("Goal" :use (:instance getbit-of-bvmult-of-expt (n (lg k)))
           :in-theory (disable getbit-of-bvmult-of-expt))))

;fragile - what if the disjuncts get out of order or other ones intervene?
(defthm boolor-adjacent-ranges-sha1-hack
  (implies (unsigned-byte-p 31 x) ;drop?
           (equal (boolor (not (bvlt '31 '2147483643 x)) (equal '536870911 (slice '30 '2 x)))
                  t))
  :hints (("Goal" :in-theory (enable bvlt))))



(defthm +-of-bvplus-of-1-and-unary-minus-same
  (implies (and (unsigned-byte-p size x) ;slow?
                (natp size))
           (equal (binary-+ (bvplus size 1 x) (unary-- x))
                  (if (equal (+ -1 (expt 2 size)) x)
                      (- (+ -1 (expt 2 size)))
                    1)))
  :hints (("Goal" :in-theory (enable bvplus))))

;gen?!
(defthm +-of-bvplus-of-2-and-unary-minus-same
  (implies (and (unsigned-byte-p size x) ;slow?
                (posp size))
           (equal (+ (bvplus size 2 x) (- x))
                  (if (<= (+ -2 (expt 2 size)) x)
                      (+ 2 (- (EXPT 2 SIZE))) ;yy ;(- (+ -1 (expt 2 size)))
                    2)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthmd unsigned-byte-p-when-unsigned-byte-p-free-better
  (implies (and (unsigned-byte-p xsize x)
                (<= y x))
           (equal (unsigned-byte-p xsize y)
                  (natp y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))



;constant version?
(defthm equal-of-logtail-and-floor-of-expt-same
  (implies (and (integerp x)
                (Natp n))
           (equal (equal (logtail n x) (floor x (expt 2 n)))
                  t))
  :hints (("Goal" :in-theory (e/d (slice logtail) (bvchop-of-logtail-becomes-slice)))))

;constant version?
(defthm equal-of-slice-and-floor-of-expt-same
  (implies (and (integerp y)
                (natp low)
                (<= low high)
                (natp high))
           (equal (equal (slice high low y) (floor y (expt 2 low)))
                  (unsigned-byte-p (+ 1 high) y)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (bvchop-of-logtail-becomes-slice)))))

;constant version?
(defthm equal-of-floor-of-expt-and-bv
  (implies (and (unsigned-byte-p xsize x) ;use bind-free?
                (natp n)
                (posp xsize)
                (integerp y))
           (equal (equal (floor y (expt 2 n)) x)
                  (if (< y 0)
                      nil
                    (if (<= (expt 2 (+ xsize n)) y)
                        nil
                      (equal (slice (+ -1 xsize n) n y) x)))))
  :hints (("Goal"; :cases ((integerp xsize))
           :in-theory (enable natp))))



(in-theory (disable BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS))

;gen!
(defthm bvplus-of-bvuminus-of-slice-and-bvcat-of-slice
  (implies (and (syntaxp (quotep k))
                (bvle 4 (slice 5 2 x) k) ;limit? or we could use the fact that we know these 4 bits to turn (slice 30 2 x) into a cat
                )
           (equal (bvplus 29 (bvuminus 29 (slice 30 2 x))
                          (bvcat 25 (slice 30 6 x) 4 k))
                  (bvminus 4 k (slice 5 2 x))))
  :hints (("Goal"
           :use (:instance SPLIT-BV (y (SLICE 30 2 X)) (n 29) (m 4))

           :in-theory (enable bvplus bvuminus bvminus bvchop-of-sum-cases bvlt bvcat logapp))))






(defthm *-of-1/4-and-bvcat-of-0
  (equal (* 1/4 (BVCAT highsize highval 2 0)) ;gen the 2 (and maybe the 0)?
         (bvchop highsize highval))
  :hints (("Goal" :in-theory (enable bvcat))))

(defthm *-of-1/16-and-bvcat-of-0
  (equal (* 1/16 (BVCAT highsize highval 4 0)) ;gen the 2 (and maybe the 0)?
         (bvchop highsize highval))
  :hints (("Goal" :in-theory (enable bvcat))))


(defthm equal-of-0-and-*-of-constant
  (implies (and (syntaxp (quotep k))
                (acl2-numberp k))
           (equal (equal 0 (* k x))
                  (if (equal 0 k)
                      t
                    (equal 0 (fix x))))))

;gen!
(defthm bvchop-of-1/4
  (implies (integerp x)
           (equal (bvchop 4 (* 1/4 x))
                  (if (equal 0 (mod x 4))
                      (slice 5 2 x)
                    0)))
  :hints (("Goal" :in-theory (e/d (slice logtail bvchop
                                         mod-is-0-when-multiple)
                                  (anti-slice
                                   MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                   MOD-OF-EXPT-OF-2)))))

;see 0-<-*
(defthm <-of-0-and-*
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (equal (< 0 (* x y))
                  (and (not (equal x 0))
                       (not (equal y 0))
                       (equal (< 0 x) (< 0 y))))))

;gen the -1
(defthm <-of-minus1-and-floor
  (implies (and (rationalp x)
                (posp j))
           (equal (< -1 (floor x j))
                  (<= 0 x))))

;(set-body bvchop$inline (:definition bvchop$inline))

(defthm equal-of-*-of-1/4-and-slice-of-2 ;gen!
  (implies (rationalp x)
           (equal (equal (binary-* 1/4 x) (slice 31 2 x))
                  (and (equal 0 (bvchop 2 x))
                       (unsigned-byte-p 32 x))))
  :hints (("Goal" :expand ((bvchop 2 x))
           :in-theory (e/d (slice logtail ;bvchop
                                  )
                           (anti-slice
                            floor-becomes-slice-when-unsigned-byte-p ;add to anti-slice
                            )))))

(defthm <-of-floor-constant-when-not-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (rationalp k))
           (equal (< (floor i j) k)
                  (< (floor i j) (ceiling k 1))))
  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor-alt
                                     FLOOR-BOUNDED-BY-/))))

;gen the len to any known nat (or add a backchain limit)
(defthm <-of-len-and-expt-of-2
  (implies (natp n)
           (equal (< (len x) (expt 2 n))
                  (unsigned-byte-p n (len x)))))

;newly disabled
(defthmd <-of-len-and-expt-of-2-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (natp (lg k)))
           (equal (< (len x) k)
                  (unsigned-byte-p (lg k) (len x))))
  :hints (("Goal" :use (:instance <-of-len-and-expt-of-2 (n (lg k)))
           :in-theory (disable <-of-len-and-expt-of-2))))

(set-body unsigned-byte-p (:definition unsigned-byte-p))

;can cause a case split
(defthm unsigned-byte-p-of-bvuminus-bigger
  (equal (unsigned-byte-p m (bvuminus n x))
         (and (natp m)
              (boolor (equal 0 (bvchop n x))
                      (bvlt n (- (expt 2 n) (expt 2 m))  x))))
  :hints (("Goal" :in-theory (enable bvuminus bvminus bvlt UNSIGNED-BYTE-P))))

(defthm boolor-of-not-and-booland-same-1
  (equal (boolor (not x) (booland x y))
         (boolor (not x) y))
  :hints (("Goal" :in-theory (enable booland))))

;gen
(defthm equal-of-bvplus-of-bvchop-and-bvplus-same
  (equal (equal (bvplus '3 '1 (bvchop '2 x))
                (bvplus '2 '1 x))
         (not (equal 3 (bvchop 2 x)))))

;gen
(defthmd lowbits-not-0-helper
  (IMPLIES (AND (< 2147483648 K)
                (UNSIGNED-BYTE-P 32 K))
           (equal (EQUAL (BVCHOP 31 K) 0)
                  nil))
  :hints (("Goal" :in-theory (e/d (bvchop unsigned-byte-p
                                           )
                                  (MOD-OF-EXPT-OF-2
                                   MOD-OF-EXPT-OF-2-constant-version
                                   )))))

;; (thm
;;  (equal (< (+ (bvchop 31 x) y) x)
;;         (< y (* (expt 2 31) (logtail 31 x))))
;;  :hints (("Goal" :use (:instance split-bv (y x) (

(defthmd UNSIGNED-BYTE-P-when-top-bit-1
  (implies (EQUAL 1 (GETBIT 31 K))
           (equal (UNSIGNED-BYTE-P 32 K)
                  (equal k (bvcat 1 1 31 (bvchop 31 k))))))

;fixme restrict to constants?
(defthm sbvlt-of-constant-and-bvplus-of-constant
  (implies (and (syntaxp (quotep k)) ;Fri Mar 18 19:44:02 2011
                (< (expt 2 31) k) ;handles "negative" constants     ;other case? ;Sun Mar 28 15:21:30 2010 moved to first hyp
                (unsigned-byte-p 31 x) ;limit? ;drop?
                (unsigned-byte-p 32 k))
           (equal (sbvlt '32 '0 (bvplus '32 k x))
                  (sbvlt '32 (- 4294967296 k) x) ;this can be further simplified
                  ))
  :hints (("Goal"
           :cases ((equal 0 (getbit 31 x)))
           :use (:instance split-bv (y k) (n 32) (m 31))
           :in-theory (e/d (;UNSIGNED-BYTE-P-when-top-bit-1
                            bvplus bvlt bvchop-of-sum-cases lowbits-not-0-helper getbit-of-plus
                                   bvcat
                            logapp)
                           (
                            GETBIT-WHEN-BOUND
                            GETBIT-WHEN-BOUND4
                            BVCAT-OF-+-LOW
                            BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE)))))

(defthm nth-of-bv-array-clear-range-contained
  (implies (and (<= low index)
                (<= index high)
                (< high len)
                (natp low)
                (natp len)
                (natp high)
                (natp index))
           (equal (nth index (bv-array-clear-range size len low high data))
                  0))
  :hints (("Goal" :in-theory (enable bv-array-clear-range
                                     bv-array-clear))))

(defthm bv-array-clear-of-0-arg2
  (equal (bv-array-clear size 0 index data)
         nil)
  :hints (("Goal" :in-theory (enable bv-array-clear))))

;; (DEFTHM BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF-gen
;;   (IMPLIES
;;    (AND (SYNTAXP (SMALLER-TERMP INDEX2 INDEX1))
;;         (<= ELEMENT-SIZE2 ELEMENT-SIZE1)
;; ;        (< INDEX1 LEN)
;;  ;       (< INDEX2 LEN)
;;         (NATP INDEX1)
;;         (NATP INDEX2)
;;         (NATP LEN)
;;         (NATP ELEMENT-SIZE1)
;;         (NATP ELEMENT-SIZE2))
;;    (EQUAL (BV-ARRAY-CLEAR
;;            ELEMENT-SIZE1 LEN INDEX1
;;            (BV-ARRAY-CLEAR ELEMENT-SIZE2 LEN INDEX2 LST))
;;           (BV-ARRAY-CLEAR
;;            ELEMENT-SIZE2 LEN INDEX2
;;            (BV-ARRAY-CLEAR ELEMENT-SIZE2 LEN INDEX1 LST))))
;;   :hints (("Goal" :use (:instance BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF)
;;            :in-theory (e/d (BV-ARRAY-CLEAR)
;;                            ( BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF)))))

(defthm bv-array-clear-of-bv-array-clear-range
  (implies (and (< index len)
                (< high len)
                (< low len)
                (natp len)
                (natp low)
                (natp high)
                (natp size)
                (natp index))
           (equal (bv-array-clear size len index (bv-array-clear-range size len low high data))
                  (bv-array-clear-range size len low high (bv-array-clear size len index data))))
  :hints (("Goal"
           ;;:induct (clear-ind index high data)
           :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bv-array-clear-range)
                           (bv-array-clear-range-same
                            update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-range-of-bv-array-write-contained
  (implies (and (<= low index)
                (<= index high)
                (< high len)
                (equal len (len data))
                (natp len)
                (natp low)
                (natp high)
                (natp size)
                (natp index))
           (equal (bv-array-clear-range size len low high (bv-array-write size len index val data))
                  (bv-array-clear-range size len low high data)))
  :hints (("Subgoal *1/2" :cases ((< high (+ 1 index))))
          ("Goal"
;:induct (clear-ind index high data)
           :induct t
           :do-not '(generalize eliminate-destructors)
           :expand ((BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          LOW HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          HIGH VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          (+ 1 HIGH)
                                          HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          HIGH VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          HIGH HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          HIGH VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          (+ 1 HIGH)
                                          HIGH DATA)
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          LOW HIGH DATA)
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          LOW HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          INDEX VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          INDEX HIGH DATA)
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          INDEX HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          INDEX VAL DATA)))

           :in-theory (e/d ((:induction bv-array-clear-range)
;bv-array-write UPDATE-NTH2
                            )
                           (BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR
                            bv-array-clear-range-same
                            BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR-ADJACENT2
;                           BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE
                            BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE-ADJACENT1
                            BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR-ADJACENT1
                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

;gen!
(defthm slice-when-bvchop-known-2
  (implies (and (equal free (bvchop 6 x))
                (syntaxp (quotep free)))
           (equal (slice 30 2 x)
                  (bvcat 25 (slice 30 6 x) 4 (slice 5 2 free)))))

;slow?
(defthm bvplus-of-bvcat-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep lowsize)))
                (equal (+ lowsize 25) size)
                (unsigned-byte-p lowsize k2)
                (equal 6 lowsize) ;gen!
                (unsigned-byte-p (+ lowsize 25) k1)
                (unsigned-byte-p 25 x))
           (equal (bvplus size k1 (bvcat 25 x lowsize k2))
                  (bvcat 25 (bvplus 25 (slice (+ lowsize 25) lowsize (+ k1 k2)) x) lowsize (bvchop lowsize (+ k1 k2)))))
  :hints (("Goal"
           :use (:instance split-bv (y k1) (n (+ lowsize 25)) (m lowsize))
           :in-theory (enable bvchop-of-sum-cases
                              slice-of-sum-cases
                              logapp
                              bvplus bvcat))))

;more versions?
(defthm booland-of-not-of-equal-and-equal-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal k1 k2)))
           (equal (booland (not (equal k1 x)) (equal k2 x))
                  (equal k2 x))))

(defthm booland-of-not-of-equal-and-equal-constants-alt
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal k1 k2)))
           (equal (booland (equal k2 x) (not (equal k1 x)))
                  (equal k2 x))))

(defthm myif-of-boolor-same
  (equal (myif x (boolor x y) z)
         (myif x t z))
  :hints (("Goal" :in-theory (enable boolor myif))))

(defthmd myfirst-of-myif-arg2
  (equal (take n (myif test a b))
         (myif test (take n a)
               (take n b)))
  :hints (("Goal" :in-theory (enable myif))))

;slow?
(defthm unsigned-byte-p-of-+
  (implies (and (unsigned-byte-p (+ -1 size) x)
                (unsigned-byte-p (+ -1 size) z)
                (natp size))
           (unsigned-byte-p size (+ x z)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     expt-of-+))))

(defthm bvlt-of-bitxor-of-1-same
  (equal (bvlt 1 (bitxor 1 x) x)
         (equal 1 (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm bvlt-of-bitxor-of-1-same-two
  (equal (bvlt 1 x (bitxor 1 x))
         (equal 0 (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm <-of-shift-of-slice-and-same
  (implies (and ;(natp k)
                (< lowsize size)
                (natp size)
                (natp lowsize))
           (equal (< (* (expt 2 lowsize) (slice (+ -1 size) lowsize k))
                     (bvchop size k))
                  (not (equal 0 (bvchop lowsize k)))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp)
                                  (BVCAT-SLICE-SAME
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   LOGAPP-EQUAL-REWRITE
                                   LOGAPP-EQUAL-REWRITE))
           :use (:instance split-bv (y (bvchop size k)) (n size) (m lowsize)))))

(defthm <-of-shift-of-slice-and-same-special
  (implies (and ;(natp k)
                (< 1 size)
                (natp size))
           (equal (< (* 2 (slice (+ -1 size) 1 k))
                     (bvchop size k))
                  (not (equal 0 (bvchop 1 k)))))
  :hints (("Goal" :use (:instance <-of-shift-of-slice-and-same (lowsize 1))
           :in-theory (disable <-of-shift-of-slice-and-same))))

(defthm bitxor-of-minus-of-expt
  (implies (posp size) ;gen?
           (equal (bitxor (- (expt 2 size)) y)
                  (getbit 0 y))))

;move
(defthm equal-of-+-and-+-cancel-3-3
  (equal (equal (+ x y z) (+ w v z))
         (equal (+ x y) (+ w v))))

;move
(defthm equal-of-+-and-+-cancel-2-3
  (equal (equal (+ x z) (+ w v z))
         (equal (fix x) (+ w v))))

;move
(defthm equal-of-+-and-+-cancel-2-4
  (equal (equal (+ x z) (+ w v u z))
         (equal (fix x) (+ w v u))))

(defthm bvchop-non-negative-linear
  (<= 0 (BVCHOP N X))
  :rule-classes (:linear))

(defthm bvplus-of-constant-and-bvcat-of-0
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (natp lowsize)
                (< lowsize size)
                (natp size)
                (integerp x)
                (equal highsize (- size lowsize))
                )
           (equal (bvplus size k (bvcat highsize x lowsize 0))
                  (bvcat highsize (bvplus highsize x (slice (+ -1 size) lowsize k))
                         lowsize (bvchop lowsize k))))
  :hints (("Goal" :in-theory (e/d ( ;bvcat logapp bvplus ;bvchop-of-sum-cases
                                   SLICE-OF-BVPLUS-CASES
                                   bvlt
                                   )
                                  (LOGAPP-EQUAL-REWRITE
                                   ;bvplus-of-0
                                   )))))





(defthm bitxor-of-minus
  (implies (integerp x)
           (equal (bitxor 1 (unary-- x))
                  (bitxor 1 (getbit 0 x))))
  :hints (("Goal" :in-theory (e/d (bitxor bvxor) (bvxor-1-becomes-bitxor)))))

;gen!
(defthm floor-of-*-of-8-and-32
 (implies (rationalp x)
          (equal (floor (* 8 x) 32)
                 (floor x 4))))

(defthmd consp-becomes-<-of-len
  (equal (consp x)
         (not (equal 0 (len x)))))

;use polarities?
;gen!
(defthm equal-of-constant-and-slice-when-equal-of-constant-and-bvchop
  (implies (and (syntaxp (quotep k)) ;quotep hyps are new
                (equal k2 (bvchop 2 x))
                (syntaxp (quotep k2)))
           (equal (equal k (slice 5 2 x))
                  (booland (unsigned-byte-p 4 k)
                           (equal (bvcat 4 k 2 k2)
                                  (bvchop 6 x)))))
  :hints (("Goal" :in-theory (enable booland))))

(defthm nthcdr-of-bv-array-write-is-nil
  (implies (and (<= len n)
                (integerp len)
                (integerp n))
           (equal (nthcdr n (bv-array-write element-size len key val lst))
                  nil)))

;gen!
(defthm bvlt-of-2147483583
  (implies (and (equal k (bvchop '6 x23))
                (syntaxp (quotep k)))
           (equal (bvlt '31 '2147483583 x23) ;gen the constant?
                  (booland (unsigned-byte-p 6 k)
                           (equal ;2147483584
                            (bvcat 25 33554431 6 k)
                            (bvchop 31 x23)))))
  :hints (("Goal" :use (:instance split-bv (y (bvchop 31 x23)) (n 31) (m 6))
           :in-theory (e/d (bvlt) (bvcat-slice-same BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE BVCAT-OF-SLICE-ONTO-CONSTANT BVCAT-OF-SLICE-AND-X-ADJACENT
                                                    )))))

;move
(defthm bvcat-subst-constant-arg2
  (implies (and (syntaxp (not (quotep highval)))
                (equal k (bvchop free highval))
                (syntaxp (quotep k))
                (<= highsize free)
                (integerp free))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize k lowsize lowval))))

(defthm bvcat-subst-constant-arg4
  (implies (and (syntaxp (not (quotep lowval)))
                (equal k (bvchop free lowval))
                (syntaxp (quotep k))
                (<= lowsize free)
                (integerp free))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize k))))




;gen!
(defthm equal-of-0-and-slice-when-bvlt
  (implies (and (bvlt 6 k x)
                (syntaxp (quotep k))
                (bvle 6 3 k) ;gets computed
                )
           (equal (equal 0 (slice 5 2 x)) ;ffixme just turn this into a bound?
                  nil))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 6 x)) (m 2) (n 6))
           :in-theory (e/d (bvlt
                            ) (BVCAT-EQUAL-REWRITE-ALT
                            BVCAT-EQUAL-REWRITE
;BVCAT-OF-0
                            BVCAT-TIGHTEN-UPPER-SIZE
                            REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2)))))

;weird but showed up in the sha1 loop proof (during backchaining)
(defthm bvif-of-equal-of-bvchop-same
  (implies (and (syntaxp (and (quotep k)
                              (not (quotep x)))))
           (equal (bvif size (equal k (bvchop size x)) x y)
                  (bvif size (equal k (bvchop size x)) k y))))

;gen
(defthm bvlt-of-constant-and-slice
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 4 k))
           (equal (bvlt 4 k (slice 5 2 x))
                  (bvlt 6
                        (+ -1 (* 4 (+ 1 k))) ;gets computed
                        x)))
  :hints (("Goal" :in-theory (enable bvlt slice-bound-lemma-gen2))))

(defthm unsigned-byte-p-of-bvchop-bigger
  (equal (unsigned-byte-p '31 (bvchop '32 x))
         (bvlt 32 x 2147483648))
  :hints (("Goal" :in-theory (enable bvlt))))

;gross?
;move like this? alt versions?
(defthm bvplus-of-bvuminus-when-equal-hack
  (implies (equal (bvplus size free x2) x20)
           (equal (bvplus size (bvuminus size x2) x20)
                  (bvchop size free))))

;gen!
(defthm equal-of-constant-and-slice-when-equal-of-constant-and-slice
  (implies (and (syntaxp (quotep k))
                (equal free (slice 5 2 x))
                (syntaxp (quotep free))
                (not (equal free (bvchop 4 k)))
                )
           (equal (equal k (slice 30 2 x))
                  nil)))

;; (thm
;;  (implies (and (rationalp i)
;;                (posp j))
;;           (<= (+ i (- j))
;;               (* j (floor i j))))
;;  :hints (("Goal"
;;           :use (:instance floor-lower-bound (x i) (y j))
;;           :in-theory (e/d (posp) (;FLOOR-BOUNDED-BY-/
;;                                   )))))

(defthm floor-bound-lemma100
  (implies (and (rationalp i)
                (posp j))
           (equal (equal (* j (floor i j))
                         (+ i (- j)))
                  nil))
  :hints (("Goal"
           :use (:instance my-floor-lower-bound)
           :in-theory (e/d (posp) ( ;FLOOR-BOUNDED-BY-/
                                   )))))


(local
 (defthmd equal-of-slice-helper
   (implies (and (unsigned-byte-p (+ 1 high) x)
                 (natp high)
                 (natp low)
                 (<= low high))
            (equal (equal k (slice high low x))
                   (and (unsigned-byte-p (+ 1 high (- low)) k)
                        (<= (bvchop (+ 1 high) x) (+ -1 (* (+ 1 k) (expt 2 low))))
                        (<= (* k (expt 2 low)) (bvchop (+ 1 high) x)))))
   :hints (("Goal" :in-theory (e/d (slice logtail) (bvchop-of-logtail-becomes-slice
                                                    EQUAL-OF-FLOOR-OF-EXPT-AND-BV
                                                    FLOOR-BECOMES-SLICE-WHEN-UNSIGNED-BYTE-P))))))

(defthmd equal-of-slice
  (implies (and (<= low high)
                (natp high)
                (natp low))
           (equal (equal k (slice high low x))
                  (and (unsigned-byte-p (+ 1 high (- low)) k)
                       (<= (bvchop (+ 1 high) x) (+ -1 (* (+ 1 k) (expt 2 low))))
                       (<= (* k (expt 2 low)) (bvchop (+ 1 high) x)))))
  :hints (("Goal" :use (:instance equal-of-slice-helper (x (bvchop (+ 1 high) x))))))

(local
 (defthmd <-of-slice-arg2-helper
   (implies (and (unsigned-byte-p (+ 1 high) x)
                 (unsigned-byte-p (+ 1 high (- low)) k)
                 (natp high)
                 (natp low)
                 (<= low high))
            (equal (< k (slice high low x))
                   (<= (* (+ 1 k) (expt 2 low)) (bvchop (+ 1 high) x))))
   :hints (("Goal" :in-theory (e/d (<-of-floor-arg1 <-of-floor-arg2 slice logtail)
                                   (bvchop-of-logtail-becomes-slice
                                    EQUAL-OF-FLOOR-OF-EXPT-AND-BV
                                    FLOOR-BECOMES-SLICE-WHEN-UNSIGNED-BYTE-P))))))

(defthmd <-of-slice-arg2
  (implies (and (unsigned-byte-p (+ 1 high (- low)) k) ;move to conclusion?
                (natp high)
                (natp low)
                (<= low high))
           (equal (< k (slice high low x))
                  (<= (* (+ 1 k) (expt 2 low)) (bvchop (+ 1 high) x))))
  :hints (("Goal" :use (:instance <-of-slice-arg2-helper (x (bvchop (+ 1 high) x))))))

(local
 (defthmd <-of-slice-arg1-helper
   (implies (and (unsigned-byte-p (+ 1 high) x)
                 (unsigned-byte-p (+ 1 high (- low)) k) ;move to conclusion?
                 (natp high)
                 (natp low)
                 (<= low high))
            (equal (< (slice high low x) k)
                   (< (bvchop (+ 1 high) x) (* k (expt 2 low)))))
   :hints (("Goal" :in-theory (e/d (<-of-floor-arg1 <-of-floor-arg2 slice logtail)
                                   (bvchop-of-logtail-becomes-slice
                                    equal-of-floor-of-expt-and-bv
                                    floor-becomes-slice-when-unsigned-byte-p))))))

(defthmd <-of-slice-arg1
  (implies (and (unsigned-byte-p (+ 1 high (- low)) k) ;move to conclusion?
                (natp high)
                (natp low)
                (<= low high))
           (equal (< (slice high low x) k)
                  (< (bvchop (+ 1 high) x) (* k (expt 2 low)))))
  :hints (("Goal" :use (:instance <-of-slice-arg1-helper (x (bvchop (+ 1 high) x))))))

;see also slice-when-not-bvlt-gen?
(defthm equal-of-constant-and-slice-when-bvlt
  (implies (and (syntaxp (quotep k))
                (not (bvlt size free x)) ;alt version?
                (syntaxp (quotep free))
                (equal size (+ 1 high))
                (bvlt (+ high 1 (- low)) (slice high low free) k) ;is this the best we can do?
                (natp high)
                (natp low)
                (<= low high)
                )
           (equal (equal k (slice high low x))
                  nil))
  :hints (("Goal" :in-theory (enable equal-of-slice bvlt <-of-slice-arg1 natp))))

(defthm slice-of-bvif-safe
  (implies (and (syntaxp (and (or (quotep a)
                                  (quotep b))
                              (quotep high)
                              (quotep low)
                              (quotep size)))
                (< high size)
                (<= low high)
                (natp size)
                (natp high)
                (natp low))
           (equal (slice high low (bvif size test a b))
                  (bvif (+ 1 high (- low)) ;;was just "size"
                        test (slice high low a)
                        (slice high low b))))
  :hints (("Goal" :in-theory (enable bvif myif natp))))

(local
 (defthmd bvchop-0-hack-helper
   (implies (and (unsigned-byte-p 6 x)
                 (bvlt '6 x free)
                 (bvlt 6 free 5)
                 (equal free2 (bvchop '2 x))
                 (equal 0 free2))
            (equal (bvchop '6 x)
                   0))
   :hints (("Goal" :in-theory (enable bvlt)))))

;gross?
(defthm bvchop-0-hack
  (implies (and ;(unsigned-byte-p 6 x)
                (bvlt '6 x free)
                (syntaxp (quotep free))
                (bvlt 6 free 5)
                (equal free2 (bvchop '2 x))
                (equal 0 free2) ;poor man's backchain limit
                )
           (equal (bvchop '6 x)
                  0))
  :hints (("Goal" :use (:instance bvchop-0-hack-helper (x (bvchop 6 x))))))



(defthm equal-of-firstn-and-firstn-same
  (implies (and (natp n1)
                (natp n2)
                (<= n1 (len x))
                (<= n2 (len x)))
           (equal (equal (firstn n1 x) (firstn n2 x))
                  (equal n1 n2))))

;ffixme what other bvop of myif rules are missing?
(defthm bvuminus-of-myif-arg2
  (equal (bvuminus size (myif test x y))
         (bvuminus size (bvif size test x y)))
  :hints (("Goal" :cases ((natp size))
           :in-theory (enable myif bvif))))

;gen
(defthm bv-array-read-of-unary-minus-32-2
  (implies (integerp index)
           (equal (bv-array-read '32 '2 (unary-- index) data)
                  (bv-array-read '32 '2 (getbit 0 index) data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read) (NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm <-cancel-only-and-2-of-more
  (equal (< x (+ y (+ x z)))
         (< 0 (+ y z))))

(defthm bitxor-when-equal-of-constant-and-bvchop-arg2
  (implies (and (equal free (bvchop size x))
                (syntaxp (and (quotep free)
                              (not (quotep x))))
                (posp size))
           (equal (bitxor y x)
                  (bitxor y free))))

(defthm bitxor-when-equal-of-constant-and-bvchop-arg1
  (implies (and (equal free (bvchop size x))
                (syntaxp (and (quotep free)
                              (not (quotep x))))
                (posp size))
           (equal (bitxor x y)
                  (bitxor free y))))

(defthm bvxor-cancel-2-of-more-and-1-of-more
  (equal (equal (bvxor size y (bvxor size x z)) (bvxor size x w))
         (equal (bvxor size y z) (bvchop size w))))



;gen!
(defthm	bvplus-of-bvuminus-of-bvcat-and-bvcat
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (bvle 4 k1 k2)
                ;(integerp k1)
                ;(integerp k2)
                )
           (equal (bvplus 30 (bvuminus 30 (bvcat 25 x 4 k1)) (bvcat 25 x 4 k2))
                  (bvminus 4 k2 k1)
                  ))
  :hints (("Goal" :in-theory (enable bvcat bvplus bvuminus bvminus logapp bvchop-of-sum-cases bvlt))))

(in-theory (disable unsigned-byte-p-of-plus-of-minus-1 unsigned-byte-p-of-plus-minus-4-gen-dag)) ;can unify with constants? or slow for some other reason

;(in-theory (disable mod-sum-cases))

(in-theory (disable SLICE-OF-NTH-BECOMES-BV-ARRAY-READ))

;why?
(in-theory (disable small-int-hack ;natp-when-integerp-cheap
                    natp-means-non-neg ;dangerous?
                    usb-plus-from-bounds
                    ;integerp-of-small
                    ;floor-bounded-by-/
                    bvlt-add-to-both-sides-constant-lemma-alt-no-split
                    ;collect-constants-over-<  ;remove?
                    ))

;gen
(defthm equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus
  (implies (and (natp n)
                (< n 31) ;the bvplus doesn't overflow
                (<= n (len data))
                (all-unsigned-byte-p 32 data))
           (equal (equal (bv-array-write '32 (bvplus 5 1 n) n '0 data) (repeat (bvplus 5 1 n) '0))
                  (equal (firstn n data) (repeat n '0))))
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-WRITE update-nth2 bvplus ceiling-of-lg equal-of-append repeat)
                                  (UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN equal-of-cons)))))

;gen
(defthm equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus-alt
  (implies (and (natp n)
                (< n 31) ;the bvplus doesn't overflow
                (<= n (len data))
                (all-unsigned-byte-p 32 data))
           (equal (equal (repeat (bvplus 5 1 n) '0) (bv-array-write '32 (bvplus 5 1 n) n '0 data))
                  (equal (firstn n data) (repeat n '0))))
  :hints (("Goal" :use (:instance equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus)
           :in-theory (disable equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus))))

(in-theory (disable ;LIST::OPEN-EQUIV
                    NTH-BECOMES-BV-ARRAY-READ-STRONG ;looped
                    ))

;gen
(defthm equal-of-constant-and-bv-array-write
  (implies (and (syntaxp (quotep k))
                (<= 16 (len data))
                (unsigned-byte-p 32 val)
                (all-unsigned-byte-p 32 data)
                (equal 17 (len k)))
           (equal (equal k (bv-array-write '32 '17 '16 val data))
                  (and (true-listp k)
                       (equal val (nth 16 k))
                       (equal (firstn 16 k) (firstn 16 data)))))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2 bvplus bv-array-read equal-of-append)
                                  (update-nth-becomes-update-nth2-extend-gen
                                   LEN-OF-CDR
                                   CDR-OF-TAKE
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm bv-array-clear-of-0-and-cons
  (implies (syntaxp (not (quotep a)))
           (equal (bv-array-clear size len 0 (cons a b))
                  (bv-array-clear size len 0 (cons 0 b))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-range-of-cons
  (implies (and (syntaxp (not (quotep a))) ;ffixme we really want to do it for anything but 0? add support for equal to make-axe-rules
                (< high len)
                (natp len)
                (natp high))
           (equal (bv-array-clear-range size len 0 high (cons a b))
                  (bv-array-clear-range size len 0 high (cons '0 b))))
  :hints (("Goal"
           :expand ((bv-array-clear-range size len 0 high (cons a b)))
           :in-theory (e/d (bv-array-clear-range subrange-of-cons) ()))))

(defthm bv-array-clear-range-of-cons-of-cons
  (implies (and (syntaxp (not (and (quotep a)
                                   (quotep b)))) ;ffixme we really want to do it for anything but 0? add support for equal to make-axe-rules
                (< high len)
                (natp len)
                (posp high) ;gen?
                )
           (equal (bv-array-clear-range width len 0 high (cons a (cons b c)))
                  (bv-array-clear-range width len 0 high (append '(0 0) c))))
  :hints (("Goal" :in-theory (enable subrange-of-cons))))

(defthm bv-array-clear-range-of-append-of-cons
  (implies (and (syntaxp (not (quotep b))) ;ffixme we really want to do it for anything but 0? add support for equal to make-axe-rules
                (syntaxp (quotep a))
                (<= (len a) high)
                (< high len)
                (natp high)
                (natp len))
           (equal (bv-array-clear-range width len 0 high (append a (cons b c)))
                  (bv-array-clear-range width len 0 high (append (append a '(0)) c))))
  :hints (("Goal" :in-theory (enable ;list::nth-of-cons
                              natp subrange-of-cons))))

;fixme gen the 0 (may not be true becuase of the clear)
(defthm equal-of-repeat-of-0-and-bv-array-write
  (implies (and (equal len (len data))
                (natp index)
                (< index len)
                (true-listp data)
                (all-unsigned-byte-p '32 data))
           (equal (equal (repeat len '0) (bv-array-write '32 len index val data))
                  (and (equal 0 (bvchop 32 val))
                       (equal (repeat len '0) (bv-array-clear '32 len index data)))))
  :hints (("Goal" :in-theory (e/d ( ;bv-array-clear bv-array-write
                                   bv-array-clear
                                   bv-array-write-opener
                                   update-nth2
                                   ) (bv-array-write-equal-rewrite-alt bv-array-write-equal-rewrite
                                   update-nth-becomes-update-nth2-extend-gen)))))

(defthm equal-of-repeat-and-bv-array-write-hack
  (implies (and (true-listp data)
                (unsigned-byte-p 5 x)
                (< x 31) ;no overflow
                (>= (len data) x)
                (all-unsigned-byte-p '32 data)
                )
           (equal (equal (repeat (bvplus 5 1 x) '0) (bv-array-write '32 (bvplus 5 1 x) x '0 data))
                  (equal (repeat x '0) (firstn x data))))
  :hints (("Goal" :in-theory (e/d (bv-array-write UPDATE-NTH2 bvplus ceiling-of-lg equal-of-append)
                                  (UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   equal-of-cons)))))

(defthm equal-of-repeat-and-bv-array-write-hack-alt
  (implies (and (true-listp data)
                (unsigned-byte-p 5 x)
                (< x 31) ;no overflow
                (>= (len data) x)
                (all-unsigned-byte-p '32 data)
                )
           (equal (equal (bv-array-write '32 (bvplus 5 1 x) x '0 data) (repeat (bvplus 5 1 x) '0))
                  (equal (repeat x '0) (firstn x data))))
  :hints (("Goal" :use (:instance equal-of-repeat-and-bv-array-write-hack)
           :in-theory (disable equal-of-repeat-and-bv-array-write-hack))))

(defthm bvlt-of-constant-when-unsigned-byte-p-tighter
  (implies (and (syntaxp (quotep k)) ;relax?
                (unsigned-byte-p freesize x)
                (syntaxp (quotep freesize))
                (syntaxp (quotep size))
                (<= (+ -1 (expt 2 freesize)) (bvchop size k))
                (natp size))
           (equal (bvlt size k x)
                  nil))
  :hints (("Goal" :in-theory (enable bvlt))))

;fixme more like this?!
(defthm boolor-of-booland-same-2
  (equal (boolor (booland x y) x)
         (bool-fix x)))

(defthm sha1-context-hack
  (equal (booland (not (equal '0 (bvchop '2 x)))
                  (not (bvlt '2 '1 x)))
         (equal 1 (bvchop 2 x)))
  :hints (("Goal" :in-theory (enable bvlt))))

;this may help us get x in the context!
(defthm booland-of-booland-of-boolif
  (equal (booland x (booland y (boolif x z w)))
         (booland x (booland y z)))
  :hints (("Goal" :in-theory (enable boolif booland))))

(defthm boolor-of-equal-and-not-of-equal-constants
  (implies (syntaxp (and (quotep k1)
                              (quotep k2)))
           (equal (boolor (equal k1 x) (not (equal k2 x)))
                  (if (equal k1 k2)
                      t
                    (not (equal k2 x))))))

(defthm boolor-of-equal-and-not-of-equal-constants-alt
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (boolor (not (equal k2 x)) (equal k1 x))
                  (if (equal k1 k2)
                      t
                    (not (equal k2 x))))))

;gen
(defthm bvplus-of-bvplus-of-bvuminus-of-bvcat
  (implies (unsigned-byte-p 31 i) ;limit?
           (equal (bvplus '32
                          i
                          (bvplus '32 y
                                  (bvuminus '32
                                            (bvcat '25
                                                   (slice '30 '6 i)
                                                   '6
                                                   '0))))
                  (bvplus '32
                          (bvchop 6 i) y))))

(defthm equal-of-myif-and-bvif-same
  (implies (natp size)
           (equal (equal (myif test x y) (bvif size test x y))
                  (myif test
                        (unsigned-byte-p size x)
                        (unsigned-byte-p size y))))
  :hints (("Goal" :in-theory (enable boolor myif))))

(defthm equal-of-myif-and-bvif-same-alt
  (implies (natp size)
           (equal (equal (bvif size test x y) (myif test x y))
                  (myif test
                        (unsigned-byte-p size x)
                        (unsigned-byte-p size y))))
  :hints (("Goal" :use (:instance equal-of-myif-and-bvif-same)
           :in-theory (disable equal-of-myif-and-bvif-same))))

;yuck?
(defthm equal-of-bv-array-read-and-bv-array-read-lens-differ
  (implies (and (< index len1)
                (< index len2)
                (natp len1)
                (natp len2)
                (natp index)
                )
           (equal (equal (bv-array-read width len1 index data) (bv-array-read width len2 index data))
                  t))
  :hints (("Goal" :cases ((< len1 len2))
           :in-theory (e/d (BV-ARRAY-READ-opener) (NTH-BECOMES-BV-ARRAY-READ2)))))

(defthm prefixp-of-bv-array-write-when-prefixp
  (implies (and (< (len x) len)
                (all-unsigned-byte-p 8 data)
                (prefixp x data)
                (natp len))
           (equal (prefixp x (bv-array-write '8 len (len x) val data))
                  t))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX
                           (size 8)
                           (lst x))
           :in-theory (e/d (bv-array-write ceiling-of-lg UPDATE-NTH2 PREFIXP-REWRITE-gen
                                           equal-of-true-list-fix-and-true-list-fix-forward)
                           (ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX
                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

(defthm bvlt-of-len-and-len-when-prefixp
  (implies (and (prefixp x free)
                (equal y free)
                (unsigned-byte-p size (len x))
                (unsigned-byte-p size (len y)))
           (equal (bvlt size (len y) (len x))
                  nil))
  :hints (("Goal" :in-theory (enable bvlt prefixp))))

;fixme not equal when < of lens

;gross
(defthm bvplus-of-bvplus-of-bvuminus-same-sizes-differ
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (BVPLUS '32 x (BVPLUS '31 (BVUMINUS '31 x) y))
                  (if (bvlt 31 y x)
                      (bvplus 32 2147483648 Y)
                    y)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases bvuminus bvminus bvlt))))

;same rhs as for 32?
(defthm bvplus-of-bvplus-of-bvuminus-same-sizes-differ2
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (BVPLUS '33 x (BVPLUS '31 (BVUMINUS '31 x) y))
                  (if (bvlt 31 y x)
                      (bvplus 32 2147483648 Y)
                    y)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases bvuminus bvminus bvlt))))

;move
;shouldn't this get commuted?
(defthm equal-of-+-of-minus-same
  (equal (+ (- x) x)
         0))

;move
(defthm equal-of-fix-same
  (equal (equal (fix x) x) ;fixme why didn't this get reordered in the rc4 proof?
         (acl2-numberp x)))

(defthm bvcat-of-slice-and-constant-when-equal-of-bvchop-and-constant
  (implies (and (syntaxp (quotep k1))
                (equal k2 (bvchop 7 x)))
           (equal (bvcat '25 (slice '30 '6 x) '6 k1)
                  (bvcat '24 (slice '30 '7 x)
                         '7
                         ;;this gets computed:
                         (bvcat 1 (getbit 6 k2)
                                6 k1)))))

;gen
(defthmd bvplus-of-bvplus-of-constant-and-short-expand-helper
  (IMPLIES (AND (< YSIZE 32)
                (NATP YSIZE)
                (unsigned-byte-p 32 K)
                (INTEGERP Y)
                (< (+ K (EXPT 2 YSIZE)) 1073741824)
                (UNSIGNED-BYTE-P-FORCED YSIZE Y))
           (BVLT 32 (BVPLUS 32 K Y) 1073741824))
  :hints (("Goal" :in-theory (enable bvlt bvplus bvchop-of-sum-cases UNSIGNED-BYTE-P-FORCED UNSIGNED-BYTE-P))))

(in-theory (disable BVLT-TIGHTEN-WHEN-GETBIT-0))

(defthm integerp-when-UNSIGNED-BYTE-P-FORCED-free
  (implies (UNSIGNED-BYTE-P-FORCED YSIZE Y)
           (integerp y))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P-FORCED))))


;gen!
;rename
(defthm sbvlt-of-bvplus-32
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep k2))
                (unsigned-byte-p 30 x) ; do better?
                (unsigned-byte-p 30 k) ;do better?
                (unsigned-byte-p 30 k2) ;do better..
                )
           (equal (sbvlt 32 k (bvplus 32 k2 x))
                  (sbvlt 32 (- k k2) x)))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases bvplus getbit-of-plus))))

;gen
(defthmd <-of-256
  (implies (natp x)
           (equal (< x 256)
                  (unsigned-byte-p 8 x))))

;gen!
(defthm slice-when-slice-known
  (implies (and (equal free (slice 5 2 x))
                (syntaxp (quotep free)))
           (equal (slice 30 2 x)
                  (bvcat 25 (slice 30 6 x)
                         4 free))))

;gen
(defthm equal-of-bvplus-and-+
  (implies (integerp x)
           (equal (equal (bvplus 32 1 x) (+ 1 x))
                  (and (<= -1 x)
                       (< X (+ -1 (expt 2 32)))
                       ))))

(defthm bvlt-when-equal-of-constant
  (implies (and (syntaxp (quotep free)) ;rename
                (equal k (slice high low x))
                (syntaxp (quotep k)) ;rename
                (equal size (+ 1 high))
                (bvlt (+ high 1 (- low)) (slice high low free) k) ;is this the best we can do?
                (natp high)
                (natp low)
                (<= low high)
                )
           (equal (bvlt size free x)
                  t))
  :hints (("Goal" :use (:instance EQUAL-OF-CONSTANT-AND-SLICE-WHEN-BVLT)
           :in-theory (disable EQUAL-OF-CONSTANT-AND-SLICE-WHEN-BVLT))))

;use polarity?
(defthm not-equal-of-max-when-huge
  (implies  (and (bvlt '2 free x)
                 (syntaxp (quotep free))
                 (equal 1 free) ;poor man's backchain limit..
                 )
            (equal (equal 'nil (equal '3 (bvchop '2 x))) ;commute?
                   (equal 2 (bvchop 2 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvplus-of-bvplus-32-1-31
  (implies (and (syntaxp (quotep k))
                (not (equal (bvuminus 31 (+ 1 k)) (bvchop 31 x)))
                (unsigned-byte-p 31 k))
           (equal (bvplus 32 1 (bvplus 31 k x))
                  (bvplus 31 (+ 1 k) x)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases bvlt boolor bvuminus bvminus))))

(defthm nth-of-add-to-end
  (implies (natp n)
           (equal (nth n (add-to-end item lst))
                  (if (> n (len lst))
                      nil
                    (if (< n (len lst))
                        (nth n lst)
                      item))))
  :hints (("Goal" ; :induct t
           :in-theory (enable add-to-end ;LIST::NTH-WITH-LARGE-INDEX
                              ))))

(defthm equal-of-firstn-same
  (equal (equal x (firstn n x))
         (and (true-listp x)
              (<= (len x) (nfix n))))
  :hints (("Goal" :in-theory (enable firstn))))

;gen!
(defthm sbvmoddown-of-bvplus-of-minus-4
  (equal (sbvmoddown '32 (bvplus '32 '4294967292 x) '4)
         (sbvmoddown '32 x '4))
  :hints (("Goal" :in-theory (enable sbvmoddown MOD-OF-EXPT-OF-2-CONSTANT-VERSION))))


;fixme or go to myif
(defthm if-x-x-nil
  (implies (booleanp x)
           (equal (if x x nil)
                  x))
  :rule-classes nil)

(defthm bv-array-clear-range-of-bv-array-write-too-high
  (implies (and (< high index)
                (< index len)
                (< high len)
                (<= alow high) ;"alow" comes alphabetically first
                (equal len (len data))
                (natp len)
                (natp alow)
                (natp high)
                (natp size)
                (natp index))
           (equal (bv-array-clear-range size len alow high (bv-array-write size len index val data))
                  (bv-array-write size len index val (bv-array-clear-range size len alow high data))))
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-CLEAR-RANGE) (BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE ;looped
;                                                          BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF
                                                          )))))


(defthmd array-write-of-0
  (equal (bv-array-write elem-size len index1 0 lst)
         (bv-array-clear elem-size len index1 lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))


(DEFTHM BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-write-of-0-ADJACENT1
  (IMPLIES (AND (EQUAL LOWINDEX (+ 1 INDEX1))
                (< INDEX1 LEN)
                (< LOWINDEX LEN)
                (< HIGHINDEX LEN)
                (<= LOWINDEX HIGHINDEX)
                (NATP ELEM-SIZE)
                (NATP LEN)
                (NATP INDEX1)
                (NATP LOWINDEX)
                (NATP HIGHINDEX))
           (EQUAL
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX HIGHINDEX (BV-ARRAY-write ELEM-SIZE LEN INDEX1 0 LST))
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX1 HIGHINDEX LST)))
  :hints (("Goal" :in-theory (enable ARRAY-WRITE-of-0))))

(DEFTHM BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-write-of-0-ADJACENT2
  (IMPLIES (AND (EQUAL INDEX1 (+ 1 HIGHINDEX))
                (< INDEX1 LEN)
                (< LOWINDEX LEN)
                (< HIGHINDEX LEN)
                (<= LOWINDEX HIGHINDEX)
                (NATP ELEM-SIZE)
                (NATP LEN)
                (NATP INDEX1)
                (NATP LOWINDEX)
                (NATP HIGHINDEX))
           (EQUAL
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX HIGHINDEX (BV-ARRAY-write ELEM-SIZE LEN INDEX1 0 LST))
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX INDEX1 LST)))
  :hints (("Goal" :in-theory (enable ARRAY-WRITE-of-0))))

;move
(defthm subrange-of-repeat
  (implies (and (< end n)
;                (<= start end)
                (natp start)
                (natp end)
                (natp n))
           (equal (subrange start end (repeat n x))
                  (repeat (+ 1 (- end start)) x)))
  :hints (("Goal" :in-theory (e/d (subrange repeat)
                                  (;anti-subrange
                                   )))))

(theory-invariant (incompatible (:rewrite equal-of-repeat-of-len-same) (:rewrite all-equal$-when-true-listp)))

;gen!
(defthm bv-array-clear-range-of-append-one-more
  (implies (and (syntaxp (quotep z))
                (equal z (repeat (len z) 0))
                (< index (+ -1 (len z))) ;to prevent loops
                (< (len z) len)
                (natp index)
                (natp len)
                )
           (equal (bv-array-clear-range 32 len 0 index (binary-append z x))
                  (bv-array-clear-range 32 len 0 (+ -1 (len z)) (binary-append z x))))
  :hints (("Goal" :in-theory (e/d (equal-of-append) (EQUAL-OF-REPEAT-OF-LEN-SAME)))))

(defthm first-hack-for-sha1
  (equal (firstn (+ (BVCAT 25 (SLICE 30 6 x) 4 0) (- (SLICE 30 2 x))) y)
         nil))



;Mon Jul 19 21:10:23 2010
;why does the update-nth2 arise?
;; (defthm bv-array-clear-of-update-nth2-same
;;   (equal (bv-array-clear size len index (update-nth2 len index val lst))
;;          (bv-array-clear size len index lst))
;;   :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-read-of-update-nth2-same
  (implies (and (natp len)
                (< index len)
                (natp index))
           (equal (bv-array-read size len index (update-nth2 len index val lst))
                  (bvchop size val)))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-read-opener update-nth2) (update-nth-becomes-update-nth2-extend-gen
                                                                                     NTH-BECOMES-BV-ARRAY-READ2)))))







;gen the 0!
(defthm sbvlt-of-bvplus-of-constant
  (implies (and (syntaxp (quotep k))
                (< (expt 2 31) k) ;k is a "negative" constant
                (not (equal (bvchop 31 k) 0)) ;drop
                (sbvle 32 (- (expt 2 31) k) x) ;holds of any x that's a usb 31...
                (unsigned-byte-p 32 k) ;drop
                )
           (equal (sbvlt 32 (bvplus 32 k x) 0)
                  (sbvlt 32 x (- k))))
  :hints (("Goal" :cases ((equal x -1))
           :in-theory (e/d (bvplus bvlt getbit-of-plus)
                                  (EQUAL-OF-BVCHOP-EXTEND ;looped
                                   )))))

(defthm sbvlt-of-bvplus-of-constant-minus-1
  (implies (and (syntaxp (quotep k))
                (< (expt 2 31) k)              ;k is a "negative" constant
                (not (equal (bvchop 31 k) 0)) ;drop
                (sbvle 32 (- (expt 2 31) k) x) ;holds of any x that's a usb 31...
                (unsigned-byte-p 32 k)         ;drop
                )
           (equal (sbvlt 32 4294967295 (bvplus 32 k x))
                  (not (sbvlt 32 x (- k)))))
  :hints (("Goal" :cases ((equal x -1))
           :in-theory (e/d (bvplus bvlt getbit-of-plus)
                           (EQUAL-OF-BVCHOP-EXTEND ;looped
                            )))))

(defthm sbvlt-of-negative-constant-when-unsigned-byte-p
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal size 32) ;(posp size) ;gen!
                (< (expt 2 (+ -1 size)) k) ;gets computed - use sbvlt?
                (unsigned-byte-p size k) ;drop?
                (unsigned-byte-p 31 x) ;could this be slow?
                )
           (equal (sbvlt size x k)
                  nil)))

;; ;drop?
;; (defthm sbvlt-transitive-hack
;;   (implies (not (sbvlt '32 x '#.|*minus-1*|))
;;            (equal (sbvlt '32 x '2147483651)
;;                   nil)))

;gen this series!
;use polarities?
(defthm sbvlt-when-sbvmoddown-hack
  (implies (equal 3 (sbvmoddown 32 x 4))
           (equal (sbvlt 32 x 3)
                  (not (sbvlt 32 -1 x))))
  :hints (("Goal"
           :use (:instance <-of-bvchop-and-bvchop-same (s1 2) (s2 31))
           :in-theory (e/d (sbvmoddown bvlt) (<-of-bvchop-and-bvchop-same rewrite-<-when-sizes-dont-match)))))

(defthm sbvlt-when-sbvmoddown-hack2
  (implies (equal 3 (sbvmoddown 32 x 4))
           (equal (sbvlt 32 x 2)
                  (not (sbvlt 32 -1 x))))
  :hints (("Goal"
           :use (:instance <-of-bvchop-and-bvchop-same (s1 2) (s2 31))
           :in-theory (e/d (sbvmoddown bvlt) (<-of-bvchop-and-bvchop-same rewrite-<-when-sizes-dont-match)))))

(defthmd sbvlt-when-sbvmoddown-hack3
  (implies (equal 3 (sbvmoddown 32 x 4))
           (equal (sbvlt 32 x 1)
                  (not (sbvlt 32 -1 x))))
  :hints (("Goal"
           :use (:instance <-of-bvchop-and-bvchop-same (s1 2) (s2 31))
           :in-theory (e/d (sbvmoddown bvlt) (<-of-bvchop-and-bvchop-same rewrite-<-when-sizes-dont-match)))))

;todo: use polarities:
(defthmd sbvlt-when-sbvmoddown-hack4
;  (implies t;(equal 3 (sbvmoddown 32 x 4)) ;not needed?
           (equal (sbvlt 32 x 0)
                  (not (sbvlt 32 -1 x)))
           ;)
  :hints (("Goal"
           :use (:instance <-of-bvchop-and-bvchop-same (s1 2) (s2 31))
           :in-theory (e/d (sbvmoddown bvlt) (<-of-bvchop-and-bvchop-same rewrite-<-when-sizes-dont-match)))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-alt
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size)
                (natp k1))
           (equal (boolor (not (sbvlt size k1 x))
                          (sbvlt size x k2))
                  (if (sbvlt size k1 k2) ;gets computed
                      (sbvlt size x k2)
                    (not (sbvlt size k1 x)))))
  :hints (("Goal" :in-theory (enable sbvlt bvchop-of-sum-cases))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-alt2
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size)
                (natp k1))
           (equal (boolor (sbvlt size x k2)
                          (not (sbvlt size k1 x)))
                  (if (sbvlt size k1 k2) ;gets computed
                      (sbvlt size x k2)
                    (not (sbvlt size k1 x)))))
  :hints (("Goal" :in-theory (enable sbvlt bvchop-of-sum-cases))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-alt3
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (posp size)
                (natp x)
                (natp k1))
           (equal (boolor (not (sbvlt size k2 x))
                          (not (sbvlt size k1 x)))
                  (if (sbvle size k1 k2) ;gets computed
                      (not (sbvlt size k2 x))
                    (not (sbvlt size k1 x)))))
  :hints (("Goal" :in-theory (enable bvlt sbvlt bvchop-of-sum-cases))))


(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2-alt
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (sbvlt size k1 x)
                          (not (sbvlt size x k2)))
                  (if (sbvle size k2 k1) ;gets computed
                      (not (sbvlt size x k2))
                    (sbvlt size k1 x))))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2-alt2
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (not (sbvlt size x k2))
                          (sbvlt size k1 x))
                  (if (sbvle size k2 k1) ;gets computed
                      (not (sbvlt size x k2))
                    (sbvlt size k1 x))))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm boolor-of-sbvlt-of-constant-and-sbvlt-of-constant-2-alt3
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (not (sbvlt size x k2))
                          (not (sbvlt size x k1)))
                  (if (sbvle size k2 k1) ;gets computed
                      (not (sbvlt size x k2))
                    (not (sbvlt size x k1)))))
  :hints (("Goal" :in-theory (enable sbvlt))))

;gen!
(defthm <-of-ones-and-bvchop
  (equal (< 2147483647 (bvchop 32 x))
         (equal 1 (getbit 31 x)))
  :hints (("Goal" :in-theory (e/d ( ;getbit
                                   bvchop-when-top-bit-1-cheap
                                   ) ( slice-becomes-getbit bvchop-1-becomes-getbit)))))

;slow
;TODO: Speed this up
;can add to both sides when neither value rolls over:
(defthmd sbvlt-add-to-both-sides-1
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (bvle 32 k (bvminus 32 (+ -1 (expt 2 31)) x))
                (bvle 32 k (bvminus 32 (+ -1 (expt 2 31)) y))
                )
           (equal (sbvlt 32 x y)
                  (sbvlt 32 (bvplus 32 x k) (bvplus 32 y k))))
  :hints (("Goal" :cases ((equal 0 (getbit 31 k)))
           :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases bvminus BVCHOP-WHEN-TOP-BIT-1-CHEAP getbit-of-plus)
                           (GETBIT-WHEN-BVLT-OF-SMALL-HELPER
                            ;BVCHOP-OF-IF
                            ;BVPLUS-SUBST-VALUE
                            ;BVCHOP-WHEN-TOP-BIT-1-CHEAP
                            SHA1-LEMMA-0)))))

;slow
;TODO: Speed this up
;can add to both sides when both sides roll over:
(defthmd sbvlt-add-to-both-sides-2
  (implies (and (integerp x)
                (integerp y)
                (integerp k)
                (bvlt 32 (bvminus 32 (+ -1 (expt 2 31)) x) k)
                (bvlt 32 (bvminus 32 (+ -1 (expt 2 31)) y) k)
                )
           (equal (sbvlt 32 x y)
                  (sbvlt 32 (bvplus 32 x k) (bvplus 32 y k))))
  :hints (("Goal"
           :cases ((equal 0 (getbit 31 k)))
           :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases bvminus  getbit-of-plus
                                 bvchop-when-top-bit-1-cheap
                                 <-OF-IF-ARG1)
                           ;some of these are for speed
                           (;<-OF-IF-ARG1
;                            IF-BACKCHAIN-RULE
 ;                           IF-BACKCHAIN-RULE2
                            BVCHOP-CHOP-LEADING-CONSTANT
                            GETBIT-WHEN-BVLT-OF-SMALL-HELPER
                            BVPLUS-OF-0
                            BVPLUS-SUBST-VALUE
                            BVCHOP-OF-IF)))))

;either both roll over or neither do
(defthmd sbvlt-add-to-both-sides
  (implies (or (and (bvle 32 k (bvminus 32 (+ -1 (expt 2 31)) x))
                    (bvle 32 k (bvminus 32 (+ -1 (expt 2 31)) y)))
               (and (bvlt 32 (bvminus 32 (+ -1 (expt 2 31)) x) k)
                    (bvlt 32 (bvminus 32 (+ -1 (expt 2 31)) y) k)))
           (equal (sbvlt 32 x y)
                  (sbvlt 32 (bvplus 32 x k) (bvplus 32 y k))))
  :hints (("Goal" :in-theory (disable equal-of-bvchop-extend sbvlt-rewrite)
           :use ((:instance sbvlt-add-to-both-sides-1 (x (ifix x)) (y (ifix y)) (k (ifix k)))
                 (:instance sbvlt-add-to-both-sides-2 (x (ifix x)) (y (ifix y)) (k (ifix k)))))))

;or should we just go to bvplus?
(defthm bvlt-of-+-of-constant-trim-arg2
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)
                              (not (quotep x)) ;defeats acl2's over-aggressive matching
                              ))
                (not (unsigned-byte-p size k))
                (integerp x)
                (integerp k)
                (natp size))
           (equal (bvlt size (+ k x) y)
                  (bvlt size (+ (bvchop size k) x) y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;or should we just go to bvplus?
(defthm bvlt-of-+-of-constant-trim-arg3
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)
                              (not (quotep x)) ;defeats acl2's over-aggressive matching
                              ))
                (not (unsigned-byte-p size k))
                (integerp x)
                (integerp k)
                (natp size))
           (equal (bvlt size y (+ k x))
                  (bvlt size y (+ (bvchop size k) x))))
  :hints (("Goal" :in-theory (enable bvlt))))

;gen
;or should we just go to bvplus?
(defthm bvplus-of-+-of-4294967296-arg2
  (implies (and (syntaxp (not (quotep y))) ;defeats acl2's over-aggressive matching
                (integerp y))
           (equal (bvplus 32 x (+ 4294967296 y))
                  (bvplus 32 x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm sbvlt-add-to-both-sides-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep y)))
                (bvle 32 (- k) (bvminus 32 (+ -1 (expt 2 31)) (bvplus 32 k x))) ;fixme simplify?
                (bvle 32 (- k) (bvminus 32 (+ -1 (expt 2 31)) y)) ;gets computed
                (integerp x)
                (integerp y)
                (integerp k))
           (equal (sbvlt 32 (bvplus 32 k x) y)
                  (sbvlt 32 x (bvplus 32 y (- k)))))

  :hints (("Goal" :in-theory (e/d (BVPLUS-OF-UNARY-MINUS BVPLUS-OF-UNARY-MINUS-arg2)
                                  (sbvlt-add-to-both-sides-1 sbvlt-rewrite))
           :use (:instance sbvlt-add-to-both-sides-1
                           (k (- (expt 2 32) k))
                           (x (bvplus 32 k x))))))

(defthm bvminus-of-constant-and-bvplus-of-constant
  (implies (and (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
                (natp size))
           (equal (bvminus size k1 (bvplus size k2 x))
                  (bvminus size
                           (bvminus size k1 k2) ;gets computed
                           x)))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-of-sum-cases))))

(defthm bvlt-of-two-less-than-max-when-not-max
  (implies (not (equal 3 (bvchop 2 x)))
           (equal (bvlt 2 1 x)
                  (equal 2 (bvchop 2 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

;gen
(defthm bvplus-of-bvcat-and-bvuminus-of-bvcat
  (implies (<= (bvchop 6 k1) (bvchop 6 k2))
           (equal (bvplus 31 (bvcat 25 x 6 k2) (bvuminus 31 (bvcat 25 x 6 k1)))
                  (bvminus 6 k2 k1)))
  :hints (("Goal" :in-theory (enable SLICE-OF-BVPLUS-CASES bvminus bvplus bvuminus bvchop-of-sum-cases bvcat logapp))))

(defthm bv-array-clear-length-1-of-list-zero
  (equal (bv-array-clear width 1 index '(0))
         '(0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthmd repeat-of-one-more
  (implies (and (syntaxp (not (quotep n)))
                (natp n))
           (equal (repeat (+ 1 n) val)
                  (cons val (repeat n val)))))

(defthm car-of-bv-array-clear
  (equal (car (bv-array-clear width len index data))
         (if (posp len)
             (if (zp (bvchop (ceiling-of-lg (nfix len)) index))
                 0
               (bvchop width (car data)))
           nil))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm car-of-bv-array-clear-range
  (implies (and (natp high)
                (natp low)
                (<= low high) ;Mon Jul 19 21:20:04 2010
                (< high len) ;Mon Jul 19 21:20:04 2010
                (posp len))
           (equal (car (bv-array-clear-range width len low high data))
                  (if (zp low)
                      0
                    (bvchop width (car data)))))
  :hints (("Goal"
           :in-theory (e/d (bv-array-clear-range
                            subrange-of-cons)
                                  ( ;list::equal-append-reduction!
                                   cons-onto-repeat
                                   )))))


(defthm cdr-of-bv-array-clear
  (implies (and (posp len)
                (< index len) ;Mon Jul 19 21:20:04 2010
                (natp index))
           (equal (cdr (bv-array-clear width len index data))
                  (if (zp index)
                      (bvchop-list width (SUBRANGE 1 (+ -1 LEN) DATA))
                    (bv-array-clear width (+ -1 len) (+ -1 index) (cdr data)))))
  :hints (("Goal"
           :cases ((< len 2))
           :in-theory (e/d (bv-array-clear bv-array-write-opener update-nth2)
                                  (GETBIT-OF-BV-ARRAY-READ-HELPER ;yuck
                                   ;LIST::UPDATE-NTH-EQUAL-REWRITE-ALT
                                   update-nth-becomes-update-nth2-extend-gen)))))

(defthm cdr-of-bv-array-clear-range
  (implies (and (natp high)
                (natp width)
                (<= low high) ;Mon Jul 19 21:20:04 2010
                (< high len) ;Mon Jul 19 21:20:04 2010
                (equal len (len data)) ;Mon Jul 19 21:40:02 2010
                (natp low) ;gen?
                (posp len))
           (equal (cdr (bv-array-clear-range width len low high data))
                  (if (zp low)
                      (bv-array-clear-range width (+ -1 len) 0 (+ -1 high) (cdr data))
                    (bv-array-clear-range width (+ -1 len) (+ -1 low) (+ -1 high) (cdr data)))))
  :hints (("subgoal *1/2" :cases ((< HIGH (BINARY-+ '2 LOW))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (BV-ARRAY-CLEAR-RANGE WIDTH LEN LOW HIGH DATA)
           :in-theory (e/d (bv-array-clear-range subrange-of-cons consp-of-cdr equal-of-append)
                                  ( ;list::equal-append-reduction!
                                   cons-onto-repeat
                                   ;LIST::LEN-POS-REWRITE
                                   )))))

(defthm bv-array-clear-range-of-1-and-cons-of-0
  (implies (and (<= 1 high)
                (< high len)
                (posp len)
                (equal len (+ 1 (len data)))
                (natp high)
                (natp width))
           (equal (bv-array-clear-range width len 1 high (cons '0 data))
                  (bv-array-clear-range width len 0 high (cons '0 data))))
  :hints (("Goal" ;:expand ((bv-array-clear-range width len 1 high (cons 0 data)))
           :in-theory (e/d (bv-array-clear-range subrange-of-cons subrange cdr-take-plus-1 repeat-of-one-more)
                           ( ;list::equal-append-reduction!
                            cons-onto-repeat
                            nthcdr-of-take-becomes-subrange
                            cdr-of-take-becomes-subrange-better
                            take-of-nthcdr-becomes-subrange
                            take-of-cdr-becomes-subrange ;looped and no theory invar
                            )))))

(defthm bvchop-identity-when-<
  (implies (and (< x free)
                (syntaxp (and (quotep free)
                              (quotep n)))
                (<= free (expt 2 n)) ;gets computed
                (natp n)
                (natp x)
                )
           (equal (bvchop n x)
                  x))
  :hints (("Goal" :use (:instance unsigned-byte-p-from-bound-constant-version)
           :in-theory (disable unsigned-byte-p-from-bound-constant-version))))



;gen?
;scary?
(defthm <-of-constant-becomes-bvlt
  (implies (natp x)
           (equal (< x 80)
                  (and (bvlt 7 x 80) (unsigned-byte-p 7 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm sbvlt-of-constant-when-<-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (< x free)
                (syntaxp (quotep free))
                (<= free (+ 1 k))                 ;gets computed
                (unsigned-byte-p (+ -1 size) free) ;gets computed
                (unsigned-byte-p (+ -1 size) k)    ;gets computed
                (natp x)
                (posp size))
           (equal (sbvlt size k x)
                  nil))
  :hints (("Goal" :in-theory (enable bvlt))))

(DEFTHM BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-WRITE-TOO-low
  (IMPLIES (AND (< INDEX alow)
                (< INDEX LEN)
                (< HIGH LEN)
                (<= ALOW HIGH)
                (EQUAL LEN (LEN DATA))
                (NATP LEN)
                (NATP ALOW)
                (NATP HIGH)
                (NATP SIZE)
                (NATP INDEX))
           (EQUAL (BV-ARRAY-CLEAR-RANGE SIZE LEN ALOW HIGH (BV-ARRAY-WRITE SIZE LEN INDEX VAL DATA))
                  (BV-ARRAY-WRITE SIZE LEN INDEX VAL (BV-ARRAY-CLEAR-RANGE SIZE LEN ALOW HIGH DATA))))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BV-ARRAY-CLEAR-RANGE)
                    (BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE)))))

(defthm bv-array-clear-range-of-bv-array-write-both
  (implies (and (< high len)
                (equal len (len data))
                (natp len)
                (natp low)
                (natp high)
                (natp size)
                (<= low high)
                (< index (len data))
                (natp index))
           (equal (bv-array-clear-range size len low high (bv-array-write size len index val data))
                  (if (and (<= low index)
                           (<= index high))
                      (bv-array-clear-range size len low high data)
                    (bv-array-write size len index val (bv-array-clear-range size len low high data)))))
  :hints (("Goal" :in-theory (disable BV-ARRAY-WRITE-EQUAL-REWRITE-ALT BV-ARRAY-WRITE-EQUAL-REWRITE))))

;gen?
;seemed to cause loops without the syntaxps
(defthm bvchop-when-must-be-1
  (implies (and (not (bvlt n free x))
                (syntaxp (quotep free))
                (equal free 1)
                (not (equal free2 (bvchop n x)))
                (syntaxp (quotep free2))
                (equal free2 0)
                (natp n)
                )
           (equal (bvchop n x)
                  1))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm <-of-constant-and-+-of-constant
  (implies (syntaxp (and (quotep k1) (quotep k2)))
           (equal (< k1 (+ k2 X))
                  (< (- k1 k2) x))))

(defthm <-of-constant-when-usb
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (unsigned-byte-p free x))
           (not (< x k))))

(defthm <-of-constant-when-usb2
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (unsigned-byte-p free x))
           (< k x)))

(defthmd sbvlt-add-to-both-sides-1-lemm
  (implies (and (integerp x)
                (integerp k)
                (bvle 32 (- k2) (bvminus 32 (+ -1 (expt 2 31)) (bvplus 32 k2 x)))
                (bvle 32 (- k2) (bvminus 32 (+ -1 (expt 2 31)) k))
                )
           (equal (sbvlt 32 (bvplus 32 k2 x) k)
                  (sbvlt 32 (bvplus 32 (bvplus 32 k2 x) (- k2)) (bvplus 32 k (- k2)))))
  :hints (("Goal" :use (:instance sbvlt-add-to-both-sides-1 (k (- k2)) (y k) (x (bvplus 32 k2 x)))
           :in-theory (disable sbvlt-add-to-both-sides-1))))

(defthmd sbvlt-add-to-both-sides-1-lemmb-helper
  (implies (and (unsigned-byte-p 31 x)
                (bvle 32 (expt 2 31) k2))
           (bvle 32 (- k2) (bvminus 32 (+ -1 (expt 2 31)) (bvplus 32 k2 x)))
           )
  :hints (("Goal"
           :cases ((< x 0))
           :in-theory (enable bvlt bvminus bvplus bvle bvchop-of-sum-cases))))

(defthmd sbvlt-of-bvplus-of-constant-and-constant
  (implies (and (syntaxp (and (quotep k) (quotep k2)))
                (integerp k)
                (unsigned-byte-p 31 x)
                (integerp k2)
                (bvle 32 (expt 2 31) k2) ;gets computed (yikes! this requires k2 to be huge (basically negative)
                (bvle 32 (- k2) (bvminus 32 (+ -1 (expt 2 31)) k)) ;gets computed
                )
           (equal (sbvlt 32 (bvplus 32 k2 x) k)
                  (sbvlt 32 x (bvplus 32 k (- k2)))))
  :hints (("Goal" :in-theory (e/d (BVPLUS-OF-UNARY-MINUS BVPLUS-OF-UNARY-MINUS-arg2)
                                  (sbvlt-rewrite))
           :use ((:instance sbvlt-add-to-both-sides-1-lemm)
                 (:instance sbvlt-add-to-both-sides-1-lemmb-helper)))))

(defthm sbvlt-of-negative-constant-when-unsigned-byte-p-2
  (implies (and (syntaxp (quotep k)) ;make a bind-free version?
                (sbvlt 32 k 0)
                (unsigned-byte-p free x)
                (<= free 31))
           (equal (sbvlt 32 k x)
                  t)))

(defthm booland-of-bvlt-of-constant-and-bvle-of-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size))
           (equal (booland (not (bvlt size x k1)) (not (bvlt size x k2)))
                  (not (bvlt size x (max (bvchop size k1) (bvchop size k2))))))
  :hints (("Goal" :in-theory (enable bvlt))))


(defthm unsigned-byte-p-when-bvlt
  (implies (and (bvlt freesize x y)
                (<= xsize freesize)
                (unsigned-byte-p ysize y)
                (<= ysize xsize)
                (unsigned-byte-p xsize3 x)
                (equal xsize3 freesize) ;allow <
                )
           (equal (unsigned-byte-p xsize x)
                  (natp xsize)))
  :hints (("Goal" :in-theory (enable bvlt ))))

;; (defthm unsigned-byte-p-when-bvle
;;   (implies (and (not (bvlt freesize y x))
;;                 (<= xsize freesize)
;;                 (unsigned-byte-p ysize y)
;;                 (<= ysize xsize)
;;                 (unsigned-byte-p xsize3 x)
;;                 (= xsize3 freesize) ;allow <
;;                 )
;;            (equal (unsigned-byte-p xsize x)
;;                   (natp xsize)))
;;   :hints (("Goal" :in-theory (enable bvlt ))))

;; (defthm unsigned-byte-p-when-bvlt2
;;   (implies (and (bvlt freesize x y)
;;                 (<= xsize freesize)
;;                 (unsigned-byte-p ysize y)
;;                 (<= ysize xsize)
;;                 (unsigned-byte-p xsize3 x)
;;                 (<= xsize3 freesize) ;allow <
;;                 )
;;            (equal (unsigned-byte-p xsize x)
;;                   (natp xsize)))
;;   :hints (("Goal" :use (:instance unsigned-byte-p-when-bvlt)
;;            :in-theory (disable unsigned-byte-p-when-bvlt))))



;fixme add -1 version?
;looped when used by acl2?
(defthmd <-of-constant-when-natp-2
  (implies (and (syntaxp (quotep k))
                (posp k) ;if we allowed 0 this could loop when relieving the natp hyp (if it opens the natp)
                (natp x) ;i've seen this be expensive to relieve (when x is a RV of a loop function, so axe must establish all the function's preconditions)
                )
           (equal (< x k)
                  (and (unsigned-byte-p (integer-length k) x)
                       (bvlt (integer-length k) x k))))
  :hints (("Goal" :in-theory (e/d (bvlt UNSIGNED-BYTE-P) (integer-length)))))

(defthm bv-array-clear-of-bv-array-write-both
  (implies (and (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (if (equal key1 key2)
                      (bv-array-clear esize len key1 lst)
                    (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst)))))
  )


;gen!
(defthm times-of-64-becomes-bvmult
 (implies (unsigned-byte-p free x)
          (equal (* 64 x)
                 (bvmult (+ 6 free) 64 x))))

;gen the 31
(defthm unsigned-byte-p-shrink
  (implies (and (bvlt 31 x y)
                (unsigned-byte-p free y)
                (< free 31)
                (natp free)
                )
           (equal (unsigned-byte-p 31 x)
                  (unsigned-byte-p free x))))

;rename
;yuck?
(defthmd bvlt-of-33554432 ;gen!
  (implies (and (BVLT '31 x free)
                (syntaxp (quotep free)) ;Fri Oct 22 01:59:06 2010
                (equal '33554432 free))
           (equal (unsigned-byte-p 31 x)
                  (unsigned-byte-p 25 x)))
  :hints (("Goal" :in-theory (enable bvlt))))

(DEFTHM GETBIT-OF-EXPT-too-high
  (IMPLIES (AND (< m n)
                (INTEGERP m)
                (NATP n))
           (EQUAL (GETBIT n (EXPT 2 m))
                  0))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (GETBIT SLICE)
                    (BVCHOP-1-BECOMES-GETBIT
                     SLICE-BECOMES-GETBIT ANTI-SLICE)))))



;gen!
(defthmd bvlt-of-64
  (implies (and (unsigned-byte-p free x)
                (syntaxp (quotep free))
                (equal 7 free))
           (equal (bvlt '7 x '64)
                  (equal 0 (getbit 6 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm equal-of-0-and-bvchop-6
  (implies (and (not (equal free (getbit 6 x))) ;polarities could be used on this fact
                (syntaxp (quotep free))
                (equal 0 free))
           (equal (equal 0 (bvchop 6 x))
                  (equal 64 (bvchop 7 x)))))



(defthm move-minus-hack
  (implies (acl2-numberp w)
           (equal (equal w (+ x (+ y (- z))))
                  (equal (+ z w) (+ x y)))))

(defthm move-minus-hack2
  (implies (acl2-numberp w)
           (equal (< (+ x (+ y (- z))) w)
                  (< (+ x y) (+ z w)))))

(defthm equal-of-nil-when-equal-of-len
  (implies (and (equal free (len x))
                (syntaxp (quotep free))
                (< 0 free))
           (equal (equal nil x)
                  nil)))



(defthm bvlt-of-2-and-2
  (equal (BVLT '2 x '2)
         (equal 0 (getbit 1 x)))
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x)))
           :in-theory (e/d (bvlt getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT
                                                               EQUAL-OF-BVCHOP-EXTEND)))))


;gen
(defthm bvcat-when-top-bit-0
  (implies (and (equal '0 (getbit free x))
                (equal free 1))
           (equal (bvcat '2 x '3 y)
                  (bvcat '1 x '3 y))))

;gen
(defthm bvcat-when-top-bit-0-2
  (implies (and (not (equal freek (getbit 0 x)))
                (equal 0 freek))
           (equal (bvcat '1 x '3 y)
                  (bvcat '1 1 '3 y))))

;; (thm
;;  (implies (and (signed-byte-p 27 z)
;;                (equal 1 (getbit 26 z)))
;;           (equal (bvchop 26 z)
;;                  (+ (- (expt 2 26)) z)))
;;  :hints (("Goal" :cases ((< z 0))
;;           :in-theory (enable ;signed-byte-p
;;                       ))))

;gen the sizes! and the -1
(defthmd <-of-+-of-minus
  (implies (and (unsigned-byte-p 26 x)
                (unsigned-byte-p 26 y)
                ;(signed-byte-p 27 z)
                (equal -1 z) ;gen!
                )
           (equal (< (+ (- x) y) z)
                  (sbvlt 27 (bvminus 27 y x) z)))
  :hints (("Goal" :in-theory (enable bvlt sbvlt bvminus bvplus bvchop-of-sum-cases getbit-of-plus))))

;gen the sizes! and the -1
(defthmd <-of-+-of-minus-alt
  (implies (and (unsigned-byte-p 26 x)
                (unsigned-byte-p 26 y)
                ;(signed-byte-p 27 z)
                (equal -1 z) ;gen!
                )
           (equal (< (+ y (- x)) z)
                  (sbvlt 27 (bvminus 27 y x) z)))
  :hints (("Goal" :use (:instance <-of-+-of-minus)
           :in-theory (disable <-of-+-of-minus))))

;gen!
;use bind-free and free vars - way to combine those two?  augment the bind free code to use assumptions?
(defthm equal-of-+-of-minus
  (implies (and (syntaxp (quotep z))
                (< z 0)
                (unsigned-byte-p 26 x)
                (unsigned-byte-p 26 y)
                (unsigned-byte-p 26 (- z)))
           (equal (equal z (+ (- x) y))
                  (equal (- z) (bvminus 27 x y))))
  :hints (("Goal" :in-theory (enable bvlt sbvlt bvminus bvplus bvchop-of-sum-cases))))

(defthm equal-of-+-of-minus-alt
  (implies (and (syntaxp (quotep z))
                (< z 0)
                (unsigned-byte-p 26 x) ;use axe-bind-free or look for free vars
                (unsigned-byte-p 26 y) ;use axe-bind-free or look for free vars
                (unsigned-byte-p 26 (- z)))
           (equal (equal z (+ y (- x)))
                  (equal (- z) (bvminus 27 x y))))
  :hints (("Goal" :use (:instance equal-of-+-of-minus) :in-theory (disable equal-of-+-of-minus))))

;here they are for 32:

;gen the sizes! and the -1
(defthmd <-of-+-of-minus-32
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                ;(signed-byte-p 33 z)
                (equal -1 z) ;gen!
                )
           (equal (< (+ (- x) y) z)
                  (sbvlt 33 (bvminus 33 y x) z)))
  :hints (("Goal" :in-theory (enable bvlt sbvlt bvminus bvplus bvchop-of-sum-cases getbit-of-plus))))

;gen the sizes! and the -1
(defthmd <-of-+-of-minus-alt-32
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                ;(signed-byte-p 33 z)
                (equal -1 z) ;gen!
                )
           (equal (< (+ y (- x)) z)
                  (sbvlt 33 (bvminus 33 y x) z)))
  :hints (("Goal" :use (:instance <-of-+-of-minus-32)
           :in-theory (disable <-of-+-of-minus-32))))

;gen!
;use bind-free and free vars - way to combine those two?  augment the bind free code to use assumptions?
(defthm equal-of-+-of-minus-32
  (implies (and (syntaxp (quotep z))
                (< z 0)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 (- z)))
           (equal (equal z (+ (- x) y))
                  (equal (- z) (bvminus 33 x y))))
  :hints (("Goal" :in-theory (enable bvlt sbvlt bvminus bvplus bvchop-of-sum-cases))))

(defthm equal-of-+-of-minus-alt-32
  (implies (and (syntaxp (quotep z))
                (< z 0)
                (unsigned-byte-p 32 x) ;use axe-bind-free or look for free vars
                (unsigned-byte-p 32 y) ;use axe-bind-free or look for free vars
                (unsigned-byte-p 32 (- z)))
           (equal (equal z (+ y (- x)))
                  (equal (- z) (bvminus 33 x y))))
  :hints (("Goal" :use (:instance equal-of-+-of-minus-32) :in-theory (disable equal-of-+-of-minus))))



;gen
(defthm equal-of-0-and-getbit-when-bvlt-hack
  (implies (and (not (bvlt 6 free x))
                (syntaxp (quotep free))
                (equal 1 free))
           (equal (equal 0 (getbit 0 x))
                  (equal 0 (bvchop 6 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthmd slice-when-not-bvlt-hack
  (implies (and (not (bvlt '6 free x))
                (syntaxp (quotep free))
                (bvle 6 free 1))
           (equal (slice 5 2 x)
                  0))
  :hints (("Goal" :cases ((equal 0 (bvchop 6 x)))
           :in-theory (enable bvlt))))

(defthmd bvlt-6-1
  (equal (bvlt '6 1 x)
         (equal (equal 0 (slice 5 1 x))
                nil))
  :hints (("Goal" :cases ((equal 0 (bvchop 6 x))) :in-theory (enable bvlt))))

(defthm bvchop-6-slice-5
  (implies (and (equal 0 (slice 5 free x))
                (syntaxp (quotep free))
                (equal free 1))
           (equal (equal 0 (bvchop 6 x))
                  (not (equal 1 (bvchop 6 x))))))


;use polarities!
(defthm equal-of-0-and-slice-extend
  (implies (and (not (equal free (getbit 0 x)))
                (syntaxp (quotep free))
                (equal 0 free) ;gen
                )
           (equal (equal 0 (slice 5 1 x))
                  (equal 1 (slice 5 0 x)))))

;gen
(defthm equal-0-getbit-when-bvlt
  (implies (and (not (BVLT '6 free x))
                (syntaxp (quotep free))
                (equal 2 free))
           (equal (equal 0 (getbit 1 x))
                  (not (equal 2 (bvchop 6 x)))))
  :hints (("Goal"
           :cases ((equal 0 (bvchop 6 x))(equal 1 (bvchop 6 x)))
           :in-theory (e/d (bvlt getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

;Mon Jul 19 21:42:27 2010
;fixme loops with CONS-BECOMES-BV-ARRAY-WRITE-GEN?
(defthm bv-array-write-length-1
  (implies (natp index)
           (equal (bv-array-write width 1 index val data)
                  (list (bvchop width val))))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

;gen
(defthm unsigned-byte-p-of-2-when-bvlt
  (implies (and (bvlt 2 x free)
                (bvle 2 free 2))
           (equal (unsigned-byte-p 2 x)
                  (unsigned-byte-p 1 x)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvcat-when-unsigned-byte-p
  (implies (and (unsigned-byte-p free highval)
                (< free highsize)
                (natp highsize)
                (natp lowsize)
                (natp free))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat free highval lowsize lowval))))

(defthm bvcat-of-slice-extend-constant-region
  (implies (and (syntaxp (and (quotep lowval)
                              (quotep lowsize)))
                (equal k (slice 5 1 x))
                (syntaxp (quotep k))
                (natp lowsize))
           (equal (bvcat 29 (slice 30 2 x) lowsize lowval)
                  (bvcat 25 (slice 30 6 x) (+ lowsize 4) (bvcat 4 (slice 4 1 k) lowsize lowval)))))

(defthm +-of-same
  (equal (+ x x)
         (* 2 x)))

(defthm bvplus-of-same
  (equal (bvplus size x x)
         (bvmult size 2 x))
  :hints (("Goal" :in-theory (enable bvplus bvmult))))

;fixme gen!
(defthm bvlt-of-bvmult-of-constant-and-constant
  (equal (bvlt 32 (bvmult 32 2 x) 2147483648)
         (bvlt 31 x (expt 2 30))))

(defthm bvlt-of-bvuminus-same
  (equal (bvlt size x (bvuminus size x))
         (and (< 0 (bvchop size x))
              (< (bvchop size x) (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable bvlt bvuminus bvminus expt-of-+))))

;gen
;use polarities? but they are equal - which do we prefer?
;this is like strength reduction?
(defthm bvlt-6-4
  (equal (bvlt '6 x '4)
         (equal 0 (slice 5 2 x))))

;move
(defthm bv-array-write-shorten-constant-data
  (implies (and (syntaxp (and (quotep data)
                              (quotep numelems)))
                (< numelems (len data))
                (natp numelems))
           (equal (bv-array-write width numelems index val data)
                  (bv-array-write width numelems index val (firstn numelems data))))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm unsigned-byte-p-of-+-of-minus-better-helper
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                (<= n size)
                (natp n)
                )
           (equal (unsigned-byte-p n (+ x (- y)))
                  (if (bvlt (+ 1 size) x y)
                      nil ;because (+ x (- y)) is negative
                    (bvlt (+ 1 size) (bvminus (+ 1 size) x y) (expt 2 n)))))
  :hints (("Goal" :in-theory (enable bvlt bvminus bvuminus UNSIGNED-BYTE-P bvchop-of-sum-cases))))

;; (defthm unsigned-byte-p-of-+-of-minus-better-helper
;;   (implies (and (unsigned-byte-p size x)
;;                 (unsigned-byte-p size y)
;;                 (< n size)
;;                 (natp n)
;;                 )
;;            (equal (unsigned-byte-p n (+ x (- y)))
;;                   (if (bvlt size x y)
;;                       nil ;because (+ x (- y)) is negative
;;                     (bvlt size (bvminus size x y) (expt 2 n)))))
;;   :hints (("Goal" :in-theory (enable bvlt bvminus bvuminus UNSIGNED-BYTE-P))))

(defthmd nth-when-all-same
  (implies (and (all-same lst)
                (integerp x))
           (equal (nth x lst)
                  (if (< x (len lst))
                      (first lst)
                    nil)))
  :hints (("Goal" :in-theory (e/d ((:i nth) all-equal$) (;nth-of-cdr
                                                    )))))

(defthm nth-when-all-same-cheap
  (implies (and (syntaxp (quotep lst))
                (all-same lst)
                (integerp x))
           (equal (nth x lst)
                  (if (< x (len lst))
                      (first lst)
                    nil)))
  :hints (("Goal" :use (:instance nth-when-all-same)
           :in-theory (disable nth-when-all-same))))



;gen!
(defthm bvcat-of-slice-when-slice-known
  (implies (and (syntaxp (quotep k))
                (equal k1 (slice 5 2 x))
                (syntaxp (quotep k1))
                (natp lowsize))
           (equal (bvcat 29 (slice 30 2 x) lowsize k)
                  (bvcat 25 (slice 30 (+ 2 4) x) (+ lowsize 4) (bvcat 4 k1 lowsize k))))
  :hints (("Goal" :in-theory (enable REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))))

;gross?
;see also the xxx32 rule
(defthm bvplus-of-bvuminus-of-bvcat-of-slice
  (implies (and (syntaxp (quotep k))
                (not (bvlt 6 x free)) ;get rid of the free var?
                (bvle 6 k free)
                )
           (equal (bvplus 31 x (bvuminus 31 (bvcat 25 (slice 30 6 x) 6 k)))
                  (bvminus 6 x k)))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 31 x)) (n 31) (m 6))
           :in-theory (enable bvlt bvplus bvminus bvuminus bvcat logapp
                              bvchop-of-sum-cases
                              ))))

;use polarities?
(defthm unsigned-byte-p-of-1-when-not-nil
  (implies (and (not (equal free x))
                (syntaxp (quotep free))
                (equal free nil)
                (true-listp x))
           (equal (unsigned-byte-p 1 (len x))
                  (equal 1 (len x)))))



;loops with BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE ?
;use polarities?
;gen the bit indices
(defthm equal-of-constant-and-getbit-extend
  (implies (and (syntaxp (quotep k2))
                (equal k1 (getbit 1 x))
                (syntaxp (quotep k1))
                (unsigned-byte-p 1 k1)
                (unsigned-byte-p 1 k2))
           (equal (equal k2 (getbit 0 x))
                  (equal (bvcat 1 k1 1 k2)
                         (slice 1 0 x)))))
;gen!
(defthmd <-of-+-of-minus-and-constant
  (implies (and (unsigned-byte-p 35 x)
                (unsigned-byte-p 35 y)
                (signed-byte-p 36 k)
                )
           (equal (< (+ (- x) y) k)
                  (sbvlt 36 (bvminus 36 y x) k)))
  :hints (("Goal"
           :use (:instance signed-byte-p-when-top-bit-1 (n 36))
           :in-theory (enable bvlt sbvlt bvminus bvplus bvchop-of-sum-cases getbit-of-plus))))

;gen!
(defthmd <-of-+-of-minus-and-constant-alt
  (implies (and (unsigned-byte-p 35 x)
                (unsigned-byte-p 35 y)
                (signed-byte-p 36 k)
                ;(equal k -456)
                )
           (equal (< (+ y (- x)) k)
                  (sbvlt 36 (bvminus 36 y x) k)))
  :hints (("Goal" :use (:instance <-of-+-of-minus-and-constant)
           :in-theory (disable <-of-+-of-minus-and-constant))))

(defthm equal-of-bvchop-and-bvplus-of-same
  (implies (natp size)
           (equal (equal (bvchop size x) (bvplus size k x))
                  (equal 0 (bvchop size k))))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm equal-of-bvchop-and-bvplus-of-same-alt
  (implies (natp size)
           (equal (equal (bvplus size k x) (bvchop size x))
                  (equal 0 (bvchop size k))))
  :hints (("Goal" :use (:instance equal-of-bvchop-and-bvplus-of-same)
           :in-theory (disable equal-of-bvchop-and-bvplus-of-same))))

(defthm bvcat-of-constant-when-equal-of-constant-and-bvchop
  (implies (and (syntaxp (quotep k2))
                (equal k (bvchop size x))
                (syntaxp (quotep k))
                (< size highsize) ;gen?
                (posp size) ;could loop if size=0?
                (natp lowsize)
                (natp highsize))
           (equal (bvcat highsize x lowsize k2)
                  (bvcat (+ highsize (- size)) (slice (+ -1 highsize) size x) (+ lowsize size) (bvcat size k lowsize k2)))))

(defthm bvnot-of-myif
  (equal (bvnot size (myif test x1 x2))
         (bvnot size (bvif size test x1 x2)))
  :hints (("Goal" :in-theory (enable myif bvnot))))

(defthm leftrotate-32-of-myif-arg2
  (equal (leftrotate32 amt (myif test val1 val2))
         (leftrotate32 amt (bvif 32 test val1 val2))))

(defthm unsigned-byte-p-of-minus-when-natp
  (implies (natp x) ;possibly expensive?
           (equal (unsigned-byte-p '10 (unary-- x))
                  (equal 0 x))))

(defthmd integer-length-of-one-less-when-not-power-of-2p
  (implies (and (natp width)
                (not (power-of-2p width)))
           (equal (integer-length (+ -1 width))
                  (+ 1 (lg width))))
  :hints (("Subgoal *1/5" :in-theory (e/d (FLOOR-OF-SUM) (INTEGER-LENGTH-OF-FLOOR-BY-2 BVCHOP-1-BECOMES-GETBIT MOD-OF-EXPT-OF-2-CONSTANT-VERSION natp zip))
           :expand ((:with INTEGER-LENGTH (INTEGER-LENGTH WIDTH))
                    (:with INTEGER-LENGTH (INTEGER-LENGTH (+ -1 WIDTH)))))
          ("Subgoal *1/4"  :in-theory (e/d (FLOOR-OF-SUM) (INTEGER-LENGTH-OF-FLOOR-BY-2 BVCHOP-1-BECOMES-GETBIT MOD-OF-EXPT-OF-2-CONSTANT-VERSION natp zip))
           :expand ((:with INTEGER-LENGTH (INTEGER-LENGTH WIDTH))
                    (:with INTEGER-LENGTH (INTEGER-LENGTH (+ -1 WIDTH)))))
          ("Goal" :in-theory (e/d (power-of-2p lg integer-length zip expt-of-+)
                                  (BVCHOP-1-BECOMES-GETBIT INTEGER-LENGTH-OF-FLOOR-BY-2 MOD-OF-EXPT-OF-2-CONSTANT-VERSION)))))


;gen
(defthm <-of-lg-and-minus-1
  (not (< (lg len) -1))
  :hints (("Goal" :in-theory (enable lg))))

(defthm <-of-*-of-2-and-expt-of-lg
  (IMPLIES (AND (INTEGERP LEN)
                (<= 0 LEN))
           (< LEN (* 2 (EXPT 2 (LG LEN)))))
  :hints (("Goal" :in-theory (enable lg))))

(defthm bvchop-of-integer-length-of-one-less
  (implies (natp len)
           (equal (bvchop (integer-length (+ -1 len)) len)
                  (if (power-of-2p len)
                      0
                    len)))
  :hints (("Goal" :in-theory (enable power-of-2p unsigned-byte-p expt-of-+ natp integer-length-of-one-less-when-not-power-of-2p))))

(defthm bv-array-read-when-index-is-len
  (equal (bv-array-read width len len data)
         (if (power-of-2p len)
             (bv-array-read width len 0 data)
           0))
  :hints (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg)
                                  (nth-becomes-bv-array-read2
                                   getbit-of-nth-becomes-bv-array-read ;looped?
                                   )))))

(defthm unsigned-byte-p-of-minus
  (implies (and (integerp x)
                (natp size))
           (equal (unsigned-byte-p size (- x))
                  (and (<= x 0)
                       (< (- (expt 2 size)) x))))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))

(defthm boolor-lemma-sha-1
  (implies (bvle 6 4 k)
           (equal (boolor (equal 0 (slice 5 2 x)) (bvlt 6 x k))
                  (bvlt 6 x k)))
  :hints (("Goal" :in-theory (enable bvlt
                                     REWRITE-<-WHEN-SIZES-DONT-MATCH
                                     REWRITE-<-WHEN-SIZES-DONT-MATCH2))))

(defthm equal-of-0-and-+-of-minus-2
  (implies (and (acl2-numberp x)(acl2-numberp y))
           (equal (equal 0 (+ (- x) y))
                  (equal x y))))

;fixme use polarities?
;move?
(DEFTHM BVLT-TIGHTEN-FREE-and-free
  (IMPLIES (AND (UNSIGNED-BYTE-P FREE1 X)
                (SYNTAXP (QUOTEP FREE1))
                (< FREE1 SIZE)
                (UNSIGNED-BYTE-P FREE2 y)
                (SYNTAXP (QUOTEP FREE2))
                (< FREE2 SIZE)
                (natp free1)
                (natp free2)
                (NATP SIZE))
           (EQUAL (BVLT SIZE X y)
                  (BVLT (max FREE1 free2) X y)))
  :hints (("Goal" :in-theory (disable BVLT-WHEN-UNSIGNED-BYTE-P-BETTER-NON-CONSTANT)
           :use (:instance BVLT-TIGHTEN-FREE (k y) (free (max free1 free2))))))


;gen to a trim rule?
(defthm bv-array-read-of-bvcat-256
  (equal (bv-array-read width '256 (bvcat highsize x '8 y) data)
         (bv-array-read width '256 y data))
  :hints (("Goal" :in-theory (e/d (bv-array-read
                                   ) (nth-becomes-bv-array-read2)))))

(defthm bv-array-read-of-firstn
  (implies (and (< index len)
                (equal len (len x))
                (natp index)
;(natp n)
                )
           (equal (bv-array-read width len index (firstn n x))
                  (if (< index (nfix n))
                      (bv-array-read width len index x)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener)
                                  (nth-becomes-bv-array-read2
                                   getbit-of-nth-becomes-bv-array-read ;looped
                                   )))))



(defthm bvlt-of-one-more-when-not-bvlt-helper
  (IMPLIES (AND (integerp z)
                (<= z y)
                (< X (+ 1 z))
                (UNSIGNED-BYTE-P 31 X)
                (UNSIGNED-BYTE-P 31 Y)
                )
           (equal (<= Y X)
                  (EQUAL X Y)))
  :rule-classes nil)

;use priorities?
(defthm bvlt-of-one-more-when-not-bvlt
  (implies (and (not (bvlt 31 x free))
                (equal y free) ;poor man's backchain limit
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt 31 x (bvplus 7 1 y)) ;fixme gen the 7 (and the 1?) and the 31
                  (and (equal (bvchop 31 x) (bvchop 31 y))
                       (not (equal 127 (bvchop 7 y)))
                       (unsigned-byte-p 7 y)
                       )))
  :hints (("Goal"
           :use (:instance bvlt-of-one-more-when-not-bvlt-helper (z (bvchop 7 y)))
           :in-theory (enable bvlt bvplus GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER bvchop-of-sum-cases))))

(defthm cdr-of-bv-array-write-of-cons
  (implies (and (integerp len)
                (< key len) ;Mon Jul 19 21:43:17 2010
                (natp key))
           (equal (cdr (bv-array-write element-size len key val (cons x lst)))
                  (if (zp len)
                      nil
                      (if (equal 0 key)
                          (bvchop-list element-size
                                        (cdr (take len (true-list-fix (cons x lst)))))
                          (bv-array-write element-size (- len 1)
                                          (- key 1)
                                          val lst)))))
  :hints (("Goal" :use (:instance cdr-of-bv-array-write-better (lst (cons x lst))))))

(defthm update-subrange-from-end
  (implies (and (natp end)
                (true-listp lst) ;drop?
                )
           (equal (update-subrange (len lst) end vals lst)
                  (append lst (take (+ 1 (- end (len lst))) vals))))
  :hints (("Goal" :in-theory (enable update-subrange posp natp))))

;move?
(defthm all-unsigned-byte-p-of-update-subrange
  (implies (and (all-unsigned-byte-p size lst)
                (all-unsigned-byte-p size vals)
                (integerp start) (natp start)
                (integerp end)
                (natp size)
                (true-listp lst) ;drop?
                (<= start (len lst))
                (<= (+ end 1 (- start)) (len vals)))
           (all-unsigned-byte-p size (update-subrange start end vals lst)))
  :hints (("Goal" ;:cases ((equal -1 end))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (update-subrange natp UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
                           (NTH-BECOMES-BV-ARRAY-READ2
                            UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;gen?
(defthm all-unsigned-byte-p-of-update-subrange2
  (implies (and (all-unsigned-byte-p size lst)
                (all-unsigned-byte-p size vals)
                (natp start) ;gen?
                (integerp end) ;(natp end) ;gen?
                (<= (+ end 1 (- start)) (len vals)) ;what if len causes not all vals to be used?
                (<= len (len lst)) ;gen?
                (true-listp lst)
                (natp size))
           (all-unsigned-byte-p size (update-subrange2 len start end vals lst)))
  :hints (("Goal" :cases ((<= start len))
           :in-theory (enable natp))))

;move
;more like this?
(defthm bvlt-when-low-bits-too-big
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal free (bvchop freesize x)) ;note the order
                (syntaxp (and (quotep free)
                              (quotep freesize)))
                (<= (bvchop size k) free)
                (<= freesize size)
                (natp size))
           (equal (bvlt size x k)
                  nil))
  :hints (("Goal" :use (:instance <-of-bvchop-and-bvchop-same (s1 freesize) (s2 size))
           :in-theory (e/d (bvlt) (<-of-bvchop-and-bvchop-same
                                   REWRITE-<-WHEN-SIZES-DONT-MATCH)))))

;move
(defthmd slice-of-bv-array-read-helper
  (implies (and (natp high)
                (natp low)
                (< high element-size)
                (natp len)
                (natp element-size))
           (equal (slice high low (bv-array-read element-size len index data))
                  (bv-array-read (+ 1 (- high low)) len index (map-slice high low data))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (map-slice ;LIST::NTH-WITH-LARGE-INDEX
                            natp posp bv-array-read SLICE-WHEN-VAL-IS-NOT-AN-INTEGER BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                           (NTH-BECOMES-BV-ARRAY-READ2
                            ;;LIST::NTH-OF-CONS
                            )))))

;move
(defthmd slice-of-bv-array-read
  (implies (and (syntaxp (and (quotep data)
                              (quotep low)
                              (quotep high)))
                (natp high)
                (natp low)
                (< high element-size)
                (natp len)
                (natp element-size))
           (equal (slice high low (bv-array-read element-size len index data))
                  (bv-array-read (+ 1 (- high low)) len index (map-slice high low data))))
  :hints (("Goal" :use (:instance slice-of-bv-array-read-helper))))

(defthm unsigned-byte-p-tighten-from-bound
  (implies (and (bvlt size x free)
                (posp size)
                (bvle size free (expt 2 (+ -1 size))))
           (equal (unsigned-byte-p size x)
                  (unsigned-byte-p (+ -1 size) x)))
  :hints (("Goal" :in-theory (enable bvlt))))


;gen!
(defthm bvlt-of-slice-same
  (equal (bvlt '30 (slice '29 '1 x) x)
         (not (equal 0 (bvchop 30 x))))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 30 x)) (n 30) (m 1))
           :in-theory (e/d (bvlt ;slice
                            bvcat logapp
                            ) (bvchop-of-logtail-becomes-slice
                            bvcat-slice-same
                            bvcat-equal-rewrite-alt)))))



;slow!
;yuck? could strengthen true-listp to equal nil when len is 0... - use polarities?
(defthmd equal-when-lens-0
  (implies (and (equal free (len x))
                (equal 0 free)
                (equal free2 (len y))
                (equal 0 free2)
                (true-listp x)
                (true-listp y))
           (equal (equal x y)
                  (equal (finalcdr x) (finalcdr y)))))


;; (thm
;;  (implies (not (BVLT '2 x '2))
;;           (equal (GETBIT '1 x)
;;                  1)))

(defthm bvlt-1
  (equal (bvlt 1 x y)
         (and (equal 0 (getbit 0 x))
              (equal 1 (getbit 0 y))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm getbit-identity-cheap
  (implies (and (unsigned-byte-p free x)
                (equal 1 free))
           (equal (getbit 0 x) x)))

(defthm unsigned-byte-p-of-1-when-not-0-free
  (implies (and (not (equal free x))
                (equal 0 free))
           (equal (unsigned-byte-p 1 x)
                  (equal 1 x))))

(defthmd prefixp-when-longer-work-hard
  (implies (work-hard (< (len x) (len y)))
           (equal (prefixp y x)
                  nil))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthmd prefixp-when-not-shorter-work-hard
  (implies (work-hard (<= (len x) (len y)))
           (equal (prefixp y x)
                  (equal (true-list-fix x) (true-list-fix y))))
  :hints (("Goal" :in-theory (enable prefixp))))

;gen!
(defthm bvlt-when-top-bit-one
  (implies (and (not (equal free (getbit 1 x)))
                (equal 0 free))
           (equal (bvlt 2 1 x)
                  t))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 2 x)) (m 1) (n 2))
           :in-theory (enable bvlt bvcat logapp))))

(defthm equal-of-nth2-and-bv-array-read
  (implies (and (natp len)
                (natp index)
                (< index len)
                (natp width2)
                (<= width2 width)
                (unsigned-byte-p width index)
                )
           (equal (equal (nth2 width index data) (bv-array-read width2 len index data))
                  (unsigned-byte-p width2 (nth2 width index data))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener nth2) (nth-becomes-bv-array-read2)))))

;rename?
(defthm equal-of-nth2-and-bv-array-read-alt
  (implies (and (natp len)
                (natp index)
                (< index len)
                (natp width2)
                (<= width2 width)
                (unsigned-byte-p width index)
                )
           (equal (equal (bv-array-read width2 len index data) (nth2 width index data))
                  (unsigned-byte-p width2 (nth2 width index data))))
  :hints (("Goal" :use (:instance equal-of-nth2-and-bv-array-read)
           :in-theory (disable equal-of-nth2-and-bv-array-read))))

(defthm unsigned-byte-p-of-nth2
  (implies (and (unsigned-byte-p width index)
                (< index (len data))
                (natp size)
                (all-unsigned-byte-p size data))
           (equal (unsigned-byte-p size (nth2 width index data))
                  t))
  :hints (("Goal" :in-theory (enable nth2))))

;fixme gen a lot or improve axe to not need this
(defthm hack-for-aes-cbc
  (equal (bvplus '31 (bvcat '27 (slice '30 '4 x) '4 '15) (bvuminus '31 x))
         (bvplus 4 15 (bvuminus 4 x)))
  :hints (("Goal"
           :use ((:instance split-bv (y (bvchop 31 x)) (n 31) (m 4)))
           :in-theory (e/d (bvplus bvuminus bvminus bvcat logapp bvchop-of-sum-cases)
                           (<-OF-+-OF-MINUS-AND-CONSTANT ;looped
                            )))))

(defthm <-of-expt-of-one-less-of-integer-length
  (implies (posp x)
           (not (< x (expt 2 (+ -1 (integer-length x))))))
  :hints (("Goal" :in-theory (enable integer-length))))

;move
(defthm <-of-integer-length-arg2
  (implies (and (posp x)
                (natp n))
           (equal (< n (integer-length x))
                  (<= (expt 2 n) x)))
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm <-of-integer-length-arg1
  (implies (and (syntaxp (not (and (quotep n) (< 1000 (unquote n))))) ;prevent huge calls to EXPT
                (posp x)
                (natp n))
           (equal (< (integer-length x) n)
                  (< x (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (enable integer-length posp))))

(defthm unsigned-byte-p-of-ceiling-of-lg
  (implies (and (natp x) ;(posp x) ;gen?
                (natp n))
           (equal (unsigned-byte-p n (ceiling-of-lg x))
                  (<= x (expt 2 (+ -1 (expt 2 n))))))
  :hints (("Goal" :cases ((equal 1 x)(equal 0 x))
           :in-theory (enable ceiling-of-lg unsigned-byte-p posp))))

(defthm aesccbhack1
  (implies (and ;(natp x) ;(posp x) ;gen?
                ;(natp n)
                (unsigned-byte-p 8 x)
                (not (bvlt '8 '128 x))
                )
           (equal (bvlt 3 4 (ceiling-of-lg x))
                  (bvlt 8 16 x)
                  ))
  :hints (("Goal" :cases ((equal 1 x)(equal 0 x))
           :in-theory (e/d (bvlt ceiling-of-lg unsigned-byte-p posp)
                           (<-of-+-of-minus-and-constant ;yuck?
                            )))))


;;

;compare to UNSIGNED-BYTE-P-OF-BVCHOP-BIGGER
(defthm unsigned-byte-p-of-bvchop-bigger2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2))
           (equal (unsigned-byte-p size1 (bvchop size2 x))
                  (equal 0 (slice (+ -1 size2) size1 x))))
  :hints (("Goal"
           :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y (bvchop size2 x)) (n size2) (m size1)))))

;fixme should stp be able to prove goals like this? maybe we dont translate the read since the len is unknown...
(defthm equal-of-bv-array-read-and-bv-array-read-different-widths
  (equal (equal (bv-array-read '32 len index data) (bv-array-read '31 len index data))
         (unsigned-byte-p 31 (bv-array-read '32 len index data)))
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-READ) (NTH-BECOMES-BV-ARRAY-READ2
                                                   GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ ;looped
                                                   UNSIGNED-BYTE-P-OF-BVCHOP-BIGGER)))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ)))
(theory-invariant (incompatible (:definition bv-array-read) (:rewrite BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ)))

(defthm getbit-of-bv-array-read-when-all-unsigned-byte-p
  (implies (all-unsigned-byte-p 31 x)
           (equal (getbit 31 (bv-array-read 32 len index x))
                  0))
  :hints (("Goal"
           :cases ((< (bvchop (ceiling-of-lg len) index) (len x)))
           :in-theory (e/d (bv-array-read getbit-too-high ;list::nth-with-large-index
                                          )
                           (nth-becomes-bv-array-read2
                            bvchop-of-nth-becomes-bv-array-read
                            getbit-of-nth-becomes-bv-array-read)))))



(defthm bvplus-of-bvuminus-of-bvcat-of-slice32
  (implies (and (syntaxp (quotep k))
                (bvle 6 k x)
                (unsigned-byte-p 31 x)
                )
           (equal (bvplus 32 x (bvuminus 32 (bvcat 25 (slice 30 6 x) 6 k)))
                  (bvminus 6 x k)))
  :hints (("Goal"
           :use (:instance split-bv (y (bvchop 31 x)) (n 31) (m 6))
           :in-theory (e/d (bvlt bvplus bvminus bvuminus bvcat logapp
                              bvchop-of-sum-cases
                              ) (<-OF-+-OF-MINUS-AND-CONSTANT-ALT ;fixme disable!
                                 )))))

;gen!
(DEFTHM EQUAL-OF-0-AND-SLICE-WHEN-BVLT2
  (IMPLIES (AND (BVLT 5 K X)
                (SYNTAXP (QUOTEP K))
                (BVLt 5 3 K)) ;ffffixme allow bvle
           (EQUAL (EQUAL 0 (SLICE 5 2 X))
                  NIL))
  :HINTS
  (("Goal"
    :USE (:INSTANCE EQUAL-OF-0-AND-SLICE-WHEN-BVLT)
    :IN-THEORY
    (E/D (BVLT-TIGHTEN-WHEN-SLICE-0-GEN)
         (BVCAT-EQUAL-REWRITE-ALT
          BVCAT-EQUAL-REWRITE
          BVCAT-TIGHTEN-UPPER-SIZE
          REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2
          )))))

;gen this by improving getbit-when-bvlt-of-small
(defthmd equal-of-bvchop-extend-when-bvlt-helper
  (implies (and (bvlt size2 x free) ;x is bounded such that its top bit must be 0 (fixme make a version for 1...)
                (< size size2)
                (bvle size2 free (expt 2 size))
                (natp size)
                (natp size2))
           (equal (bvchop size x)
                  (bvchop size2 x)))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases unsigned-byte-p) (slice-too-high-is-0-new bound-when-usb2 bvchop-when-<-tighten unsigned-byte-p-of-bvchop-bigger2))
           :use (:instance slice-too-high-is-0-new (high (+ -1 size2)) (low size)))))


(defthmd equal-of-bvchop-extend-when-not-bvlt-helper
   (implies (and (not (bvlt size2 free x)) ;x is bounded such that its top bits must be 0 (fixme make a version for 1... and maybe other values?)
                 (< size size2)
                 (bvlt size2 free (expt 2 size))
                 (natp size)
                 (natp size2))
            (equal (bvchop size x)
                   (bvchop size2 x)))
   :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases unsigned-byte-p) (slice-too-high-is-0-new bound-when-usb2 bvchop-when-<-tighten unsigned-byte-p-of-bvchop-bigger2))
            :use (:instance slice-too-high-is-0-new (high (+ -1 size2)) (low size)))))



;; ;fixme gen!
;; (defthm bvplus-of-bvcat-4294967292-4
;;   (implies (and (syntaxp (quotep k)) ;fixme
;;                 (equal 4294967292 k) ;(<= 4294967292 k)               (< k 4294967296)
;;                 (integerp k))
;;            (equal (bvplus 32 ;could also be 32
;;                           k (bvcat 25 x 6 4))
;;                   (bvcat 25 x 6 (- 4 (- (expt 2 32) k)))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvplus getbit bvcat logapp
;;                                           bvchop-of-sum-cases
;;                                           )
;;                                   (anti-bvplus
;;                                    (:REWRITE SLICE-BECOMES-GETBIT)
;;                                    (:REWRITE BVCHOP-1-BECOMES-GETBIT)
;;                                    SLICE-OF-SUM-CASES)))))

;; (defthm bvplus-of-bvcat-4294967293-4
;;   (implies (and (syntaxp (quotep k)) ;fixme
;;                 (equal 4294967293 k) ;(<= 4294967292 k)               (< k 4294967296)
;;                 (integerp k))
;;            (equal (bvplus 32 ;could also be 32
;;                           k (bvcat 25 x 6 4))
;;                   (bvcat 25 x 6 (- 4 (- (expt 2 32) k)))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvplus getbit bvcat logapp
;;                                           bvchop-of-sum-cases
;;                                           )
;;                                   (anti-bvplus
;;                                    (:REWRITE SLICE-BECOMES-GETBIT)
;;                                    (:REWRITE BVCHOP-1-BECOMES-GETBIT)
;;                                    SLICE-OF-SUM-CASES)))))

;; (defthm bvplus-of-bvcat-4294967294-4
;;   (implies (and (syntaxp (quotep k)) ;fixme
;;                 (equal 4294967294 k) ;(<= 4294967292 k)               (< k 4294967296)
;;                 (integerp k))
;;            (equal (bvplus 32 ;could also be 32
;;                           k (bvcat 25 x 6 4))
;;                   (bvcat 25 x 6 (- 4 (- (expt 2 32) k)))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvplus getbit bvcat logapp
;;                                           bvchop-of-sum-cases
;;                                           )
;;                                   (anti-bvplus
;;                                    (:REWRITE SLICE-BECOMES-GETBIT)
;;                                    (:REWRITE BVCHOP-1-BECOMES-GETBIT)
;;                                    SLICE-OF-SUM-CASES)))))

;; (defthm bvplus-of-bvcat-4294967295-4
;;   (implies (and (syntaxp (quotep k)) ;fixme
;;                 (equal 4294967295 k) ;(<= 4294967292 k)               (< k 4294967296)
;;                 (integerp k))
;;            (equal (bvplus 32 ;could also be 32
;;                           k (bvcat 25 x 6 4))
;;                   (bvcat 25 x 6 (- 4 (- (expt 2 32) k)))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (bvplus getbit bvcat logapp
;;                                           bvchop-of-sum-cases
;;                                           )
;;                                   (anti-bvplus
;;                                    (:REWRITE SLICE-BECOMES-GETBIT)
;;                                    (:REWRITE BVCHOP-1-BECOMES-GETBIT)
;;                                    SLICE-OF-SUM-CASES)))))


(defthmd plus-of-bvcat-fits-in-low-bits-core-helper
  (implies (and (<= 0 (+ k1 k2))
                (< (+ k1 k2) (expt 2 lowsize))
                (unsigned-byte-p lowsize k2) ;drop
                ;(natp lowsize)
                (integerp k1))
           (equal (+ k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :expand ((unsigned-byte-p lowsize (+ k1 k2)))
           :in-theory (enable bvcat logapp))))

(defthm bvcat-of-+-of-bvchop
  (implies (and (integerp k1) (integerp k2))
           (equal (BVCAT HIGHSIZE X LOWSIZE (+ K1 (BVCHOP LOWSIZE K2)))
                  (BVCAT HIGHSIZE X LOWSIZE (+ K1 K2)))))

(defthm plus-of-bvcat-fits-in-low-bits-core
  (implies (and (<= 0 (+ k1 (bvchop lowsize k2)))
                (< (+ k1 (bvchop lowsize k2)) (expt 2 lowsize))
                (natp lowsize)
                (integerp k2)
                (integerp k1))
           (equal (+ k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :use (:instance plus-of-bvcat-fits-in-low-bits-core-helper (k2 (bvchop lowsize k2))))))

(defthm plus-of-bvcat-fits-in-low-bits-core-negative-k1
  (implies (and (<= 0 (+ k1 (bvchop lowsize k2)))
                (<= k1 0)
                (natp lowsize)
                (integerp k1))
           (equal (+ k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :in-theory (disable plus-of-bvcat-fits-in-low-bits-core)
           :use (:instance plus-of-bvcat-fits-in-low-bits-core))))

(defthm bvplus-of-bvcat-fits-in-low-bits-core-negative-k1-helper
  (implies (and (<= 0 (+ k1 (bvchop lowsize k2)))
                (<= k1 0)
                (natp lowsize)
                (natp highsize)
                (<= (+ lowsize highsize) size)
                (integerp size)
                (integerp k1))
           (equal (bvplus size k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :in-theory (e/d (bvplus) (plus-of-bvcat-fits-in-low-bits-core-negative-k1
                                            BVCAT-OF-BVCHOP-LOW ;looped
                                            ))
           :use (:instance plus-of-bvcat-fits-in-low-bits-core-negative-k1))))



;could allow the inner size to differ
(defthm bvplus-of-+-of-minus-of-expt
  (implies (and (natp size)
                (integerp x))
           (equal (bvplus size (+ x (- (expt 2 size))) y)
                  (bvplus size x y))))

(defthm bvplus-of-bvcat-fits-in-low-bits-core-negative-k1
  (implies (and (<= 0 (+ (- k1 (expt 2 size)) (bvchop lowsize k2)))
                (unsigned-byte-p size k1) ;drop?
                (integerp k2)
                (natp lowsize)
                (natp highsize)
                (<= (+ lowsize highsize) size)
                (integerp size)
                (integerp k1))
           (equal (bvplus size k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :use (:instance bvplus-of-bvcat-fits-in-low-bits-core-negative-k1-helper (k1 (- k1 (expt 2 size))))
           :in-theory (disable bvplus-of-bvcat-fits-in-low-bits-core-negative-k1-helper))))

(defthm bvplus-of-bvcat-fits-in-low-bits-negative-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (<= 0 (+ (- k1 (expt 2 size)) (bvchop lowsize k2)))
                (unsigned-byte-p size k1) ;drop?
                (integerp k2)
                (natp lowsize)
                (natp highsize)
                (<= (+ lowsize highsize) size)
                (integerp size)
                (integerp k1))
           (equal (bvplus size k1 (bvcat highsize x lowsize k2))
                  (bvcat highsize x lowsize (+ k2 k1))))
  :hints (("Goal" :use (:instance bvplus-of-bvcat-fits-in-low-bits-core-negative-k1)
           :in-theory (disable bvplus-of-bvcat-fits-in-low-bits-core-negative-k1))))

(defthm equal-of-bv-array-read-and-bv-array-read-leibniz
  (implies (work-hard (equal index1 index2))
           (equal (equal (bv-array-read ELEMENT-SIZE LEN INDEX1 DATA) (bv-array-read ELEMENT-SIZE LEN INDEX2 DATA))
                  t)))

;fixme could combine with the regular rule..
(defthm take-of-subrange-too-big
  (implies (and (< (+ 1 (- end start)) i)
                (natp start)
                (natp end)
                (natp i))
           (equal (take i (subrange start end lst))
                  (if (< end (nfix start))
                      (repeat i nil)
                    ;;usual case:
                    (append (subrange start end lst)
                            (repeat (- i (+ 1 (- end start)))
                                    nil))))))

;move?
;use defforall?
(defthm all-unsigned-byte-p-of-subrange
  (implies (and (all-unsigned-byte-p size x)
                (integerp start)
                (integerp end))
           (equal (all-unsigned-byte-p size (subrange start end x))
                  (or (< (nfix end) start)
                      (< end (len x)))))
  :hints (("Goal" :in-theory (e/d (SUBRANGE)
                                  (NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                   CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER)))))

;; ;this may help get rid of irrelevant values in x...
;; ;or is it gross to introduce repeat?
;; ;fffixme can this loop?!
;; (defthmd all-unsigned-byte-p-of-take-of-subrange
;;   (implies (and (all-unsigned-byte-p width x)
;;                 (natp width)
;;                 (natp start)
;;                 (natp end)
;;                 (natp i)
;;                 )
;;            (equal (all-unsigned-byte-p width (take i (subrange start end x)))
;;                   (all-unsigned-byte-p width (take i (subrange start end (repeat (len x) 0))))))
;;   :hints (("Goal" :cases ( (< (+ 1 (- end start)) i)))))

;this may help get rid of the values of x, which may be large terms!
;fixme where does the take come from?
;fixme is this too special-purpose?  it may be useful just for efficiency..
(defthm all-unsigned-byte-p-of-take-of-subrange
  (implies (and (all-unsigned-byte-p width x)
                (natp width)
                (natp start)
                (natp end)
                (natp i)
                )
           (equal (all-unsigned-byte-p width (take i (subrange start end x)))
                  (if (< (+ 1 (- end start)) i)
                      (and (< end start)
                           (equal i 0))
                    (or (equal i 0)
                        (< (+ start i -1) (len x)))))))



;; ;gen the 1 that gets added
;; (thm
;;  (implies (not (equal (bvchop 31 x) (+ -1 (expt 2 31))))
;;           (equal (bvmod 31 (bvplus 31 1 (bvmod 31 x y)) y)
;;                  (bvmod 31 (bvplus 31 1 x) y)))
;;  :hints (("Goal"
;;           :cases ((equal 0 (bvchop 31 y)))
;;           :in-theory (e/d (bvmod bvplus)
;;                                  (;SIMPLIFY-MOD-+-MOD ;fixme improve
;;                                   mod-type
;;                                   )))))

;; (DEFTHM <-OF-MOD-SAME-linear
;;   (IMPLIES (AND (<= 0 X)
;;                 (RATIONALP X)
;;                 (<= 0 Y)
;;                 (RATIONALP Y))
;;            (EQUAL (< X (MOD X Y)) NIL))
;;   :rule-classes ((:linear))
;;   )


;used below
(defthmd <-of-+-and-0
  (implies (and (<= 0 x)
                (<= 0 y))
           (not (< (+ x y) 0))))

(defthmd bvmod-of-bvplus-of-bvmod-helper
  (implies (and (bvlt 32 (bvplus 32 k x) (expt 2 31))
                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 k))
           (equal (bvmod 31 (bvplus 31 k (bvmod 31 x y)) y)
                  (bvmod 31 (bvplus 31 k x) y)))
  :hints (("Goal"
           :cases ((equal 0 (bvchop 31 y)))
           :expand ((unsigned-byte-p 31 (+ K (MOD X (BVCHOP 31 Y)))))
           :use ((:instance bvchop-identity (size 31) (i (+ K (MOD X (BVCHOP 31 Y)))))
                 (:instance bvchop-identity (size 31) (i (+ K x)))
                 (:instance bvchop-identity (size 32) (i (+ K x))))
           :in-theory (e/d (bvmod bvplus bvlt <-of-+-and-0)
                           ( ;SIMPLIFY-MOD-+-MOD ;fixme improve
                            bvchop-identity
                            BVCHOP-DOES-NOTHING-REWRITE
                            anti-bvplus
                            mod-type
                            )))))

;is the work-hard needed?
(defthm bvmod-of-bvplus-of-bvmod
  (implies (work-hard (bvlt 32 (bvplus 32 (bvchop 31 k) (bvchop 31 x)) (expt 2 31))) ;no overflow
           (equal (bvmod 31 (bvplus 31 k (bvmod 31 x y)) y)
                  (bvmod 31 (bvplus 31 k x) y)))
  :hints (("Goal" :use (:instance bvmod-of-bvplus-of-bvmod-helper (x (bvchop 31 x)) (k (bvchop 31 k))))))

;fixme move
(defthm bv-array-read-tighten-free
  (implies (and (syntaxp (quotep width))
                (all-unsigned-byte-p free data)
                (syntaxp (quotep free))
                (equal len (len data))
                (natp free)
                (natp width)
                (< free width))
           (equal (bv-array-read width len index data)
                  (bv-array-read free len index data)))
  :hints (("Goal" :in-theory (e/d (SLICE-TOO-HIGH-IS-0
                                   bv-array-read)
                                  (BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                                   GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))


;gross proof?
;fixme gen!
(defthm equal-of-bv-array-write-and-bv-array-write-top-elements
  (implies (and (work-hard (< index (bvplus '5 '1 index))) ;fixme
                (work-hard (< index (bvplus '5 '1 index))) ;fixme
                (work-hard (natp index)) ;so we can use bv-array-write-opener
                (all-unsigned-byte-p 8 data1)
                (all-unsigned-byte-p 8 data2)
                (true-listp data1)
                (true-listp data2))
           (equal (equal (bv-array-write '8 (bvplus '5 '1 index) index val1 data1)
                         (bv-array-write '8 (bvplus '5 '1 index) index val2 data2))
                  (and (equal (bvchop 8 val1)
                              (bvchop 8 val2))
                       (equal (bvchop-list 8 (take index data1))
                              (bvchop-list 8 (take index data2))))))
  :hints (("Goal" :in-theory (e/d (bv-array-write-opener
                                   update-nth2
                                   bvplus) (update-nth-becomes-update-nth2-extend-gen)))))



(defthm <-of-bvchop-when-<-of-bvchop-smaller
  (implies (and (< k (bvchop freesize x))
                (<= freesize size)
                (natp freesize)
                (natp size))
           (< k (bvchop size x)))
  :hints (("Goal" :use (:instance <-of-bvchop-and-bvchop-same (s1 freesize) (s2 size))
           :in-theory (disable <-of-bvchop-and-bvchop-same
                               rewrite-<-when-sizes-dont-match))))

;move
(defthm bvlt-when-bvlt-smaller-of-constant
  (implies (and (syntaxp (quotep k))
                (bvlt freesize k x)
                (unsigned-byte-p freesize k)
                (<= freesize size)
                (natp freesize)
                (natp size))
           (equal (bvlt size k x)
                  t))
  :hints (("Goal" :in-theory (enable bvlt))))

;(include-book "packbv-axe")
;(include-book "arrays-axe")

;move up
;fixme gen!
;add a polarity?
;makes clear the one case in which incrementing x makes it go non-negative
(defthm sbvlt-of-bvplus-of-1-and-0
  (implies (and (unsigned-byte-p 32 x)
                (sbvle 32 0 x))
           (equal (sbvlt 32 (bvplus 32 1 x) 0)
                  (equal (bvchop 32 x) (+ -1 (expt 2 31)))))
  :hints (("Goal" :in-theory (disable ;sbvlt-rewrite sbvle SBVLT-WHEN-SBVMODDOWN-HACK4
                              ))))

(defthm sbvlt-transitive-1
  (implies (and (sbvlt 32 i free)
                (not (sbvlt 32 len free)))
           (sbvlt 32 i len)))

(defthm myif-of-myif-of-myif-same-1
 (equal (MYIF test a (MYIF b (MYIF test c d) e))
        (MYIF test a (MYIF b d e)))
 :hints (("Goal" :in-theory (enable myif))))

(defthm sbvlt-of-bvplus-of-1-and-0-alt
  (implies (sbvlt 32 n (+ -1 (expt 2 31)))
           (equal (SBVLT '32 (BVPLUS '32 '1 n) '0)
                  (SBVLT 32 n -1)))
  :hints (("Goal" :in-theory (enable SBVLT-REWRITE))))

(defthm sbvlt-of-maxint-when-sbvlt
  (IMPLIES (SBVLT 32 N free)
           (SBVLT 32 N 2147483647)))

(defthm bvlt-of-bvplus-of-1
  (IMPLIES (AND (BVLT 31 I J)
                (BVLT 31 J LEN))
           (BVLT 31 (BVPLUS 31 1 I) LEN))
  :hints (("Goal" :in-theory (enable bvlt bvplus
                                     bvchop-of-sum-cases
                                     ))))

(defthm sbvlt-of-bvplus-of-1-alt
  (implies (and (sbvlt 32 i j)
                (sbvlt 32 j len))
           (sbvlt 32 (bvplus 32 1 i) len))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))

(defthm sbvlt-of-bvplus-of-minus-1
  (implies (NOT (SBVLT '32 x '0))
           (NOT (SBVLT '32 (BVPLUS '32 4294967295 x) '-1)))
  :hints (("Goal" :in-theory (e/d (sbvlt bvminus) (;BVPLUS-OF-MINUS-1
                                                   )))))
(defthm bvlt-of-plus-hack9
  (implies (and (bvlt 31 x y)
                (integerp x)
                (not (equal 0 (bvchop 31 x))))
           (BVLT '31 (+ 2147483647 x) y))
  :hints (("Goal" :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases)
                                  (;BVPLUS-OF-MINUS-1
                                   )))))

; x<y ->  x-1<y, assuming x isn't the most negative number
(defthm sbvlt-of-one-less
  (implies (and (sbvlt 32 x y)
                (not (equal (expt 2 31) (bvchop 32 x))))
           (SBVLT '32 (BVPLUS '32 4294967295 x) y))
  :hints (("Goal" :use (:instance bvlt-of-plus-hack9)
           :in-theory (e/d (sbvlt-rewrite bvplus bvchop-of-sum-cases BVLT)
                           (;BVPLUS-OF-MINUS-1
                            bvlt-of-plus-hack9)))))

(defthm not-equal-min-int-when-not-sbvlt
  (implies (and (NOT (SBVLT '32 x free))
                (syntaxp (quotep free))
                (sbvlt 32 (expt 2 31) free))
           (not (equal 2147483648 (bvchop 32 x)))))

;gen the 4
(defthm sbvlt-of-bvmult-4-and-0
  (implies (and (not (sbvlt 32 x 0))
                (sbvlt 32 x 100000)) ;gen!
           (not (sbvlt '32 (bvmult '32 '4 x) '0)))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))

;if x<4 then 4x<16
(defthm sbvlt-of-bvmult-4-and-16
  (implies (and (not (sbvlt 32 x 0))
                (sbvlt 32 x 4))
           (sbvlt '32 (bvmult '32 '4 x) '16))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))


;todo: flesh out this theory fully
;could be expensive...
(defthm sbvlt-transitive-another
  (implies (and (not (sbvlt 32 free x))
                (sbvlt 32 free y))
           (sbvlt 32 x y)))

;in case we don't chose a normal form:
;TODO: Add other variants of this.  Or just choose a normal form...
(defthm <-of-logext-when-sbvlt
  (implies (and (syntaxp (quotep k))
                (signed-byte-p 32 k)
                (sbvlt 32 x free)
                (syntaxp (quotep free))
                (sbvle 32 free k))
           (< (logext 32 x) k))
  :hints (("Goal" :in-theory (e/d (sbvlt) (sbvlt-rewrite)))))

(defthm <-of-logext-when-not-sbvlt
  (implies (and (syntaxp (quotep k))
                (signed-byte-p 32 k)
                (not (sbvlt 32 free x))
                (syntaxp (quotep free))
                (sbvlt 32 free k))
           (< (logext 32 x) k))
  :hints (("Goal" :in-theory (e/d (sbvlt) (sbvlt-rewrite)))))

;we'll try leaving this version enabled
(defthm bvminus-becomes-bvplus-of-bvuminus-constant-version
  (implies (syntaxp (quotep y))
           (equal (bvminus size x y)
                  (bvplus size x (bvuminus size y))))
  :hints (("Goal" :in-theory (enable bvminus-becomes-bvplus-of-bvuminus))))

;; If you know n > k-1, then saying n>k is the same as saying n<>k
(defthm sbvlt-when-sbvlt-of-one-less
  (implies (and (syntaxp (quotep k))
                (syntaxp (want-to-weaken (sbvlt 32 k n)))
                (sbvlt 32 k2 n) ;k2 is a free var but below we require k2=k-1
                (syntaxp (quotep k2))
                (equal k2 (bvminus 32 k 1)) ;gets computed
                (sbvlt 32 (- (expt 2 31)) k) ;gets computed (no underflow)
                (unsigned-byte-p 32 k))
           (equal (sbvlt 32 k n)
                  (not (equal k (bvchop 32 n)))))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite bvlt bvplus bvchop-of-sum-cases))))



;; new stuff (file these into good libraries, but first file getbit-of-bvplus-split)

(defthm bvlt-false-when-bvlt-better
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (bvlt size free x) ; free < x
                (syntaxp (quotep free))
                (bvle size k (bvplus size 1 free)) ; k <= free+1, gets computed
                (posp size) ;todo gen
                )
           (not (bvlt size x k))) ; not(x < k), i.e., x>=k
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases bvplus))))

(defthm bvlt-of-bvplus-trim-special
  (implies (posp size)
           (equal (bvlt (+ -1 size) (bvplus size x y) z)
                  (bvlt (+ -1 size) (bvplus (+ -1 size) x y) z)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvlt-of-bvuminus-of-1 ;gen the 1
  (implies (natp size)
           (equal (bvlt size x (bvuminus size 1))
                  (not (bvle size -1 x))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvlt bvminus)
                                  (bvminus-becomes-bvplus-of-bvuminus-constant-version ;looped
                                   )))))

;todo: what is the existing bvlt-of-bvplus-of-1?
;seemed to cause problems
(defthmd bvlt-of-bvplus-of-1-gen
  (implies (natp size)
           (equal (bvlt size (bvplus size 1 x) y) ;x+1 < y
                  (if (EQUAL (BVCHOP SIZE X) (+ -1 (EXPT 2 SIZE)))
                      ;; overflow case:
                      (bvlt size 0 y)
                    (and (bvlt size x y)
                         (not (equal (bvplus size 1 x) (bvchop size y)))))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases bvplus))))

(defthm bvlt-of--1-arg2
  (equal (bvlt size x -1)
         (bvlt size x (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvlt))))

;todo replace sbvlt-false-when-sbvlt over in bresenham
(defthm sbvlt-false-when-sbvlt-gen
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (sbvlt size free x) ; free < x
                (syntaxp (quotep free))
                (sbvle size k (bvplus size 1 free)) ; k <= free+1, gets computed
                (posp size) ;todo gen
                )
           (not (sbvlt size x k))) ; not(x < k), i.e., x>=k
  :hints (("Goal" :in-theory (e/d (sbvlt-rewrite
                                   GETBIT-OF-BVPLUS-SPLIT
                                   ;BVLT-OF-BVUMINUS-ARG2
                                   posp
                                   bvlt-of-bvplus-of-1-gen
                                   )
                                  (bvlt-false-when-bvlt-better))
           :use (:instance bvlt-false-when-bvlt-better (size (+ -1 size))))))

(defthm <-of-bvchop-when-<-of-bvchop-shorter-cheap
  (implies (< (bvchop 31 x) (bvchop 31 y))
           (equal (< (bvchop 32 x) (bvchop 32 y))
                  (if (equal (getbit 31 x) 1)
                      (if (equal (getbit 31 y) 1)
                          t
                        nil)
                    t)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN))))

(defthm bvlt-when-sbvlt-cheap
  (implies (sbvlt 32 x y)
           (equal (bvlt 32 x y)
                  (not (and (sbvlt 32 x 0)
                            (sbvle 32 0 y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal"
           :use ((:instance SPLIT-BV (y (BVCHOP 32 X))
                            (n 32) (m 31))
                 (:instance SPLIT-BV (y (BVCHOP 32 y))
                            (n 32) (m 31)))
           :in-theory (e/d (sbvlt-rewrite bvlt)
                           (BVCAT-OF-GETBIT-AND-X-ADJACENT)))))

;; ;doesn't work?
;; (defthm bvlt-bound-forward-to-sbvlt-bound
;;   (implies (and (not (bvlt 32 x k))
;;                 (syntaxp (quotep k))
;;                 (bvlt 32 (expt 2 31) k)) ;gets computed
;;            (sbvlt 32 x 0))
;;   :rule-classes (:forward-chaining)
;;   :hints (("Goal" :in-theory (enable sbvlt-rewrite bvlt))))

;kind of a hack, but helps with the termination proof of a factorial
(defthm bvlt-of-huge
  (implies (syntaxp (want-to-weaken (bvlt 32 x 4294967294)))
           (equal (bvlt 32 x 4294967294)
                  (not (or (equal (bvchop 32 x) 4294967294)
                           (equal (bvchop 32 x) 4294967295)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;arises in measure proofs
(defthm <-of-bvminus-of-minus-1-and-bvminus-of-0
  (equal (< (bvminus 32 *minus-1* x) (bvminus 32 0 x))
         (not (equal (bvchop 32 x) 0)))
  :hints (("Goal" :in-theory (enable bvminus bvchop-of-sum-cases))))
