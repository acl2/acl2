; Support for proofs about R1CSes
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system)
(include-book "kestrel/prime-fields/rules2" :dir :system) ;reduce?
(include-book "kestrel/utilities/def-constant-opener" :dir :system) ;reduce?
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system) ;for fe-listp, todo: reduce
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv/rules4" :dir :system))
(local (include-book "kestrel/axe/rules3" :dir :system)) ; for bvchop-not-0-when-getbit-not-0

;; TODO: Oraganize this material

;; For when the constant is negative.  Not sure which normal form is better.
(defthmd pfield::mul-when-constant-becomes-neg-of-mul
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (integerp k)
                (posp p))
           (equal (mul k x p)
                  (neg (mul (neg k p) x p) p)
                  ))
  :hints (("Goal" :in-theory (enable mul neg sub))))

;(acl2::def-constant-opener neg)
;(acl2::def-constant-opener pfield::pos-fix)
(acl2::def-constant-opener unsigned-byte-p) ;todo: built into basic evaluator!
(acl2::def-constant-opener acl2::integer-range-p)

;;todo: use an axe-bind-free rule?
(defthm pfield::move-negation-1
  (implies (and (fep lhs p) ;gen?
                (integerp x2)
                (integerp x3)
                (integerp y)
                (integerp lhs)
                (posp p))
           (equal (equal lhs (add x1 (add x2 (add (neg y p) x3 p) p) p))
                  (equal (add lhs y p) (add x1 (add x2 x3 p) p)))))

;; Not sure which form is better
(defthmd pfield::add-of-neg-and-neg
  (implies (and (posp p)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (add (neg x p) (neg y p) p)
                  (neg (add x y p) p))))

(defthmd acl2::if-of-t-and-nil-when-booleanp
  (implies (booleanp x)
           (equal (if x t nil)
                  x)))

(defthm pfield::neg-of-mod
  (equal (neg (mod x p) p)
         (neg x p)))

;for axe
(defthm acl2::not-<-of-bvcat-and-0
  (not (< (acl2::bvcat highsize highval lowsize lowval) 0)))

;mixes prime fields and bvs
(defthm acl2::fep-of-bvcat
  (implies (and (< (expt 2 (+ highsize lowsize)) p)
                (natp highsize)
                (natp lowsize)
                (posp p))
           (fep (acl2::bvcat highsize highval lowsize lowval)
                p)))

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

;for acl2
(defthm pfield::fep-when-fe-listp-and-member-equal
  (implies (and (fe-listp free p)
                (acl2::member-equal x free))
           (fep x p)))

;for axe, since member-equal is not a known boolean, todo: why isn't that ok (can't make the axe rule)?
(defthm pfield::fep-when-fe-listp-and-memberp
  (implies (and (fe-listp free p)
                (acl2::memberp x free))
           (fep x p)))

(defun gen-fe-listp-assumption (vars prime)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))))
  `(fe-listp ,(acl2::make-append-with-key-nest vars) ,prime))

;; test: (gen-fe-listp-assumption '(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))

(local (include-book "kestrel/lists-light/member-equal" :dir :system)) ;for member-equal-of-cons
;test
(thm
 (implies (fe-listp
           (acl2::append-with-key
            'x5
            (acl2::append-with-key 'x2
                             (acl2::append-with-key 'x10
                                              (cons x1 nil)
                                              (cons x10 nil))
                             (acl2::append-with-key 'x3
                                              (cons x2 nil)
                                              (acl2::append-with-key 'x4
                                                               (cons x3 nil)
                                                               (cons x4 nil))))
            (acl2::append-with-key 'x7
                             (acl2::append-with-key 'x6
                                              (cons x5 nil)
                                              (cons x6 nil))
                             (acl2::append-with-key 'x8
                                              (cons x7 nil)
                                              (acl2::append-with-key 'x9
                                                               (cons x8 nil)
                                                               (cons x9 nil)))))
           prime)
          (and (fep x1 prime)
               (fep x2 prime)
               (fep x3 prime)
               (fep x4 prime)
               (fep x5 prime)
               (fep x6 prime)
               (fep x7 prime)
               (fep x8 prime)
               (fep x9 prime)
               (fep x10 prime)))
 :hints (("Goal" :in-theory (e/d (member-equal) (ACL2::MEMBER-EQUAL-BECOMES-MEMBERP)))))

(include-book "kestrel/axe/dag-arrays" :dir :system)
(include-book "kestrel/axe/axe-syntax" :dir :system)

(defun acl2::var-less-than-unquoted-keyp (var-darg key-darg acl2::dag-array)
  (declare (xargs :guard (and (or (acl2::myquotep var-darg)
                                  (and (natp var-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 var-darg))))
                              (or (acl2::myquotep key-darg)
                                  (and (natp key-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 key-darg)))))))
  (and (consp key-darg) ;checks for quotep
       (let ((unquoted-key (unquote key-darg)))
         (and (symbolp unquoted-key)
              (natp var-darg)
              (let ((var-expr (aref1 'acl2::dag-array acl2::dag-array var-darg)))
                (and (symbolp var-expr)
                     (symbol-< var-expr unquoted-key)))))))

(defun acl2::var-not-less-than-unquoted-keyp (var-darg key-darg acl2::dag-array)
  (declare (xargs :guard (and (or (acl2::myquotep var-darg)
                                  (and (natp var-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 var-darg))))
                              (or (acl2::myquotep key-darg)
                                  (and (natp key-darg)
                                       (acl2::pseudo-dag-arrayp 'acl2::dag-array acl2::dag-array (+ 1 key-darg)))))))
  (and (consp key-darg) ;checks for quotep
       (let ((unquoted-key (unquote key-darg)))
         (and (symbolp unquoted-key)
              (natp var-darg)
              (let ((var-expr (aref1 'acl2::dag-array acl2::dag-array var-darg)))
                (and (symbolp var-expr)
                     (not (symbol-< var-expr unquoted-key))))))))

;; Restrict the search for VAR to the branch (namely, X) where we know it is.
(defthm acl2::memberp-of-append-with-key-first-half-axe
  (implies (and (acl2::axe-syntaxp (acl2::var-less-than-unquoted-keyp var key acl2::dag-array))
                (acl2::memberp var x))
           (acl2::memberp var (acl2::append-with-key key x y)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))

;; Restrict the search for VAR to the branch (namely, Y) where we know it is.
(defthm acl2::memberp-of-append-with-key-second-half-axe
  (implies (and (acl2::axe-syntaxp (acl2::var-not-less-than-unquoted-keyp var key acl2::dag-array))
                (acl2::memberp var y))
           (acl2::memberp var (acl2::append-with-key key x y)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))

(defthm pfield::booleanp-of-fe-listp
  (booleanp (fe-listp elems prime)))


(defun acl2::bit-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (acl2::bitp (first x))
         (acl2::bit-listp (rest x)))))

(defthm acl2::bitp-when-bit-listp-and-memberp
  (implies (and (acl2::bit-listp free)
                (acl2::memberp x free))
           (acl2::bitp x)))

(defun gen-bit-listp-assumption (vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))))
  `(acl2::bit-listp ,(acl2::make-append-with-key-nest vars)))


;;  could let things happen earlier (before subst)?
(defthm bitp-when-equal-1
  (implies (and (equal x free)
                (bitp free))
           (bitp x)))

(defthm bitp-when-equal-2
  (implies (and (equal free x)
                (bitp free))
           (bitp x)))

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

(defthm bitxor-of-*-of-2 ;todo: gen the 2
  (implies (INTEGERP BIT2)
           (equal (ACL2::BITXOR BIT1 (* 2 BIT2))
                  (ACL2::BITXOR BIT1 0)))
  :hints (("Goal" :in-theory (e/d (acl2::bitxor acl2::bvxor) (ACL2::BVXOR-1-BECOMES-BITXOR)))))

(defthm getbit-of-1-and-+-of-2
  (implies (integerp x)
           (equal (acl2::getbit 1 (+ 2 x))
                  (acl2::bitnot (acl2::getbit 1 x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-1-of-+-of-*-of-2
  (implies (and (bitp bit1)
                (bitp bit2))
           (equal (ACL2::GETBIT 1 (+ BIT1 (* 2 BIT2)))
                  BIT2))
  :hints (("Goal" :cases ((equal bit2 1)))))

(defthmd bitnot-becomes-subtract
  (implies (bitp x)
           (equal (acl2::bitnot x)
                  (- 1 x)))
  :hints (("Goal" :cases ((equal 0 x)))))

(defthm add-of---arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (ADD x (- y) P)
                  (add x (neg y p) p)))
  :hints (("Goal" :in-theory (enable neg add))))

(defthm add-of---arg1
  (implies (and (integerp x)
                (integerp y))
           (equal (ADD (- x) y P)
                  (add (neg x p) y p)))
  :hints (("Goal" :in-theory (enable neg add))))


(defthm add-of---arg1-fixed
  (implies (and (syntaxp (not (quotep x))) ;defeat acl2 matching (- x) with a constant
                (integerp x)
                (integerp y))
           (equal (add (- x) y p)
                  (add (neg x p) y p)))
  :hints (("Goal" :in-theory (enable neg add))))

(defthm add-of---arg2-fixed
  (implies (and (syntaxp (not (quotep y))) ;defeat acl2 matching (- y) with a constant
                (integerp x)
                (integerp y))
           (equal (add x (- y) p)
                  (add x (neg y p) p)))
  :hints (("Goal" :in-theory (enable neg add))))

(in-theory (disable add-of---arg1
                    add-of---arg2))


(defthm getbit-of-+-of-constant-irrel
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal 0 (acl2::bvchop (+ 1 n) k))
                (natp n)
                (integerp x)
                (integerp k))
           (equal (acl2::getbit n (+ k x))
                  (acl2::getbit n x)))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-plus))))

(defthm getbit-of-+-of-expt-same-arg1
  (implies (and (natp n)
                (integerp x))
           (equal (acl2::getbit n (+ (expt 2 n) x))
                  (acl2::bitnot (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))


(defthm getbit-of-+-of-expt-same-arg2
  (implies (and (natp n)
                (integerp x))
           (equal (acl2::getbit n (+ x (expt 2 n)))
                  (acl2::bitnot (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

(defthm getbit-of-+-of-expt-same-when-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (equal k (expt 2 n))
                (natp n)
                (integerp x)
                (integerp k))
           (equal (acl2::getbit n (+ k x))
                  (acl2::bitnot (acl2::getbit n x))))
  :hints (("Goal" :use (getbit-of-+-of-expt-same-arg1)
           :in-theory (disable getbit-of-+-of-expt-same-arg1))))

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
                       (add (acl2::bvxor 2
                                         2 ;== b10 because bit 1 is negated and bit 0 is not
                                         (acl2::bvcat 1 bit2 1 bit1))
                            extra
                            p)
                       p)))
  :hints (("Goal" :in-theory (e/d (ACL2::BVXOR-BLAST
                                   acl2::bvcat
                                   acl2::logapp
                                   pfield::ADD-OF-+-ARG1
                                   pfield::ADD-OF-+-ARG2
                                   ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
                                   ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG2
                                   bitnot-becomes-subtract)
                                  (ACL2::BVCAT-OF-+-HIGH ;looped
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1)))))


(defthm bvxor-of-+-of-expt-of-one-less-arg2
  (implies (and (integerp x)
                (posp n))
           (equal (acl2::bvxor n extra (+ (expt 2 (+ -1 n)) x))
                  (acl2::bvcat 1
                               (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                           (acl2::getbit (- n 1) x)))
                               (- n 1)
                               (acl2::bvxor (- n 1) extra x)))))

(defthm bvxor-of-+-of-expt-of-one-less-arg1
  (implies (and (integerp x)
                (posp n))
           (equal (acl2::bvxor n (+ (expt 2 (+ -1 n)) x) extra)
                  (acl2::bvcat 1
                               (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                           (acl2::getbit (- n 1) x)))
                               (- n 1)
                               (acl2::bvxor (- n 1) extra x)))))

(defthm bvxor-of-+-of-expt-of-one-less-arg2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (integerp x)
                (posp n))
           (equal (acl2::bvxor n extra (+ k x))
                  (acl2::bvcat 1
                               (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                           (acl2::getbit (- n 1) x)))
                               (- n 1)
                               (acl2::bvxor (- n 1) extra x)))))

(defthm bvxor-of-+-of-expt-of-one-less-arg1-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (integerp x)
                (posp n))
           (equal (acl2::bvxor n (+ k x) extra)
                  (acl2::bvcat 1
                               (acl2::bitnot (acl2::bitxor (acl2::getbit (- n 1) extra)
                                                           (acl2::getbit (- n 1) x)))
                               (- n 1)
                               (acl2::bvxor (- n 1) extra x)))))

(defthm getbit-of-+-of-*-of-expt-when-bitp-arg2-arg1
  (implies (and (bitp bit)
                (integerp x)
                (natp n))
           (equal (acl2::getbit n (+ x (* (expt 2 n) bit)))
                  (acl2::bitxor bit (acl2::getbit n x))))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::bitnot)
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

(defthm bvxor-of-+-of-times-of-expt-same-arg3-arg2-arg1
  (implies (and ;(integerp x)
                (integerp y)
                (integerp z)
                (posp n))
           (equal (acl2::bvxor n x (+ y (* (expt 2 n) z)))
                  (acl2::bvxor n x y))))

(defthm bvxor-of-+-of-times-of-expt-same-arg3-arg2-arg2
  (implies (and ;(integerp x)
                (integerp y)
                (integerp z)
                (posp n))
           (equal (acl2::bvxor n x (+ y (* z (expt 2 n))))
                  (acl2::bvxor n x y))))

(defthm bvxor-of-+-of-times-of-expt-same-arg3-arg2-arg1-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (integerp x)
                (integerp y)
                (integerp z)
                (posp n))
           (equal (acl2::bvxor n x (+ y (* k z)))
                  (acl2::bvxor n x y))))

(defthmd bvxor-of-+-of-1-split
  (Implies (natp n)
           (equal (ACL2::BVXOR (+ 1 N) x y)
                  (acl2::bvcat 1 (acl2::bitxor (acl2::getbit n x) (acl2::getbit n y))
                               n (acl2::bvxor n x y)))))

(defthm bvxor-of-+-of-expt-2-same
  (implies (and (integerp x)
                (natp n))
           (equal (acl2::bvxor n (+ (expt 2 n) x) y)
                  (acl2::bvxor n x y))))

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
                                   acl2::logapp
                                   pfield::ADD-OF-+-ARG1
                                   pfield::ADD-OF-+-ARG2
                                   ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
                                   bitnot-becomes-subtract
                                   bvxor-of-+-of-1-split)
                                  (ACL2::BVCAT-OF-+-HIGH
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1
                                   ACL2::BVCAT-OF-*-LOW
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
                                   bitnot-becomes-subtract
                                   bvxor-of-+-of-1-split
                                   mul)
                                  (ACL2::BVCAT-OF-+-HIGH
                                   pfield::ADD-SAME-ARG1-ARG3
                                   ACL2::MOD-OF-MINUS-ARG1
                                   ACL2::BVCAT-OF-*-LOW
                                   ;PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE ;looped
                                   )))))

;todo: extra Z in rule ADD-OF-MUL-OF-POWER-OF-2

;; todo: these may allow us to first go to bvcats of bitnots before introducing xor masks:

;; try this last?  here, the y does not fit into the bvcat
(defthm add-of-mul-of-power-of-2-other
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

;; try this last?  here, the y does not fit into the bvcat
(defthm add-of-neg-of-mul-of-power-of-2-other
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
           :in-theory (enable bitp acl2::bvcat
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

(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
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
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special
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

(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p
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
                               acl2::<-of-bvcat))))

;; since for size 1 we'll have a bitp hyp
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-special
  (implies (and (bitp lowval)
                (natp highsize)
                (posp p))
           (equal (add lowval (acl2::bvcat highsize highval 1 0) p)
                  (mod (acl2::bvcat highsize highval 1 lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special))))

;swaps lowval and the bvcat
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
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
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
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

;swaps lowval and the bvcat
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-alt
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
                               acl2::<-of-bvcat))))

;swaps lowval and the bvcat
;; since for size 1 we'll have a bitp hyp
(defthm add-of-add-of-bvcat-of-0-when-unsigned-byte-p-special-alt
  (implies (and (bitp lowval)
                (natp highsize)
                (posp p))
           (equal (add (acl2::bvcat highsize highval 1 0) lowval p)
                  (mod (acl2::bvcat highsize highval 1 lowval) p)))
  :hints (("Goal" :use (:instance add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special (extra 0))
           :in-theory (disable add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special))))

(defthm add-commute-constant
  (implies (syntaxp (and (quotep k)
                         ;; avoid loops:
                         (not (quotep x))))
           (equal (add x (add k y p) p)
                  (add k (add x y p) p))))

(defthm not-of-if-of-nil-arg3-when-booleans
  (implies (and (booleanp x)
                (booleanp y))
           (equal (not (if x y nil)) ;; "not and"
                  (acl2::boolor (not x) (not y)))))

;; combines 2 steps, dropping the mod and dropping the ifix.
(defthm mod-of-ifix-when-fep
  (implies (fep x p)
           (equal (mod (ifix x) p)
                  x)))
