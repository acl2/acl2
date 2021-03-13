; Axe rules about BVs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;; This book includes rules that use axe-syntaxp, axe-bind-free, and
;;; axe-rewrite-objective.  They are for use with Axe but not with the ACL2
;;; Rewriter. Many of these are versions of pre-existing rules.

;; See also bv-rules-axe0.lisp.

;; TODO: Rename rules end in -dag to instead end in -axe.

(include-book "kestrel/bv/rules3" :dir :system) ;for SLICE-TIGHTEN-TOP
(include-book "kestrel/bv/rules6" :dir :system) ;for BVMULT-TIGHTEN
(include-book "bv-rules-axe0") ;drop?
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system) ;todo: make local
(include-book "axe-syntax-functions") ;for SYNTACTIC-CALL-OF
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

;move
(defthm <-of-integer-length-and-1
  (implies t;(integerp i)
           (equal (< (integer-length i) 1)
                  (or (not (integerp i))
                      (equal i 0)
                      (equal i -1))))
  :hints (("Goal" :in-theory (enable integer-length))))

;move
(defthm <-of-lg-and-0
  (implies (integerp i)
           (equal (< (lg i) 0)
                  (or (equal i 0)
                      (equal i -1))))
  :hints (("Goal" :in-theory (enable lg))))



(add-known-boolean bvlt)
(add-known-boolean sbvlt)
(add-known-boolean bvle)
(add-known-boolean sbvle)
(add-known-boolean unsigned-byte-p-forced)

(defthmd floor-when-usb-bind-free-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (natp n)
                (unsigned-byte-p-forced xsize x))
           (equal (floor x (expt 2 n))
                  (slice (+ -1 xsize) n x)))
  :hints
  (("Goal" :expand ((slice (+ -1 xsize) n x))
    :in-theory (e/d (unsigned-byte-p-forced
                     natp slice
                     logtail unsigned-byte-p ;floor-bounded-by-/
                     )
                    (anti-slice bvchop-of-floor-of-expt-of-2)))))

(defthmd floor-when-usb-bind-free-dag-constant-version
  (implies (and (power-of-2p k)
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x)
                )
           (equal (floor x k)
                  (slice (+ -1 xsize) (lg k) x)))
  :hints (("Goal" :use (:instance floor-when-usb-bind-free-dag (n (lg k)))
           :in-theory (e/d (power-of-2p) (floor-when-usb-bind-free-dag)))))

(defthmd bvnot-trim-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitnot-trim-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitnot x)
                  (bitnot (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-trim-arg1-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitand x y)
                  (bitand (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-trim-arg2-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitand y x)
                  (bitand y (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-trim-arg1-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitor x y)
                  (bitor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-trim-arg2-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitor y x)
                  (bitor y (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvminus-trim-arg1-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvminus size x y)
                  (bvminus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvminus-trim-arg2-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvminus size y x)
                  (bvminus size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvuminus-trim-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (< 0 size) ;drop
                (integerp size)
                (integerp x) ;drop
                )
           (equal (bvuminus size x)
                  (bvuminus size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd slice-trim-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe-plus-one high x 'all dag-array))
                (<= low high)
                (natp low)
                (natp high))
           (equal (slice high low x)
                  (slice high low (trim (+ 1 high) x))))
  :hints (("Goal" :in-theory (enable trim))))

;here's a loop if we did it when n=0
;; (bvchop 1 (slice 3 2 x))
;; (GETBIT 0 (SLICE 3 2 X))
;; (GETBIT 0 (bvchop 1 (SLICE 3 2 X)))
(defthmd getbit-trim-dag-all
  (implies (and (< 0 n) ;if n=0 it's already being trimmed by the getbit (BOZO make sure we can simplify such cases..)
                (axe-syntaxp (term-should-be-trimmed-axe-plus-one n x 'all dag-array))
                (integerp n))
           (equal (getbit n x)
                  (getbit n (trim (+ 1 n) x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd getbit-trim-dag-all-gen
  (implies (and (<= 0 n)
                (axe-syntaxp (term-should-be-trimmed-axe-plus-one n x 'all dag-array))
                (integerp n))
           (equal (getbit n x)
                  (getbit n (trim (+ 1 n) x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg1-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe highsize highval 'non-arithmetic dag-array))
                (natp highsize)
                (natp lowsize) ;drop?
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg2-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe lowsize lowval 'non-arithmetic dag-array))
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg1-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe highsize highval 'all dag-array))
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg2-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe lowsize lowval 'all dag-array))
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-trim-arg1-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-trim-arg2-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size y 'non-arithmetic dag-array))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-trim-arg1-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (e/d (trim)
                                  ()))))

(defthmd bvplus-trim-arg2-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (e/d (trim)
                                  ()))))

(defthmd bvxor-trim-arg1-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvxor size x y)
                  (bvxor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-trim-arg2-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvxor size y x)
                  (bvxor size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg1-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvif size test x y)
                  (bvif size test (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg2-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvif size test y x)
                  (bvif size test y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg1-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvif size test x y)
                  (bvif size test (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg2-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvif size test y x)
                  (bvif size test y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg1-dag
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvand size x y)
                  (bvand size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg2-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvand size y x)
                  (bvand size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg1-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvand size x y)
                  (bvand size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg2-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvand size y x)
                  (bvand size y (trim size x))))
  :hints
  (("Goal" :in-theory (enable trim))))

(defthmd bvor-trim-arg1-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvor size x y)
                  (bvor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvor-trim-arg2-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvor size y x)
                  (bvor size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-trim-arg1-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitxor x y)
                  (bitxor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-trim-arg2-dag-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 y 'all dag-array))
           (equal (bitxor x y)
                  (bitxor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg1-dag
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size (trim size x) y)))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg2-dag
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'non-arithmetic dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size x (trim size y))))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg1-dag-all
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size (trim size x) y)))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg2-dag-all
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size x (trim size y))))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-trim-arg1-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvxor size x y)
                  (bvxor size (trim size x) y)))
  :hints (("Goal" :in-theory (e/d (trim)
                                  ()))))

(defthmd bvxor-trim-arg2-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvxor size y x)
                  (bvxor size y (trim size x))))
  :hints (("Goal" :in-theory (e/d (trim)
                                  ()))))

;;TODO: add rules for sbvdiv and sbvrem

;rename these?!
(defthmd bvdiv-trim-arg1-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvdiv size x y)
                  (bvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-trim-arg2-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvdiv size y x)
                  (bvdiv size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-trim-arg1-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvdiv size x y)
                  (bvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-trim-arg2-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvdiv size y x)
                  (bvdiv size y (trim size x))))
  :hints (("Goal":in-theory (enable trim))))

(defthmd bvlt-trim-arg1-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvlt-trim-arg2-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
                (natp size))
           (equal (bvlt size x y)
                  (bvlt size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmod-trim-arg1-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvmod size x y)
                  (bvmod size (trim size x) y)))
  :hints(("Goal" :in-theory (enable trim))))

(defthmd bvmod-trim-arg2-dag-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvmod size y x)
                  (bvmod size y (trim size x))))
  :hints(("Goal" :in-theory (enable trim))))

(defthmd bvchop-identity-axe
  (implies (and (axe-bind-free (bind-bv-size-axe i 'isize dag-array) '(isize))
                (<= isize size)
                (integerp size)
                (unsigned-byte-p-forced isize i))
           (equal (bvchop size i)
                  i))
  :hints (("Goal" :expand ((:with unsigned-byte-p (unsigned-byte-p isize i)))
           :in-theory (e/d (unsigned-byte-p-forced) ( size-non-negative-when-unsigned-byte-p-free)))))

(defthmd bvcat-tighten-upper-size-dag
  (implies (and (axe-bind-free (bind-bv-size-axe highval 'newsize dag-array) '(newsize)) ;had x instead of highval, that should be an error
                (< 0 newsize) ;allow 0?
                (< newsize highsize)
                (integerp newsize)
                (integerp highsize)
                (unsigned-byte-p-forced newsize highval))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat newsize highval lowsize lowval)))
  :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (bvcat UNSIGNED-BYTE-P-FORCED) (bvcat-recombine)))))

;or should we bring heavier terms to the front to increase sharing?
;ffixme these differe from what simplify-bitxors does in terms of the order of terms?!
(defthmd bitxor-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bitxor x y dag-array))
           (equal (bitxor x y)
                  (bitxor y x))))

(defthmd bitxor-commutative-increasing-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bitxor x y dag-array))
           (equal (bitxor x y)
                  (bitxor y x))))

(defthmd bitxor-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bitxor x y dag-array))
           (equal (bitxor x (bitxor y z))
                  (bitxor y (bitxor x z)))))

(defthmd bitxor-commutative-2-increasing-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bitxor x y dag-array))
           (equal (bitxor x (bitxor y z))
                  (bitxor y (bitxor x z)))))

;;; bvxor

;rename to bvxor-commutative-increasing-dag
(defthmd bvxor-commutative-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bvxor x y dag-array))
           (equal (bvxor size x y)
                  (bvxor size y x)))
  :hints (("Goal" :use (:instance bvxor-commutative)
           :in-theory (disable bvxor-commutative))))

;rename to bvxor-commutative-dag
(defthmd bvxor-commutative-dag-old
  (implies (axe-syntaxp (should-commute-args-dag 'bvxor x y dag-array))
           (equal (bvxor size x y)
                  (bvxor size y x)))
  :hints (("Goal" :use (:instance bvxor-commutative)
           :in-theory (disable bvxor-commutative))))

;rename to bvxor-commutative-2-increasing-dag
(defthmd bvxor-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bvxor x y dag-array))
           (equal (bvxor size x (bvxor size y z))
                  (bvxor size y (bvxor size x z))))
  :hints (("Goal" :use (:instance bvxor-commutative-2)
           :in-theory (disable bvxor-commutative-2))))

;rename to bvxor-commutative-2-dag
(defthmd bvxor-commutative-2-dag-old
  (implies (axe-syntaxp (should-commute-args-dag 'bvxor x y dag-array))
           (equal (bvxor size x (bvxor size y z))
                  (bvxor size y (bvxor size x z))))
  :hints (("Goal" :use (:instance bvxor-commutative-2)
           :in-theory (disable bvxor-commutative-2))))

;;; bvand

(defthmd bvand-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvand x y dag-array))
           (equal (bvand size x y)
                  (bvand size y x)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd bvand-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvand y x dag-array))
           (equal (bvand size y (bvand size x z))
                  (bvand size x (bvand size y z))))
  :hints (("Goal" :use (:instance bvand-commutative-2)
           :in-theory (disable bvand-commutative-2))))

;;; bvor

(defthmd bvor-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvor x y dag-array))
           (equal (bvor size x y)
                  (bvor size y x)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd bvor-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvor y x dag-array))
           (equal (bvor size y (bvor size x z))
                  (bvor size x (bvor size y z))))
  :hints (("Goal" :use (:instance bvor-commutative-2)
           :in-theory (disable bvor-commutative-2))))

;;; bvplus

(defthmd bvplus-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvplus x y dag-array))
           (equal (bvplus size x y)
                  (bvplus size y x))))

(defthmd bvplus-commutative-increasing-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bvplus x y dag-array))
           (equal (bvplus size x y)
                  (bvplus size y x))))

(defthmd bvplus-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvplus x y dag-array))
           (equal (bvplus size x (bvplus size y z))
                  (bvplus size y (bvplus size x z)))))

(defthmd bvplus-commutative-2-increasing-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bvplus x y dag-array))
           (equal (bvplus size x (bvplus size y z))
                  (bvplus size y (bvplus size x z)))))

;;; bvmult

(defthmd bvmult-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvmult x y dag-array))
           (equal (bvmult size x y)
                  (bvmult size y x))))

(defthmd bvmult-commutative-increasing-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bvmult x y dag-array))
           (equal (bvmult size x y)
                  (bvmult size y x))))

(defthmd bvmult-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bvmult x y dag-array))
           (equal (bvmult size x (bvmult size y z))
                  (bvmult size y (bvmult size x z))))
  :hints (("Goal" :in-theory (enable))))

(defthmd bvmult-commutative-2-increasing-dag
  (implies (axe-syntaxp (should-commute-args-increasing-dag 'bvmult x y dag-array))
           (equal (bvmult size x (bvmult size y z))
                  (bvmult size y (bvmult size x z))))
  :hints (("Goal" :in-theory (enable))))

(defthmd getbit-identity-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= xsize 1) ;okay when xsize is 0?
                ;(natp xsize) ;can drop because of the usb hyp?
                (unsigned-byte-p-forced xsize x))
           (equal (getbit 0 x)
                  x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthmd getbit-too-high-is-0-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= xsize n)
                (integerp n)
                (unsigned-byte-p-forced xsize x))
           (equal (getbit n x)
                  0))
  :hints (("Goal" :cases ((integerp n))
           :in-theory (enable getbit-too-high unsigned-byte-p-forced))))

;fixme ignore bitxor with 1?
(defthmd bitand-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bitand x y dag-array))
           (equal (bitand x y)
                  (bitand y x))))

;fixme ignore bitxor with 1?
(defthmd bitand-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bitand x y dag-array))
           (equal (bitand x (bitand y z))
                  (bitand y (bitand x z))))
  :hints (("Goal" :use (:instance bitand-commutative-2))))

(defthmd bitor-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bitor x y dag-array))
           (equal (bitor x y)
                  (bitor y x))))

(defthmd bitor-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'bitor x y dag-array))
           (equal (bitor x (bitor y z))
                  (bitor y (bitor x z))))
  :hints (("Goal" :use (:instance bitor-commutative-2))))

(defthmd +-commutative-dag
  (implies (axe-syntaxp (should-commute-args-dag 'binary-+ x y dag-array))
           (equal (+ x y)
                  (+ y x))))

(defthmd +-commutative-2-dag
  (implies (axe-syntaxp (should-commute-args-dag 'binary-+ x y dag-array))
           (equal (+ x (+ y z))
                  (+ y (+ x z))))
  :hints (("Goal" :in-theory (enable))))

(defthmd myif-becomes-bvif
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

(defthmd myif-becomes-bvif-2
  (implies (and (unsigned-byte-p xsize x) ;xsize is a free variable
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y))
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

(defthmd myif-becomes-bvif-3
  (implies (and (unsigned-byte-p xsize x) ;xsize is a free variable
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y))
           (equal (myif test y x)
                  (bvif (max xsize ysize) test y x)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

(defthmd slice-too-high-is-0-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= xsize low)
                ;(natp xsize)
                (natp low)
                (unsigned-byte-p-forced xsize x))
           (equal (slice high low x)
                  0))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0 unsigned-byte-p-forced))))

;
; converting < to bvlt :
;

;cheap
(defthmd <-becomes-bvlt-dag-both
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (< x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt (k x) (x y)  (free (max xsize ysize))))))

;cheap
(defthmd <-becomes-bvlt-dag-2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p freeysize y)
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (bvlt (max xsize freeysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvlt))))

;cheap
(defthmd <-becomes-bvlt-dag-3
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p freexsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (< x y)
                  (bvlt (max freexsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvlt))))



(local (in-theory (disable ;BVPLUS-RECOLLAPSE
                   ;;hack-6
                   )))


;fixme what if there are assumptions of usb for x and/or y
;gen the 32
(defthmd sbvlt-becomes-bvlt-cheap
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< ysize 32)
                (< xsize 32)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                )
           (equal (sbvlt 32 x y)
                  ;;could use the max of the sizes? ;
                  (bvlt 31 x y)))
  :hints (("Goal" :in-theory (enable ;sbvlt
                              sbvlt-rewrite
                              UNSIGNED-BYTE-P-FORCED
                              bvlt))))

;gen the 32
(defthmd sbvlt-becomes-bvlt-cheap-1
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< ysize 32)
                (unsigned-byte-p xsize x) ;xsize is a free var
                (< xsize 32)
                (unsigned-byte-p-forced ysize y))
           (equal (sbvlt 32 x y)
                  ;;could use the max of the sizes? ;
                  (bvlt 31 x y)))
  :hints (("Goal" :use (:instance sbvlt-becomes-bvlt-cheap)
           :in-theory (e/d (unsigned-byte-p-forced)( sbvlt-becomes-bvlt-cheap)))))

;gen the 32
(defthmd sbvlt-becomes-bvlt-cheap-2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize 32)
                (unsigned-byte-p ysize y) ;ysize is a free var
                (< ysize 32)
                (unsigned-byte-p-forced xsize x))
           (equal (sbvlt 32 x y)
                  ;;could use the max of the sizes? ;
                  (bvlt 31 x y)))
  :hints (("Goal" :use (:instance sbvlt-becomes-bvlt-cheap)
           :in-theory (e/d (unsigned-byte-p-forced)( sbvlt-becomes-bvlt-cheap)))))

(defthm equal-constant-when-unsigned-byte-p-bind-free-dag
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (syntaxp (quotep xsize))
                (not (unsigned-byte-p xsize k))
                (unsigned-byte-p-forced xsize x))
           (equal (equal k x)
                  nil))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)))
  :rule-classes nil)

;fixme more rules like this?
(defthmd mod-becomes-bvmod
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y)
                (unsigned-byte-p ysize x) ;new..
                )
           (equal (mod x y)
                  (bvmod ysize x y)))
  :hints (("Goal" :in-theory (enable mod-becomes-bvmod-core unsigned-byte-p-forced))))

(defthmd mod-becomes-bvmod-better-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-core (size (max xsize ysize)))
           :in-theory (enable ;mod-becomes-bvmod-core
                       unsigned-byte-p-forced))))

(defthmd mod-becomes-bvmod-better-bind-free-and-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p ysize y)) ;ysize is a freevar
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-core (size (max xsize ysize)))
           :in-theory (enable ;mod-becomes-bvmod-core
                       unsigned-byte-p-forced))))

(defthmd mod-becomes-bvmod-better-free-and-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y)
                (unsigned-byte-p xsize x)) ;xsize is a freevar
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-core (size (max xsize ysize)))
           :in-theory (enable ;mod-becomes-bvmod-core
                       unsigned-byte-p-forced))))

;a cheap case of logext-identity
(defthmd logext-identity-when-usb-smaller-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size2 dag-array) '(size2))
                (< size2 n)
                (unsigned-byte-p-forced size2 x)
                (natp n)
                (natp size2))
           (equal (logext n x)
                  x))
  :hints (("Goal"
           :use (:instance logext-when-usb-cheap (i x) (free size2) (size n))
           :in-theory (e/d (UNSIGNED-BYTE-P-FORCED) (logext-when-usb-cheap)))))

;rename axe-
(defthmd rationalp-when-bv-operator
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (rationalp x)
                  t))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

;rename axe-
(defthmd acl2-numberp-when-bv-operator
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (acl2-numberp x)
                  t))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

;fixme more like this for other ops?!
(defthmd bvxor-tighten-axe-bind-and-bind
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (max xsize ysize) size)
                (natp size)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (bvxor size x y)
                  (bvxor (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance BVXOR-TIGHTEN (oldsize size) (newsize (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

;fixme if bind-free functions could take the assumptions we could make a version of this rule that covers the combinations of obvious sizes and sizes from usb hyps
(defthmd bvxor-tighten-axe-bind-and-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y) ;ysize is free
                (< (max xsize ysize) size)
                (natp size)
                (unsigned-byte-p-forced xsize x)
                )
           (equal (bvxor size x y)
                  (bvxor (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance BVXOR-TIGHTEN (oldsize size) (newsize (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

(defthmd bvxor-tighten-axe-free-and-bind
  (implies (and (unsigned-byte-p xsize x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (max xsize ysize) size)
                (natp size)
                (unsigned-byte-p-forced ysize y))
           (equal (bvxor size x y)
                  (bvxor (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance BVXOR-TIGHTEN (oldsize size) (newsize (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

;fixme make -core versions of these...

(defthmd unsigned-byte-p-from-bound-constant-version-axe
  (implies (and (axe-rewrite-objective 't)
                (< x free)
                (syntaxp (quotep free))
                (syntaxp (quotep n))
                (<= free (expt 2 n)))
           (equal (unsigned-byte-p n x)
                  (and (<= 0 x)
                       (integerp x)
                       (integerp n)
                       (<= 0 n))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;ex: strengthen x<4 to x<=3
(defthmd bvlt-of-constant-arg3
  (implies (and (axe-rewrite-objective 'nil)
                (not (equal 0 (bvchop size k)))
                (integerp k)
                ;(natp size)
                )
           (equal (bvlt size x k)
                  (not (bvlt size (+ -1 k) x))))
  :hints (("Goal" :cases ((Natp size))
           :in-theory (e/d (bvlt bvchop-of-sum-cases) (BVLT-OF-PLUS-ARG1)))))

;ex: strengthen 10<x to 11<=x
(defthmd bvlt-of-constant-arg2
  (implies (and (axe-rewrite-objective 'nil)
                (not (equal (+ -1 (expt 2 size)) (bvchop size k)))
                (natp size)
                (integerp k))
           (equal (bvlt size k x)
                  (not (bvlt size x (+ 1 k)))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases) (BVLT-OF-PLUS-ARG2)))))

(defthmd bvlt-of-max-arg3
  (implies (and (axe-rewrite-objective 't)
                (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvlt size x k)
                  (not (equal k (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;other versions?
(defthmd bvlt-when-bvlt-must-be-fake-free-axe
  (implies (and (axe-rewrite-objective 't)
                (not (bvlt free y x)) ;this free var is because the dag rewriter and dag prover dont support backchain limits
                (equal free size) ;fixme gen?
                )
           (equal (bvlt size x y)
                  (not (equal (bvchop size y)
                              (bvchop size x)))))
  :hints (("Goal" :in-theory (e/d (bvlt) ()))))

(defthmd bvlt-when-bvlt-must-be-gen-axe
  (implies (and (axe-rewrite-objective 't)
                (syntaxp (quotep x))
                (not (bvlt freesize y x))
                (syntaxp (quotep freesize))
                (<= freesize size)
                (unsigned-byte-p freesize x) ;gets evaluated
                (integerp size))
           (equal (bvlt size x y)
                  (not (equal (bvchop size y)
                              (bvchop size x)))))
  :hints (("Goal" :use (:instance bvlt-when-bvlt-must-be-gen))))

;could use natp-forced
;alt version?
(defthmd <-of-negative-constant-and-bv
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (< k x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthmd <-of-bv-and-non-positive-constant
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (not (< x k)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))


(defthmd bvlt-of-constant-when-too-narrow
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= (expt 2 xsize) (bvchop size k))
                (<= xsize size)
                (natp size)
                (unsigned-byte-p-forced xsize x)
                )
           (equal (bvlt size x k)
                  t))
  :hints (("Goal" :in-theory (enable bvlt unsigned-byte-p-forced))))

(defthmd trim-does-nothing-dag
  (implies (and (axe-bind-free (bind-bv-size-axe i 'isize dag-array) '(isize))
                (<= isize size)
                (unsigned-byte-p-forced isize i)
                (integerp size)
                )
           (equal (trim size i)
                  i))
  :hints (("Goal" :in-theory (enable trim unsigned-byte-p-forced))))

(defthmd bvlt-when-bound-dag
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (natp size)
                (bvle size (expt 2 xsize) k)
                (unsigned-byte-p-forced xsize x))
           (equal (bvlt size x k)
                  t))
  :hints (("Goal" :use (:instance bvlt-when-bound)
           :in-theory (disable bvlt-when-bound))))

(defthmd bvmod-tighten-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (max xsize ysize) size)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                (natp size)
                (posp xsize))
           (equal (bvmod size x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance bvmod-tighten)
           :in-theory (disable bvmod-tighten))))

(defthmd bvmod-tighten-dag-free-1
  (implies (and (unsigned-byte-p xsize x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (max xsize ysize) size)
                (unsigned-byte-p-forced ysize y)
                (natp size)
                (posp xsize))
           (equal (bvmod size x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance bvmod-tighten)
           :in-theory (e/d (UNSIGNED-BYTE-P-FORCED)( bvmod-tighten)))))

(defthmd bvmult-tighten-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (+ xsize ysize) size)
                (natp size)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (bvmult size x y)
                  (bvmult (+ xsize ysize) x y)))
  :hints (("Goal" :use (:instance bvmult-tighten)
           :in-theory (disable bvmult-tighten))))

(defthm not-equal-nil-when-syntactically-a-bv-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (not (equal nil x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

;bozo gen
(defthmd rightrotate32-trim-amt-dag
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '5 amt 'non-arithmetic dag-array))
                (natp amt))
           (equal (rightrotate32 amt x)
                  (rightrotate32 (trim 5 amt) x)))
  :hints (("Goal" :in-theory (e/d (rightrotate32 rightrotate leftrotate trim MOD-OF-EXPT-OF-2-CONSTANT-VERSION) ()))))


(defthm cancel-<-+
  (equal (< (+ k x) x)
         (< k 0)))

;todo: move these up?
(include-book "kestrel/bv/rules" :dir :system)
(local (include-book "arithmetic/equalities" :dir :system))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
(local (include-book "ihs/math-lemmas" :dir :system))
;(local (include-book "kestrel/lists-light/update-nth" :dir :system))
;(local (include-book "kestrel/lists-light/firstn" :dir :system))


;drop? rename?
(defthmd logtail-becomes-slice-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'newsize dag-array) '(newsize))
                (<= n newsize) ;drop?
                (integerp newsize)
                (unsigned-byte-p-forced newsize x) ;switched to usb-forced? (also elsewhere!)
                (integerp x) ;drop
                (natp n))
           (equal (LOGTAIL N X)
                  (slice (+ -1 newsize) n x)))
  :hints (("Goal" :use (:instance LOGTAIL-BECOMES-SLICE-BIND-FREE)
           :in-theory (e/d (unsigned-byte-p-forced)(LOGTAIL-BECOMES-SLICE-BIND-FREE)))))

(defthmd leftrotate32-trim-amt
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '5 amt 'non-arithmetic dag-array))
                (natp amt))
           (equal (leftrotate32 amt val)
                  (leftrotate32 (trim 5 amt) val)))
  :hints (("Goal" :in-theory (e/d (trim) (MOD-OF-EXPT-OF-2-CONSTANT-VERSION ;looped with imod when things were enabled?
                                          leftrotate32 ;disable globally?
                                          )))))

;for this not to loop, we must simplify things like (bvchop 5 (bvplus 32 x y))
(defthmd leftrotate32-trim-amt-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '5 amt 'all dag-array))
                (natp amt))
           (equal (leftrotate32 amt val)
                  (leftrotate32 (trim 5 amt) val)))
  :hints (("Goal" :in-theory (e/d (trim) (MOD-OF-EXPT-OF-2-CONSTANT-VERSION
                                          leftrotate32 ;disable globally?
                                          )))))

(defthmd bvcat-blast-low
  (implies (and (axe-syntaxp (not-quotep lowval)) ;prevents loops ;Fri Mar  4 20:18:21 2011
                (axe-syntaxp (not (syntactic-call-of 'bvcat lowval dag-array)));Thu Mar  3 01:52:18 2011
                (< 1 lowsize) ;prevents loops
                (integerp highsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize
                         highval
                         lowsize
                         (bvcat 1
                                (getbit (+ -1 lowsize) lowval)
                                (+ -1 lowsize)
                                lowval))))
  :hints (("Goal" :in-theory (enable natp))))


;rename
(defthmd bvxor-smaller-term-becomes-cat-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size2 dag-array) '(size2))
                (< size2 size)
                (unsigned-byte-p-forced size2 x)
                (natp size2)
                (integerp size)
                )
           (equal (bvxor size x y)
                  (bvcat (- size size2)
                         (slice (+ -1 size) size2 y)
                         size2
                         (bvxor size2 x y))))
  :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0 unsigned-byte-p-forced))))

;rename
(defthmd bvxor-smaller-term-becomes-cat-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size2 dag-array) '(size2))
                (< size2 size)
                (unsigned-byte-p-forced size2 x)
                (natp size2)
                (integerp size)
                )
           (equal (bvxor size y x)
                  (bvcat (- size size2)
                         (slice (+ -1 size) size2 y)
                         size2
                         (bvxor size2 y x))))
  :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0 unsigned-byte-p-forced))))


;this fires on (bvor x (bvchop 8 y)) but what if y is an 8-bit var and we drop the logherad from it
;might be better to discover that x is a bvcat with 0's at the bottom
;for or, wouldn't it be better to just split the or into a cat of the top part of x
(defthmd bvplus-disjoint-ones-arg2-gen
   (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                 (< size2 size)
                 (equal 0 (bvchop size2 x))
                 (unsigned-byte-p-forced size2 y)
                 (natp size)
                 (natp size2))
            (equal (bvplus size x y)
                   (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
   :hints (("Goal" :expand ((SLICE (+ -1 SIZE) SIZE2 (+ X Y)))
            :in-theory (e/d (SLICE BVPLUS SLICE-TOO-HIGH-IS-0 SLICE-WHEN-VAL-IS-NOT-AN-INTEGER LOGTAIL-OF-BVCHOP unsigned-byte-p-forced)
                            (;anti-bvplus
                             LOGTAIL-OF-BVCHOP-BECOMES-SLICE BVCHOP-OF-LOGTAIL-BECOMES-SLICE SLICE-BECOMES-BVCHOP BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                                              BVCHOP-OF-LOGTAIL)))))

(local (in-theory (enable unsigned-byte-p-forced)))

(defthmd bvor-with-small-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (natp size)
                (< 0 size)
                (natp xsize)
                (integerp x) ;drop
                (integerp y) ;drop
                (unsigned-byte-p-forced xsize x)
                )
           (equal (bvor size x y)
                  (bvcat (- size xsize)
                         (slice (+ -1 size) xsize y)
                         xsize
                         (bvor xsize x y))))
  :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

(defthmd bvor-with-small-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (natp size)
                (< 0 size)
                (natp xsize)
                (integerp x) ;drop
                (integerp y) ;drop
                (unsigned-byte-p-forced xsize x)
                )
           (equal (bvor size y x)
                  (bvcat (- size xsize)
                         (slice (+ -1 size) xsize y)
                         xsize
                         (bvor xsize y x))))
    :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

;; (defthmd bvxor-with-small-arg1
;;   (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;                 (< xsize size)
;;                 (unsigned-byte-p xsize x)
;;                 (natp size)
;;                 (< 0 size)
;;                 (natp xsize)
;;                 (integerp x) ;drop
;;                 (integerp y) ;drop
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvcat (- size xsize)
;;                          (slice (+ -1 size) xsize y)
;;                          xsize
;;                          (bvxor xsize x y))))
;;   :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

;; (defthmd bvxor-with-small-arg2
;;   (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;                 (< xsize size)
;;                 (unsigned-byte-p xsize x)
;;                 (natp size)
;;                 (< 0 size)
;;                 (natp xsize)
;;                 (integerp x) ;drop
;;                 (integerp y) ;drop
;;                 )
;;            (equal (bvxor size y x)
;;                   (bvcat (- size xsize)
;;                          (slice (+ -1 size) xsize y)
;;                          xsize
;;                          (bvxor xsize y x))))
;;       :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

;; ;shoot.  can't conveniently pass in size+1
;; (defthm slice-trim-arg2
;;   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'non-arithmetic dag-array))
;;                 (natp size))
;;            (equal (slice high low x)
;;                   (slice high low (bvchop + 1 high) x)))
;;   :hints (("Goal" :in-theory (e/d (bvplus BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (anti-bvplus)))))

(defthmd bvif-with-small-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (< 0 xsize) ;otherwise it looped!  bozo add this to similar rules

                (natp size)
                (< 0 size)
                (natp xsize)
                (integerp x) ;drop
                (integerp y) ;drop
                (unsigned-byte-p-forced xsize x)
                )
           (equal (bvif size test x y)
                  (bvcat (- size xsize)
                         (bvif (- size xsize) test 0 (slice (+ -1 size) xsize y))
                         xsize
                         (bvif xsize test x y))))
  :hints (("Goal" :in-theory (enable bvif myif GETBIT-TOO-HIGH))))

(defthmd bvif-with-small-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (< 0 xsize) ;otherwise it looped!  bozo add this to similar rules
                (natp size)
                (< 0 size)
                (natp xsize)
                (integerp x) ;drop
                (integerp y) ;drop
                (unsigned-byte-p-forced xsize x)
                )
           (equal (bvif size test y x)
                  (bvcat (- size xsize)
                         (bvif (- size xsize) test (slice (+ -1 size) xsize y) 0)
                         xsize
                         (bvif xsize test y x))))
  :hints (("Goal" :in-theory (enable bvif myif GETBIT-TOO-HIGH))))

(defthmd bvif-tighten
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< xsize size)
                (< ysize size)
;;                 (< 0 xsize)
;;                 (< 0 ysize)
                (natp size)
                (< 0 size)
                (natp xsize)
                (natp ysize)
                (integerp x)
                (integerp y)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (bvif size test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif getbit-too-high))))

(defthmd slice-tighten-top-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= xsize high)
                (natp low)
                (natp xsize)
                (natp high)
                (unsigned-byte-p-forced xsize x))
           (equal (slice high low x)
                  (slice (+ -1 xsize) low x)))
  :hints (("Goal" :use (:instance slice-tighten-top)
           :in-theory (disable slice-tighten-top))))

(defthmd bvand-with-small-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (natp size)
                (unsigned-byte-p-forced xsize x))
           (equal (bvand size x y)
                  (bvand xsize x y)))
  :hints (("Goal" :cases ((integerp y))
           :in-theory (enable BVAND logand-bvchop-when-usb))))

(defthmd bvand-with-small-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize size)
                (natp size)
                (< 0 size)
                (unsigned-byte-p-forced xsize x))
           (equal (bvand size y x)
                  (bvand xsize y x)))
  :hints (("Goal" :use (:instance bvand-with-small-arg1))))

(defthmd bvor-disjoint-ones-arg2-gen
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (axe-syntaxp (bvcat-nest-with-low-zeros x size2 dag-array)) ;new
                (< size2 size)
                (equal 0 (bvchop size2 x))
                (unsigned-byte-p-forced size2 y)
                (natp size)
                (natp size2))
           (equal (bvor size x y)
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :in-theory (e/d (BVOR SLICE-TOO-HIGH-IS-0) ()))))

(defthmd bvplus-disjoint-ones-arg1-gen
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (< size2 size)
                (equal 0 (bvchop size2 x))
                (unsigned-byte-p-forced size2 y)
                (natp size)
                (natp size2))
           (equal (bvplus size y x)
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :use (:instance bvplus-disjoint-ones-arg2-gen)
           :in-theory (disable bvplus-disjoint-ones-arg2-gen))))

(defthmd bvplus-disjoint-ones-arg1-gen-better
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (< size2 size)
                (axe-syntaxp (bvcat-nest-with-low-zeros x size2 dag-array))
                (equal 0 (bvchop size2 x)) ;; force, or something?
                (unsigned-byte-p-forced size2 y)
                (natp size)
                (natp size2))
           (equal (bvplus size y x)
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :use (:instance bvplus-disjoint-ones-arg1-gen)
           :in-theory (e/d ( SLICE-TOO-HIGH-IS-0) (bvplus-disjoint-ones-arg1-gen)))))

(defthmd bvplus-disjoint-ones-arg2-gen-better
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (< size2 size)
                (axe-syntaxp (bvcat-nest-with-low-zeros x size2 dag-array))
                (equal 0 (bvchop size2 x)) ;; force, or something?
                (unsigned-byte-p-forced size2 y)
                (natp size)
                (natp size2))
           (equal (bvplus size x y)
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :use (:instance bvplus-disjoint-ones-arg2-gen)
           :in-theory (e/d ( SLICE-TOO-HIGH-IS-0) (bvplus-disjoint-ones-arg2-gen)))))

(in-theory (disable bvplus-disjoint-ones-arg1-gen bvplus-disjoint-ones-arg2-gen bvplus-disjoint-ones-arg1-gen-better bvplus-disjoint-ones-arg2-gen-better))

(defthmd bvplus-disjoint-ones-2
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (< size2 size)
                (axe-syntaxp (bvcat-nest-with-low-zeros x size2 dag-array))
                (equal 0 (bvchop size2 x)) ;; force, or something?
                (unsigned-byte-p-forced size2 y)
                ;(natp size)
                (natp size2))
           (equal (bvplus size y (bvplus size x z))
                  (bvplus size (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y) z)))
  :hints (("Goal" :use (:instance bvplus-disjoint-ones-arg1-gen-better)
           :in-theory (disable BVCAT-EQUAL-REWRITE BVCAT-EQUAL-REWRITE-alt))))

(defthmd bvplus-disjoint-ones-2-alt
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (< size2 size)
                (axe-syntaxp (bvcat-nest-with-low-zeros x size2 dag-array))
                (equal 0 (bvchop size2 x)) ;; force, or something?
                (unsigned-byte-p-forced size2 y)
                ;(natp size)
                (natp size2))
           (equal (bvplus size x (bvplus size y z))
                  (bvplus size (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y) z)))
  :hints (("Goal" :use (:instance bvplus-disjoint-ones-arg1-gen-better)
           :in-theory (disable BVCAT-EQUAL-REWRITE BVCAT-EQUAL-REWRITE-alt))))

(defthmd bvor-disjoint-ones-arg1-gen
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size2 dag-array) '(size2))
                (axe-syntaxp (bvcat-nest-with-low-zeros x size2 dag-array)) ;new
                (< size2 size)
                (equal 0 (bvchop size2 x))
                (unsigned-byte-p-forced size2 y)
                (natp size)
                (natp size2))
           (equal (bvor size y x)
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :in-theory (e/d (BVOR SLICE-TOO-HIGH-IS-0) ()))))

;how does the speed of this compare to doing it for each operator separately?
(defthmd <-lemma-for-known-operators
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= (expt 2 xsize) k)
                (unsigned-byte-p-forced xsize x)
                )
           (< x k)))

(defthmd <-lemma-for-known-operators-alt
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (<= (+ -1 (expt 2 xsize)) k)
                (unsigned-byte-p-forced xsize x)
                )
           (not (< k x)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))

(defthmd <-lemma-for-known-operators2
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (not (< x k)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthmd <-lemma-for-known-operators3
  (implies (and (syntaxp (quotep k))
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< k 0)
                (unsigned-byte-p-forced xsize x))
           (< k x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthmd *-becomes-bvmult-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'n dag-array) '(n))
                (axe-bind-free (bind-bv-size-axe y 'm dag-array) '(m))
                (unsigned-byte-p-forced n x)
                (unsigned-byte-p-forced m y))
           (equal (* x y)
                  (bvmult (+ m n) x y)))
  :hints (("Goal" :use (:instance *-becomes-bvmult-non-dag)
           :in-theory (disable *-becomes-bvmult-non-dag))))

(defthmd bvplus-tighten-better
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (< (+ 1 (max xsize ysize)) size) ;make sure we can tighten
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y) ;may not be true
                (natp size)
                (natp xsize)
                (natp ysize)
                )
           (equal (bvplus size x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal"
           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                           (r 2)
                           (i XSIZE)
                           (j ysize))
           :in-theory (e/d (bvplus BVCHOP-OF-SUM-CASES UNSIGNED-BYTE-P unsigned-byte-p-forced)
                           (;anti-bvplus
                            ;;<-OF-EXPT-AND-EXPT
                            )))))

;; ;y is a free var - yuck!
;; ;bozo prove me
;; ;rename to have -dag in the name
;; (defthmd bvplus-tighten
;;    (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;                  ;(axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
;;                  (< (+ 1 xsize ysize) size)
;;                  (unsigned-byte-p xsize x)
;;                  (unsigned-byte-p xsize y) ;may not be true
;;                  (natp size)
;;                  (natp xsize)
;;                  (natp ysize)
;;                  )
;;             (equal (bvplus size x y)
;;                    (bvplus (+ 1 (max xsize ysize)) x y)))
;;      :hints (("Goal"
;;            :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
;;                            (r 2)
;;                            (i XSIZE)
;;                            (j ysize))
;;            :in-theory (e/d (bvplus BVCHOP-OF-SUM-CASES UNSIGNED-BYTE-P)
;;                            (anti-bvplus)))))

;;    :hints (("Goal" :use (:instance bvplus-tighten-better)
;;             :in-theory (disable bvplus-tighten-better
;;                                 BVPLUS-OPENER))))

;;    :hints (("Goal"
;;             :use (:instance sum-bound-lemma)
;; ;          :expand (UNSIGNED-BYTE-P SIZE (+ X Y))
;;             :in-theory (e/d (BVPLUS UNSIGNED-BYTE-P
;;                                     ) (anti-bvplus ;max
;;                                     sum-bound-lemma))))

(defthmd bvplus-tighten-hack2
   (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                 ;(axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                 (< (+ 1 xsize) size)
                 (unsigned-byte-p-forced xsize x)
                 (unsigned-byte-p xsize y) ;may not be true
                 (natp size)
                 (natp xsize)
                 )
            (equal (bvplus size x y)
                   (bvplus (+ 1 xsize) x y)))
   :hints (("Goal"
            :use (:instance sum-bound-lemma)
;          :expand (UNSIGNED-BYTE-P SIZE (+ X Y))
            :in-theory (e/d (BVPLUS UNSIGNED-BYTE-P
                                    SLICE-TOO-HIGH-IS-0
                                    ) (;anti-bvplus ;max
                                    sum-bound-lemma)))))

(defthm if-becomes-bvif
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y)
                (natp xsize)
                (natp ysize)
                )
           (equal (if test x y)
                  (bvif (max xsize ysize) test x y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bvif myif))))

;free var rule from usb to integerp of the index?

(defthmd bvand-of-constant-tighten-dag-version
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep size))
                (< (integer-length k) size)
                (axe-bind-free (bind-bv-size-axe k 'ksize dag-array) '(ksize))
                (unsigned-byte-p-forced ksize k)
                (< ksize size)
                (integerp x)
                (natp size)
                (natp ksize)
                )
           (equal (bvand size k x)
                  (bvand ksize k x)))
  :hints (("Goal" :use (:instance bvand-of-constant-tighten (newsize ksize))
           :in-theory (disable bvand-of-constant-tighten))))

(defthmd bvshl-32-cases-dag ;just use the non-dag-version?
  (implies (and (syntaxp (not (quotep shift-amount)))
                (unsigned-byte-p 5 shift-amount)) ;bozo redefine bvshl to chop its shift amount?
           (equal (BVSHL 32 x shift-AMOUNT)
                  (BVIF 32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '0)
                        (bvshl 32 X '0)
                        (BVIF
                         32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '1)
                         (bvshl 32 X '1)
                         (BVIF
                          32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '2)
                          (bvshl 32 X '2)
                          (BVIF
                           32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '3)
                           (bvshl 32 X '3)
                           (BVIF
                            32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '4)
                            (bvshl 32 X '4)
                            (BVIF
                             32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '5)
                             (bvshl 32 X '5)
                             (BVIF
                              32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '6)
                              (bvshl 32 X '6)
                              (BVIF
                               32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '7)
                               (bvshl 32 X '7)
                               (BVIF
                                32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '8)
                                (bvshl 32 X '8)
                                (BVIF
                                 32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '9)
                                 (bvshl 32 X '9)
                                 (BVIF
                                  32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '10)
                                  (bvshl 32 X '10)
                                  (BVIF
                                   32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '11)
                                   (bvshl 32 X '11)
                                   (BVIF
                                    32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '12)
                                    (bvshl 32 X '12)
                                    (BVIF
                                     32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '13)
                                     (bvshl 32 X '13)
                                     (BVIF
                                      32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '14)
                                      (bvshl 32 X '14)
                                      (BVIF
                                       32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '15)
                                       (bvshl 32 X '15)
                                       (BVIF
                                        32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '16)
                                        (bvshl 32 X '16)
                                        (BVIF
                                         32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '17)
                                         (bvshl 32 X '17)
                                         (BVIF
                                          32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '18)
                                          (bvshl 32 X '18)
                                          (BVIF
                                           32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '19)
                                           (bvshl 32 X '19)
                                           (BVIF
                                            32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '20)
                                            (bvshl 32 X '20)
                                            (BVIF
                                             32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '21)
                                             (bvshl 32 X '21)
                                             (BVIF
                                              32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '22)
                                              (bvshl 32 X '22)
                                              (BVIF
                                               32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '23)
                                               (bvshl 32 X '23)
                                               (BVIF
                                                32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '24)
                                                (bvshl 32 X '24)
                                                (BVIF
                                                 32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '25)
                                                 (bvshl 32 X '25)
                                                 (BVIF
                                                  32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '26)
                                                  (bvshl 32 X '26)
                                                  (BVIF
                                                   32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '27)
                                                   (bvshl 32 X '27)
                                                   (BVIF
                                                    32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '28)
                                                    (bvshl 32 X '28)
                                                    (BVIF
                                                     32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '29)
                                                     (bvshl 32 X '29)
                                                     (BVIF
                                                      32 (EQUAL (BVCHOP 5 shift-amount) '30)
                                                      (bvshl 32 X '30)
                                                      (bvshl 32
                                                           X
                                                           '31))))))))))))))))))))))))))))))))))
  :hints (("Goal" :in-theory (e/d (bvif bvshl)
                                  (BVSHL-REWRITE-WITH-BVCHOP
                                   <=-OF-BVCHOP-SAME-LINEAR
                                   <-OF-IF-ARG1
                                   ;BVCHOP-IDENTITY
                                   ;UNSIGNED-BYTE-P-FROM-BOUNDS
)))))

(defthmd bvshr-32-cases-dag;just use the non-dag-version?
  (implies (and (syntaxp (not (quotep shift-amount)))
                (unsigned-byte-p 5 shift-amount)) ;bozo redefine bvshr to chop its shift amount?
           (equal (BVSHR 32 x shift-AMOUNT)
                  (BVIF 32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '0)
                        (bvshr 32 X '0)
                        (BVIF
                         32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '1)
                         (bvshr 32 X '1)
                         (BVIF
                          32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '2)
                          (bvshr 32 X '2)
                          (BVIF
                           32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '3)
                           (bvshr 32 X '3)
                           (BVIF
                            32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '4)
                            (bvshr 32 X '4)
                            (BVIF
                             32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '5)
                             (bvshr 32 X '5)
                             (BVIF
                              32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '6)
                              (bvshr 32 X '6)
                              (BVIF
                               32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '7)
                               (bvshr 32 X '7)
                               (BVIF
                                32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '8)
                                (bvshr 32 X '8)
                                (BVIF
                                 32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '9)
                                 (bvshr 32 X '9)
                                 (BVIF
                                  32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '10)
                                  (bvshr 32 X '10)
                                  (BVIF
                                   32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '11)
                                   (bvshr 32 X '11)
                                   (BVIF
                                    32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '12)
                                    (bvshr 32 X '12)
                                    (BVIF
                                     32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '13)
                                     (bvshr 32 X '13)
                                     (BVIF
                                      32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '14)
                                      (bvshr 32 X '14)
                                      (BVIF
                                       32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '15)
                                       (bvshr 32 X '15)
                                       (BVIF
                                        32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '16)
                                        (bvshr 32 X '16)
                                        (BVIF
                                         32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '17)
                                         (bvshr 32 X '17)
                                         (BVIF
                                          32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '18)
                                          (bvshr 32 X '18)
                                          (BVIF
                                           32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '19)
                                           (bvshr 32 X '19)
                                           (BVIF
                                            32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '20)
                                            (bvshr 32 X '20)
                                            (BVIF
                                             32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '21)
                                             (bvshr 32 X '21)
                                             (BVIF
                                              32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '22)
                                              (bvshr 32 X '22)
                                              (BVIF
                                               32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '23)
                                               (bvshr 32 X '23)
                                               (BVIF
                                                32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '24)
                                                (bvshr 32 X '24)
                                                (BVIF
                                                 32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '25)
                                                 (bvshr 32 X '25)
                                                 (BVIF
                                                  32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '26)
                                                  (bvshr 32 X '26)
                                                  (BVIF
                                                   32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '27)
                                                   (bvshr 32 X '27)
                                                   (BVIF
                                                    32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '28)
                                                    (bvshr 32 X '28)
                                                    (BVIF
                                                     32 (EQUAL (BVCHOP 5 SHIFT-AMOUNT) '29)
                                                     (bvshr 32 X '29)
                                                     (BVIF
                                                      32 (EQUAL (BVCHOP 5 shift-amount) '30)
                                                      (bvshr 32 X '30)
                                                      (bvshr 32
                                                           X
                                                           '31))))))))))))))))))))))))))))))))))
  :hints (("Goal" :in-theory (e/d (bvif bvshr) (unsigned-byte-p-from-bounds)))))

(defthmd bvshl-32-cases-dag-barrel-shifter ;just use a non-dag-version?
  (implies (and (syntaxp (not (quotep shift-amount)))
                (unsigned-byte-p 5 shift-amount)) ;bozo redefine bvshl to chop its shift amount?
           (equal (BVSHL 32 x shift-AMOUNT)
                  (let* ((a (bvif 32 (equal 1 (getbit 4 shift-AMOUNT))
                                  (bvshl 32 x 16)
                                  x))
                         (b (bvif 32 (equal 1 (getbit 3 shift-AMOUNT))
                                  (bvshl 32 a 8)
                                  a))
                         (c (bvif 32 (equal 1 (getbit 2 shift-AMOUNT))
                                  (bvshl 32 b 4)
                                  b))
                         (d (bvif 32 (equal 1 (getbit 1 shift-AMOUNT))
                                  (bvshl 32 c 2)
                                  c))
                         (e (bvif 32 (equal 1 (getbit 0 shift-AMOUNT))
                                  (bvshl 32 d 1)
                                  d)))
                    e)))
  :hints (("Goal"
           :cases ((equal 0 shift-amount)
                   (equal 1 shift-amount)
                   (equal 2 shift-amount)
                   (equal 3 shift-amount)
                   (equal 4 shift-amount)
                   (equal 5 shift-amount)
                   (equal 6 shift-amount)
                   (equal 7 shift-amount)
                   (equal 8 shift-amount)
                   (equal 9 shift-amount)
                   (equal 10 shift-amount)
                   (equal 11 shift-amount)
                   (equal 12 shift-amount)
                   (equal 13 shift-amount)
                   (equal 14 shift-amount)
                   (equal 15 shift-amount)
                   (equal 16 shift-amount)
                   (equal 17 shift-amount)
                   (equal 18 shift-amount)
                   (equal 19 shift-amount)
                   (equal 20 shift-amount)
                   (equal 21 shift-amount)
                   (equal 22 shift-amount)
                   (equal 23 shift-amount)
                   (equal 24 shift-amount)
                   (equal 25 shift-amount)
                   (equal 26 shift-amount)
                   (equal 27 shift-amount)
                   (equal 28 shift-amount)
                   (equal 29 shift-amount)
                   (equal 30 shift-amount)
                   (equal 31 shift-amount))
           :in-theory (e/d (BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT) (BVSHL-REWRITE-WITH-BVCHOP)))))

(defthmd bvshr-32-cases-dag-barrel-shifter ;just use a non-dag-version?
  (implies (and (syntaxp (not (quotep shift-amount)))
                (unsigned-byte-p 5 shift-amount)) ;bozo redefine bvshr to chop its shift amount?
           (equal (BVSHR 32 x shift-AMOUNT)
                  (let* ((a (bvif 32 (equal 1 (getbit 4 shift-AMOUNT))
                                  (bvshr 32 x 16)
                                  x))
                         (b (bvif 32 (equal 1 (getbit 3 shift-AMOUNT))
                                  (bvshr 32 a 8)
                                  a))
                         (c (bvif 32 (equal 1 (getbit 2 shift-AMOUNT))
                                  (bvshr 32 b 4)
                                  b))
                         (d (bvif 32 (equal 1 (getbit 1 shift-AMOUNT))
                                  (bvshr 32 c 2)
                                  c))
                         (e (bvif 32 (equal 1 (getbit 0 shift-AMOUNT))
                                  (bvshr 32 d 1)
                                  d)))
                    e)))
  :hints (("Goal"
           :cases ((equal 0 shift-amount)
                   (equal 1 shift-amount)
                   (equal 2 shift-amount)
                   (equal 3 shift-amount)
                   (equal 4 shift-amount)
                   (equal 5 shift-amount)
                   (equal 6 shift-amount)
                   (equal 7 shift-amount)
                   (equal 8 shift-amount)
                   (equal 9 shift-amount)
                   (equal 10 shift-amount)
                   (equal 11 shift-amount)
                   (equal 12 shift-amount)
                   (equal 13 shift-amount)
                   (equal 14 shift-amount)
                   (equal 15 shift-amount)
                   (equal 16 shift-amount)
                   (equal 17 shift-amount)
                   (equal 18 shift-amount)
                   (equal 19 shift-amount)
                   (equal 20 shift-amount)
                   (equal 21 shift-amount)
                   (equal 22 shift-amount)
                   (equal 23 shift-amount)
                   (equal 24 shift-amount)
                   (equal 25 shift-amount)
                   (equal 26 shift-amount)
                   (equal 27 shift-amount)
                   (equal 28 shift-amount)
                   (equal 29 shift-amount)
                   (equal 30 shift-amount)
                   (equal 31 shift-amount))
           :in-theory (e/d (BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT) ()))))

;fixme make rules like this for other ops!
(defthmd bvsx-too-high-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize old-size)
                (integerp new-size)
;               (natp xsize)
                (< old-size new-size)
                (posp old-size)
                (unsigned-byte-p-forced xsize x))
           (equal (bvsx new-size old-size x)
                  x))
  :hints (("Goal" :in-theory (e/d (natp bvsx getbit-too-high) (;collect-constants-times-equal collect-constants-<-/
                                                               )))))

;gen
(defthmd sbvlt-of-0-when-shorter2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (< xsize 32)
                (natp xsize)
                (unsigned-byte-p-forced xsize x))
           (equal (sbvlt 32 x 0) ;gen the 0
                  nil))
  :hints (("Goal" :use (:instance sbvlt-of-0-when-shorter2)
           :in-theory (e/d (unsigned-byte-p-forced) (sbvlt-of-0-when-shorter2)))))

(defthmd turn-equal-around-axe3
  (implies (and (axe-syntaxp (bv-term-syntaxp x dag-array))
                (axe-syntaxp (not-bv-term-syntaxp y dag-array)))
           (equal (equal y x)
                  (equal x y))))

(defthmd turn-equal-around-axe4
  (implies (axe-syntaxp (should-reverse-equality x y dag-array))
           (equal (equal x y)
                  (equal y x))))

;; ;these 2 moved from hacks6:
;; (defthmd logext-list-of-myif-drop-logext-lists-arg1
;;   (implies (and (axe-syntaxp (myif-nest-needs-bvchop-list x size dag-array)) ;else it could loop?
;;                 (posp size))
;;            (equal (logext-list size (myif test x y))
;;                   (logext-list size (myif test (push-bvchop-list size x) y))))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthmd logext-list-of-myif-drop-logext-lists-arg2
;;   (implies (and (axe-syntaxp (myif-nest-needs-bvchop-list x size dag-array)) ;else it could loop?
;;                 (posp size))
;;            (equal (logext-list size (myif test y x))
;;                   (logext-list size (myif test y (push-bvchop-list size x)))))
;;   :hints (("Goal" :in-theory (enable myif))))

;use EQUAL-OF-BVCHOP-EXTEND once we have polarity in the dag-prover
;expensive!
;; (defthmd recollapse-hack
;;   (implies (and (syntaxp (not (quotep x)))
;;                 (equal free1 (bvchop size x))
;;                 (natp size)
;;                 (syntaxp (quotep free1))
;;                 (not (equal 0 (getbit size x)))
;;                 (unsigned-byte-p (+ 1 size) x))
;;            (equal (equal k x)
;;                   (equal k (bvcat 1 1 size free1))))
;;   :hints (("Goal" :use (:instance recollapse-hack-helper)
;;            :in-theory (theory 'minimal-theory)
;;            )))

;drop?  mentioned in rule-lists.lisp
(defthmd recollapse-hack-slice-version  ;just use a non-dag-version?
  (implies (and (syntaxp (not (quotep x)))
                (equal free1 (bvchop size x))
                (natp size)
                (syntaxp (quotep free1))
                (equal free2 (slice high size x))
                (syntaxp (quotep free2))
                (syntaxp (quotep high))
                (natp high)
                (<= size high)
                (unsigned-byte-p (+ 1 high) x))
           (equal (equal k x)
                  (equal k (bvcat (+ 1 high (- size)) free2 size free1))))
  :hints (("Goal" :in-theory (disable <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT ;why
                                      ))))

;move
(defthm myif-same-arg1-arg2-when-booleanp-axe
  (implies (and (axe-syntaxp (not (syntactic-constantp x dag-array))) ;avoid loops
                (booleanp x))
           (equal (myif x x y)
                  (myif x t y)))
  :hints (("Goal" :in-theory (enable myif))))

;only needed for axe
(defthm not-<-of-bvcat-and-0
  (not (< (bvcat highsize highval lowsize lowval) 0)))
