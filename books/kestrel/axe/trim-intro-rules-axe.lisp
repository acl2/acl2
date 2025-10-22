; Axe rules to trim terms that are BVs.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2021 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;; This book includes rules that introduce trim.  They are for use with Axe
;;; but not with the ACL2 Rewriter.  Many of these are versions of pre-existing
;;; non-Axe rules.

;; This is the Axe version of ../bv/trim-intro-rules.lisp

;; See also convert-to-bv-rules-axe.lisp

(include-book "axe-syntax")
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/bv/defs" :dir :system)
(include-book "kestrel/bv/sbvlt-def" :dir :system)
(include-book "kestrel/bv/bvequal" :dir :system)
(include-book "kestrel/bv/rightrotate32" :dir :system) ; add to bv/defs.lisp
(include-book "kestrel/bv/leftrotate32" :dir :system) ; add to bv/defs.lisp
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system) ; add to bv/defs.lisp?
(include-book "kestrel/bv/trim-elim-rules-bv" :dir :system) ; these rules complement the rules in this book
(local (include-book "kestrel/bv/rules" :dir :system));drop?
(local (include-book "kestrel/bv/sbvdiv" :dir :system))
(local (include-book "kestrel/bv/sbvrem" :dir :system))
(local (include-book "kestrel/bv/leftrotate-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvnot-trim-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitnot-trim-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitnot x)
                  (bitnot (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvminus-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvminus size x y)
                  (bvminus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvminus-trim-arg3-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvminus size y x)
                  (bvminus size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvuminus-trim-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (posp size) ; gen?
                )
           (equal (bvuminus size x)
                  (bvuminus size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvuminus-trim-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (posp size) ; gen?
                )
           (equal (bvuminus size x)
                  (bvuminus size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd slice-trim-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe-plus-one high x 'all dag-array))
                (<= low high)
                (natp low)
                (natp high))
           (equal (slice high low x)
                  (slice high low (trim (+ 1 high) x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;here's a loop if we did it when n=0 -- except now we use trim, not bvchop
;; (bvchop 1 (slice 3 2 x))
;; (GETBIT 0 (SLICE 3 2 X))
;; (GETBIT 0 (bvchop 1 (SLICE 3 2 X)))
(defthmd getbit-trim-axe-all
  (implies (and (< 0 n) ;if n=0 it's already being trimmed by the getbit (BOZO make sure we can simplify such cases..)
                (axe-syntaxp (term-should-be-trimmed-axe-plus-one n x 'all dag-array))
                (integerp n))
           (equal (getbit n x)
                  (getbit n (trim (+ 1 n) x))))
  :hints (("Goal" :in-theory (enable trim))))

;; (defthmd getbit-trim-axe-all-gen
;;   (implies (and (<= 0 n)
;;                 (axe-syntaxp (term-should-be-trimmed-axe-plus-one n x 'all dag-array))
;;                 (integerp n))
;;            (equal (getbit n x)
;;                   (getbit n (trim (+ 1 n) x))))
;;   :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvcat-trim-arg2-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe highsize highval 'non-arithmetic dag-array))
                (natp highsize)
                ;; (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg4-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe lowsize lowval 'non-arithmetic dag-array))
                ;; (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe highsize highval 'all dag-array))
                (natp highsize)
                ;; (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvcat-trim-arg4-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe lowsize lowval 'all dag-array))
                ;; (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvplus-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-trim-arg3-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size y 'non-arithmetic dag-array))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvplus-trim-arg3-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvequal-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvequal size x y)
                  (bvequal size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvequal-trim-arg3-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size y 'non-arithmetic dag-array))
           (equal (bvequal size x y)
                  (bvequal size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvequal-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvequal size x y)
                  (bvequal size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvequal-trim-arg3-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
           (equal (bvequal size x y)
                  (bvequal size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvand-trim-arg1-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvand size x y)
                  (bvand size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg2-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvand size y x)
                  (bvand size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvand size x y)
                  (bvand size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvand-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvand size y x)
                  (bvand size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvor-trim-arg1-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvor size x y)
                  (bvor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvor-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvor size y x)
                  (bvor size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvor-trim-arg1-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvor size x y)
                  (bvor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvor-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvor size y x)
                  (bvor size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvxor-trim-arg1-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvxor size x y)
                  (bvxor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvxor size y x)
                  (bvxor size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvxor size x y)
                  (bvxor size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvxor-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvxor size y x)
                  (bvxor size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvif-trim-arg3-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvif size test x y)
                  (bvif size test (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg4-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
           (equal (bvif size test y x)
                  (bvif size test y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg3-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvif size test x y)
                  (bvif size test (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvif-trim-arg4-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
           (equal (bvif size test y x)
                  (bvif size test y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitand-trim-arg1-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'non-arithmetic dag-array))
           (equal (bitand x y)
                  (bitand (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'non-arithmetic dag-array))
           (equal (bitand y x)
                  (bitand y (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-trim-arg1-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitand x y)
                  (bitand (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitand-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitand y x)
                  (bitand y (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitor-trim-arg1-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'non-arithmetic dag-array))
           (equal (bitor x y)
                  (bitor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'non-arithmetic dag-array))
           (equal (bitor y x)
                  (bitor y (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-trim-arg1-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitor x y)
                  (bitor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitor-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitor y x)
                  (bitor y (trim 1 x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitxor-trim-arg1-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'non-arithmetic dag-array))
           (equal (bitxor x y)
                  (bitxor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-trim-arg2-axe
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 y 'non-arithmetic dag-array))
           (equal (bitxor x y)
                  (bitxor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-trim-arg1-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 x 'all dag-array))
           (equal (bitxor x y)
                  (bitxor (trim 1 x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bitxor-trim-arg2-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '1 y 'all dag-array))
           (equal (bitxor x y)
                  (bitxor x (trim 1 y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvmult-trim-arg1-axe
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size (trim size x) y)))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg2-axe
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'non-arithmetic dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size x (trim size y))))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg1-axe-all
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size (trim size x) y)))
   :hints (("Goal" :in-theory (enable trim))))

(defthmd bvmult-trim-arg2-axe-all
   (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
                 (natp size))
            (equal (bvmult size x y)
                   (bvmult size x (trim size y))))
   :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename these?!
(defthmd bvdiv-trim-arg1-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvdiv size x y)
                  (bvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-trim-arg2-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (bvdiv size y x)
                  (bvdiv size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvdiv size x y)
                  (bvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvdiv-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvdiv size y x)
                  (bvdiv size y (trim size x))))
  :hints (("Goal":in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename these?!
(defthmd sbvdiv-trim-arg1-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (sbvdiv size x y)
                  (sbvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd sbvdiv-trim-arg2-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (sbvdiv size y x)
                  (sbvdiv size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd sbvdiv-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (sbvdiv size x y)
                  (sbvdiv size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd sbvdiv-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (sbvdiv size y x)
                  (sbvdiv size y (trim size x))))
  :hints (("Goal":in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename these?!
(defthmd sbvrem-trim-arg1-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (sbvrem size x y)
                  (sbvrem size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd sbvrem-trim-arg2-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'non-arithmetic dag-array))
                (natp size))
           (equal (sbvrem size y x)
                  (sbvrem size y (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd sbvrem-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (sbvrem size x y)
                  (sbvrem size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd sbvrem-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (sbvrem size y x)
                  (sbvrem size y (trim size x))))
  :hints (("Goal":in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvlt-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bvlt-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size y 'all dag-array))
                (natp size))
           (equal (bvlt size x y)
                  (bvlt size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvmod-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvmod size x y)
                  (bvmod size (trim size x) y)))
  :hints(("Goal" :in-theory (enable trim))))

(defthmd bvmod-trim-arg2-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (natp size))
           (equal (bvmod size y x)
                  (bvmod size y (trim size x))))
  :hints(("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd leftrotate32-trim-arg1-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '5 amt 'non-arithmetic dag-array))
                (natp amt))
           (equal (leftrotate32 amt val)
                  (leftrotate32 (trim 5 amt) val)))
  :hints (("Goal" :use leftrotate32-trim-arg1
           :in-theory (disable leftrotate32-trim-arg1))))

;for this not to loop, we must simplify things like (bvchop 5 (bvplus 32 x y))
(defthmd leftrotate32-trim-arg1-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '5 amt 'all dag-array))
                (natp amt))
           (equal (leftrotate32 amt val)
                  (leftrotate32 (trim 5 amt) val)))
  :hints (("Goal" :use leftrotate32-trim-arg1
           :in-theory (disable leftrotate32-trim-arg1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;bozo gen
;rename
;make 'all variant, like for leftrotate above
(defthmd rightrotate32-trim-amt-axe
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '5 amt 'non-arithmetic dag-array))
                (natp amt))
           (equal (rightrotate32 amt x)
                  (rightrotate32 (trim 5 amt) x)))
  :hints (("Goal" :in-theory (enable rightrotate32 rightrotate leftrotate trim mod-becomes-bvchop-when-power-of-2p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; still needed?
(defthmd logext-trim-arg-axe-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size x 'all dag-array))
                (posp size))
           (equal (logext size x)
                  (logext size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Should not be needed
(defthmd trim-does-nothing-axe
  (implies (and (axe-bind-free (bind-bv-size-axe i 'isize dag-array) '(isize))
                (<= isize size)
                (unsigned-byte-p-forced isize i)
                (integerp size)
                )
           (equal (trim size i)
                  i))
  :hints (("Goal" :in-theory (enable trim unsigned-byte-p-forced))))
