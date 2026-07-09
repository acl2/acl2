; Rules to chop arguments using trim
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See ../axe/trim-intro-rules-axe.lisp for the Axe versions of these rules

;; See trim-elim-rules-bv.lisp and trim-elim-rules-non-bv.lisp for the rules
;; that finish the job (and remove TRIM).

(include-book "bv-syntax")
(include-book "trim")
(include-book "bvsx-def")
(include-book "leftrotate32")
(include-book "bvnot")
(include-book "bvcat-def")
(include-book "bvif")
(include-book "bvplus-def")
(include-book "bvmult-def")
(include-book "bvminus-def")
(include-book "bvand-def")
(include-book "bvor-def")
(include-book "bvxor-def")
(include-book "bvlt")
(include-book "trim-elim-rules-bv") ; need these whenever we introduce trim
(local (include-book "slice"))
(local (include-book "getbit"))
(local (include-book "bvcat"))

;; TODO: Should we only trim when the sizes involved are constants?

;BOZO lots more rules like this

;; Should we consider leaving the natp hyps on the sizes in the rules below, so
;; these rules don't fire in contexts where the corresponding hyps in
;; trim-elim-rules-bv.lisp cannot be relieved?  Perhaps it suffices to have
;; term-should-be-trimmed check that the size is a quoted natp.

;enable?
(defthmd bvnot-trim-all
  (implies (and (syntaxp (term-should-be-trimmedp size x :all))
                (natp size))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: Use term-should-be-trimmed here and below, instead of bind-var-to-bv-term-size-if-trimmable?

;rename?
(defthm bvxor-trim-arg1
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize x) (innersize))
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize))
           (equal (bvxor outersize x y)
                  (bvxor outersize (trim outersize x) y)))
  :hints (("Goal" :in-theory (enable bvxor trim))))

;rename?
(defthm bvxor-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize y) (innersize))
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize))
           (equal (bvxor outersize x y)
                  (bvxor outersize x (trim outersize y))))
  :hints (("Goal" :in-theory (enable bvxor trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; these should have 'trim' in the name:

;watch out for loops
(defthm bvcat-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'newsize highval) (newsize))
                (syntaxp (quotep highsize))
                (< highsize newsize)
                (natp highsize)
                (natp newsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bvcat-trim-arg4
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'newsize lowval) (newsize))
                (syntaxp (quotep lowsize))
                (< lowsize newsize)
                (natp highsize)
                (natp newsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvcat-of-bvchop-low trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvif-trim-arg3
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize x) (innersize)) ;bozo newsize is a bad name
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize))
           (equal (bvif outersize test x y)
                  (bvif outersize test (trim outersize x) y)))
  :hints (("Goal" :in-theory (enable bvif trim))))

(defthm bvif-trim-arg4
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize y) (innersize)) ;bozo newsize is a bad name
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize))
           (equal (bvif outersize test x y)
                  (bvif outersize test x (trim outersize y))))
  :hints (("Goal" :in-theory (enable bvif trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;improve to handle non-constants
;; (defthmd bvif-trim-constant-arg3
;;   (implies (and (syntaxp (and (quotep x)
;;                               (quotep size)))
;;                 (not (unsigned-byte-p size x))
;;                 (natp size) ; prevent loops
;;                 )
;;            (equal (bvif size test x y)
;;                   (bvif size test (trim size x) y)))
;;   :hints (("Goal" :in-theory (enable trim))))

;; ;improve to handle non-constants
;; (defthmd bvif-trim-constant-arg4
;;   (implies (and (syntaxp (and (quotep x)
;;                               (quotep size)))
;;                 (not (unsigned-byte-p size x))
;;                 (natp size) ; prevent loops
;;                 )
;;            (equal (bvif size test y x)
;;                   (bvif size test y (trim size x))))
;;   :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvplus-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvplus size x y)
                  (bvplus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bvplus-trim-arg3
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'ysize y))
                (< size ysize)
                (natp size)
                (posp ysize))
           (equal (bvplus size x y)
                  (bvplus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvmult-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvmult size x y)
                  (bvmult size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bvmult-trim-arg3
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'ysize y))
                (< size ysize)
                (natp size)
                (posp ysize))
           (equal (bvmult size x y)
                  (bvmult size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvminus-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvminus size x y)
                  (bvminus size (trim size x) y)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bvminus-trim-arg3
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'ysize y))
                (< size ysize)
                (natp size)
                (posp ysize))
           (equal (bvminus size x y)
                  (bvminus size x (trim size y))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: rename n to size
(defthm bvuminus-trim
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< (+ 1 n) xsize) ; todo: why not (< n xsize)?
                (natp n)
                (integerp xsize))
           (equal (bvuminus n x)
                  (bvuminus n (trim n x))))
  :hints (("Goal" :in-theory (e/d (bvminus bvuminus trim
                                           bvchop-when-i-is-not-an-integer)
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm slice-trim
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< (+ 1 high) xsize)
                (natp high)
                (natp low)
                (integerp xsize))
           (equal (slice high low x)
                  (slice high low (trim (+ high 1) x))))
  :hints (("Goal" :in-theory (enable trim) )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm getbit-trim
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< (+ 1 size) xsize)
                (natp size)
                (integerp xsize))
           (equal (getbit size x)
                  (getbit size (trim (+ 1 size) x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvlt-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvlt size x y)
                  (bvlt size (trim size x) y)))
  :hints (("Goal" :in-theory (enable bvlt trim))))

(defthm bvlt-trim-arg3
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
                (< size xsize)
                (natp size)
                (posp xsize))
           (equal (bvlt size y x)
                  (bvlt size y (trim size x))))
  :hints (("Goal" :in-theory (enable bvlt trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;rename to indicate which arg is trimmed
;; (defthm leftrotate32-trim-arg1
;;   (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'xsize x))
;;                 (< 5 xsize)
;;                 (integerp xsize))
;;            (equal (leftrotate32 x y)
;;                   (leftrotate32 (trim 5 x) y)))
;;   :hints (("Goal" :in-theory (e/d (trim) (leftrotate32)))))

(defthm leftrotate32-trim-arg1
  (implies (and (syntaxp (term-should-be-trimmedp ''5 amt :non-arithmetic))
                (natp amt))
           (equal (leftrotate32 amt val)
                  (leftrotate32 (trim 5 amt) val)))
  :hints (("Goal" :in-theory (enable trim))))

;for this not to loop, we must simplify things like (bvchop 5 (bvplus 32 x y)) ??
(defthm leftrotate32-trim-arg1-all
  (implies (and (syntaxp (term-should-be-trimmedp ''5 amt :all))
                (natp amt))
           (equal (leftrotate32 amt val)
                  (leftrotate32 (trim 5 amt) val)))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvsx-trim-all
  (implies (syntaxp (term-should-be-trimmedp old-size x :all))
           (equal (bvsx new-size old-size x)
                  (bvsx new-size old-size (trim old-size x))))
  :hints (("Goal" :in-theory (enable trim))))
