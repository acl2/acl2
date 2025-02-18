; Axe rules about BVs
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

;;; This book includes rules that use axe-syntaxp, axe-bind-free, and
;;; axe-rewrite-objective.  They are for use with Axe but not with the ACL2
;;; Rewriter.  Many of these are versions of pre-existing rules.

;; See also ../bv/intro.lisp for rules like these that do not use
;; axe-bind-free, etc.

;; TODO: Rename rules that end in -dag to instead end in -axe.

;todo: reduce:
(include-book "axe-syntax-functions-bv")
(include-book "axe-syntax-functions") ;for SYNTACTIC-CALL-OF
(include-book "kestrel/bv/defs" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
;(include-book "kestrel/bv/rightrotate32" :dir :system) ; add to bv/defs.lisp
;(include-book "kestrel/bv/leftrotate32" :dir :system) ; add to bv/defs.lisp
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system) ; add to bv/defs.lisp?
(include-book "kestrel/booleans/boolor" :dir :system)
(include-book "kestrel/booleans/booland" :dir :system)
;(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
;(include-book "known-booleans")
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/logand-b" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ;drop?
(local (include-book "kestrel/bv/rules3" :dir :system)) ;for *-becomes-bvmult
(local (include-book "kestrel/bv/rules6" :dir :system)) ; for plus-becomes-bvplus
;(local (include-book "kestrel/bv/rules6" :dir :system)) ;for BVMULT-TIGHTEN
;(local (include-book "kestrel/bv/sbvrem-rules" :dir :system))
;(local (include-book "kestrel/bv/sbvdiv" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

(defthmd if-becomes-bvif-1-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (if test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

(defthmd if-becomes-bvif-2-axe
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free variable
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y))
           (equal (if test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif unsigned-byte-p-forced))))

(defthmd if-becomes-bvif-3-axe
  (implies (and (unsigned-byte-p ysize y) ; ysize is a free variable
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (if test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif unsigned-byte-p-forced))))

;todo: not an axe rule, so move and rename
(defthmd if-becomes-bvif-4-axe
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free variable
                (unsigned-byte-p ysize y) ; ysize is a free variable
                )
           (equal (if test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd myif-becomes-bvif-1-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

(defthmd myif-becomes-bvif-2-axe
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free variable
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y))
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

(defthmd myif-becomes-bvif-3-axe
  (implies (and (unsigned-byte-p ysize y) ; ysize is a free variable
                (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-forced))))

;todo: not an axe rule, so move and rename
(defthmd myif-becomes-bvif-4-axe
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free variable
                (unsigned-byte-p ysize y) ; ysize is a free variable
                )
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd mod-becomes-bvmod-axe-bind-free-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize y)
                (unsigned-byte-p-forced xsize x))
           (equal (mod x y)
                  (bvmod xsize x y)))
  :hints (("Goal" :use (:instance mod-becomes-bvmod-free-arg1 (size xsize)))))

(defthmd mod-becomes-bvmod-axe-bind-free-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p ysize x)
                (unsigned-byte-p-forced ysize y))
           (equal (mod x y)
                  (bvmod ysize x y)))
  :hints (("Goal" :use (:instance mod-becomes-bvmod-free-arg1 (size xsize)))))

;drop?
(defthmd mod-becomes-bvmod-axe-bind-free-and-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-free-arg1 (size (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

;drop?
(defthmd mod-becomes-bvmod-axe-bind-free-and-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y) ;ysize is a freevar
                (unsigned-byte-p-forced xsize x))
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-free-arg1 (size (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

;drop?
(defthmd mod-becomes-bvmod-axe-free-and-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p xsize x) ;xsize is a freevar
                (unsigned-byte-p-forced ysize y))
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-free-arg1 (size (max xsize ysize)))
           :in-theory (enable unsigned-byte-p-forced))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd *-becomes-bvmult-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'n dag-array) '(n))
                (axe-bind-free (bind-bv-size-axe y 'm dag-array) '(m))
                (unsigned-byte-p-forced n x)
                (unsigned-byte-p-forced m y))
           (equal (* x y)
                  (bvmult (+ m n) x y)))
  :hints (("Goal" :use (:instance *-becomes-bvmult)
           :in-theory (disable *-becomes-bvmult))))

(defthmd *-becomes-bvmult-2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y)
                (unsigned-byte-p-forced xsize x))
           (equal (* x y) (bvmult (+ ysize xsize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance *-becomes-bvmult (n xsize) (m ysize)))))

(defthmd *-becomes-bvmult-3-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y)
                (unsigned-byte-p-forced xsize x))
           (equal (* y x) (bvmult (+ ysize xsize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance *-becomes-bvmult (n xsize) (m ysize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd logand-becomes-bvand-arg1-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (logand x y)
                  (bvand xsize x y)))
  :hints (("Goal" :use (:instance logand-becomes-bvand (size xsize) (y y))
           :in-theory (disable logand-becomes-bvand))))

(defthmd logand-becomes-bvand-arg2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x))
           (equal (logand y x)
                  (bvand xsize y x)))
  :hints (("Goal":use (:instance logand-becomes-bvand (size xsize) (y y))
           :in-theory (disable logand-becomes-bvand))))

(defthmd logior-becomes-bvor-arg1-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize y)
                (unsigned-byte-p-forced xsize x))
           (equal (logior x y)
                  (bvor xsize x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd logior-becomes-bvor-arg2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p ysize x)
                (unsigned-byte-p-forced ysize y))
           (equal (logior x y)
                  (bvor ysize x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd logxor-becomes-bvxor-arg1-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p xsize y)
                (unsigned-byte-p-forced xsize x))
           (equal (logxor x y)
                  (bvxor xsize x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthmd logxor-becomes-bvxor-arg2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p ysize x)
                (unsigned-byte-p-forced ysize y))
           (equal (logxor x y)
                  (bvxor ysize x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;rename?
(defthmd logtail-becomes-slice-bind-free-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'newsize dag-array) '(newsize))
                (<= n newsize) ;drop?
                (integerp newsize)
                (integerp x) ;drop
                (natp n)
                (unsigned-byte-p-forced newsize x) ;switched to usb-forced? (also elsewhere!))
                )
           (equal (logtail n x)
                  (slice (+ -1 newsize) n x)))
  :hints (("Goal" :use (:instance logtail-becomes-slice-bind-free)
           :in-theory (e/d (unsigned-byte-p-forced) (logtail-becomes-slice-bind-free)))))

(defthmd logapp-becomes-bvcat-bind-free-axe
  (implies (and (axe-bind-free (bind-bv-size-axe j 'jsize dag-array) '(jsize))
                (unsigned-byte-p-forced jsize j))
           (equal (logapp size i j)
                  (bvcat jsize j size i)))
  :hints (("Goal" :in-theory (enable bvcat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Pretty aggressive
;rename
(defthmd +-becomes-bvplus-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (posp xsize)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus)
           :in-theory (disable plus-becomes-bvplus))))

;fixme: uses force
(defthmd +-becomes-bvplus-axe-free-and-bind-free
  (implies (and (unsigned-byte-p xsize x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus)
           :in-theory (e/d (unsigned-byte-p-forced) (plus-becomes-bvplus)))))

(defthmd +-becomes-bvplus-axe-bind-free-and-free
  (implies (and (unsigned-byte-p xsize x)
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (posp xsize)
                (unsigned-byte-p-forced ysize y))
           (equal (+ y x)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus-arg2-free)
           :in-theory (disable plus-becomes-bvplus-arg2-free))))

;; ;gen the 1
;; (defthmd +-becomes-bvplus-when-bv-dag
;;   (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;                 (unsigned-byte-p-forced xsize x)
;;                 (natp xsize))
;;            (equal (+ 1 x)
;;                   (bvplus (+ 1 xsize) 1 x)))
;;   :hints (("Goal" :in-theory (e/d (bvplus
;;                                    UNSIGNED-BYTE-P-FORCED)
;;                                   (
;;                                    PLUS-BECOMES-BVPLUS
;;                                    <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM
;;                                    )))))


;; Special case for when the + is inside an unsigned-byte-p.
(defthmd unsigned-byte-p-of-+-becomes-unsigned-byte-p-of-bvplus-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (posp xsize)
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (unsigned-byte-p size (+ x y))
                  (unsigned-byte-p size (bvplus (+ 1 (max xsize ysize)) x y))))
  :hints (("Goal" :use (:instance +-becomes-bvplus-axe)
           :in-theory (disable +-becomes-bvplus-axe equal-of-+-and-bv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;cheap, requires both x and y to be BVs (possibly constants)
(defthmd <-becomes-bvlt-axe-bind-free-and-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (< x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt (k x) (x y)  (free (max xsize ysize))))))

;cheap, requires both x and y to be BVs (possibly constants)
(defthmd <-becomes-bvlt-axe-bind-free-and-free
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p ysize y) ; free var
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvlt))))

;cheap, requires both x and y to be BVs (possibly constants)
(defthmd <-becomes-bvlt-axe-free-and-bind-free
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize axe-array) '(ysize))
                (unsigned-byte-p xsize x) ; free var
                (unsigned-byte-p-forced ysize y))
           (equal (< x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvlt))))

;deprecated?
(defthmd <-becomes-bvlt-dag
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size dag-array) '(size))
                (syntaxp (quotep k))
                (unsigned-byte-p size k)
                (unsigned-byte-p-forced size x))
           (equal (< k x) ; rename vars
                  (bvlt size k x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt (free size)))))

(defthmd <-becomes-bvlt-axe-bind-free-arg2
  (implies (and (axe-bind-free (bind-bv-size-axe y 'size dag-array) '(size))
                ;;(syntaxp (quotep x))
                (unsigned-byte-p size x)
                (unsigned-byte-p-forced size y))
           (equal (< x y)
                  (bvlt size x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt (free size) (x y) (k x)))))

(defthmd <-becomes-bvlt-axe-bind-free-arg1
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size dag-array) '(size))
                ;;(syntaxp (quotep y))
               (unsigned-byte-p size y)
               (unsigned-byte-p-forced size x))
          (equal (< x y)
                 (bvlt size x y)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced bvlt) (<-becomes-bvlt-free-alt <-becomes-bvlt-free))
           :use (:instance <-becomes-bvlt (x y) (k x)))))

;ttodo
;improve other rules like this!
(defthmd <-becomes-bvlt-dag-gen-better
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size dag-array) '(size)) ;ffffixme here and elsewhere abstain if x is a quotep?!! ;why?
                (syntaxp (not (quotep x)))
                (natp size)
                (integerp k)
                (unsigned-byte-p-forced size x))
           (equal (< k x)
                  ;;redid conc
                  (boolor (< k 0)
                          (booland (unsigned-byte-p size k)
                                   (bvlt size k x)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced unsigned-byte-p booland)
           :use (:instance <-becomes-bvlt-axe-bind-free-arg2 (x k) (y x)))))

;can loop when x=0?
;this one requires x not to be 0
(defthmd <-becomes-bvlt-dag-gen-better2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'size dag-array) '(size)) ;ffffixme here and elsewhere abstain if x is a quotep?!! ;why? can loop if k is a difference?
                (syntaxp (not (quotep x)))
                (not (equal x 0))
                (natp size)
                (integerp k)
                (unsigned-byte-p-forced size x))
           (equal (< k x)
;;redid conc to use bool ops
                  (boolor (< k 0)
                          (booland (unsigned-byte-p size k) ;fixme this can loop when k is a difference? because of UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   (bvlt size k x)))))
  :hints (("Goal" :use (:instance <-becomes-bvlt-dag-gen-better)
           :in-theory (disable <-becomes-bvlt-dag-gen-better))))

;; "safe" because it doesn't allow X to be a quote, so X really is a BV term
(defthmd <-becomes-bvlt-axe-bind-free-arg1-strong-safe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (syntaxp (not (quotep x))) ;why?
                (integerp y) ;drop?
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (if (< y 0) ;was <= but i prefer not to split on whether y=0
                      nil
                    (if (unsigned-byte-p xsize y)
                        (bvlt xsize x y)
                      t))))
  :hints (("Goal" :use (:instance <-becomes-bvlt-axe-bind-free-arg1 (size xsize))
           :in-theory (e/d (unsigned-byte-p
                            ;;unsigned-byte-p-when-unsigned-byte-p-free-better
                            unsigned-byte-p-forced)
                           (<-becomes-bvlt-axe-bind-free-arg1)))))

;fixme think about when x=0
(defthmd <-becomes-bvlt-axe-bind-free-arg1-strong
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
;;;                (syntaxp (not (quotep x))) ;why?
                (integerp y) ;drop?
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (if (< y 0) ;was <= but i prefer not to split on whether y=0
                      nil
                    (if (unsigned-byte-p xsize y)
                        (bvlt xsize x y)
                      t))))
  :hints (("Goal" :use (:instance <-becomes-bvlt-axe-bind-free-arg1-strong-safe)
           :in-theory (disable <-becomes-bvlt-axe-bind-free-arg1-strong-safe))))
