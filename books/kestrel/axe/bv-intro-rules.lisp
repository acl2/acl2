; Axe rules about BVs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
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
;(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
;(include-book "known-booleans")
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ;drop?
(local (include-book "kestrel/bv/rules3" :dir :system)) ;for *-becomes-bvmult
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

(defthmd myif-becomes-bvif-4-axe
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free variable
                (unsigned-byte-p ysize y) ; ysize is a free variable
                )
           (equal (myif test x y)
                  (bvif (max xsize ysize) test x y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;cheap
(defthmd <-becomes-bvlt-axe-both
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (< x y)
                  (bvlt (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance <-becomes-bvlt (k x) (x y)  (free (max xsize ysize))))))

;cheap
(defthmd <-becomes-bvlt-axe-2
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (unsigned-byte-p freeysize y)
                (unsigned-byte-p-forced xsize x))
           (equal (< x y)
                  (bvlt (max xsize freeysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvlt))))

;cheap
(defthmd <-becomes-bvlt-axe-3
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize axe-array) '(ysize))
                (unsigned-byte-p freexsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (< x y)
                  (bvlt (max freexsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;add axe to name
;todo: more rules like this?
(defthmd mod-becomes-bvmod
  (implies (and (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced ysize y)
                (unsigned-byte-p ysize x) ;new..
                )
           (equal (mod x y)
                  (bvmod ysize x y)))
  :hints (("Goal" :in-theory (enable mod-becomes-bvmod-core unsigned-byte-p-forced))))

;name
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

;name
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

;name
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
                (unsigned-byte-p-forced xsize x)
                )
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
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x)
                (natp y))
           (equal (logand x y)
                  (bvand xsize x y)))
  :hints (("Goal" :use (:instance acl2::logand-becomes-bvand (size xsize) (acl2::y y))
           :in-theory (disable acl2::logand-becomes-bvand))))

(defthmd logand-becomes-bvand-arg2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p-forced xsize x)
                (natp y))
           (equal (logand y x)
                  (bvand xsize y x)))
  :hints (("Goal":use (:instance acl2::logand-becomes-bvand (size xsize) (acl2::y y))
           :in-theory (disable acl2::logand-becomes-bvand))))

(defthmd logior-becomes-bvor-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize acl2::dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (logior x y)
                  (bvor (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd logxor-becomes-bvxor-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (unsigned-byte-p-forced xsize x)
                (unsigned-byte-p-forced ysize y))
           (equal (logxor x y)
                  (bvxor (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;rename?
(defthmd logtail-becomes-slice-bind-free-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'newsize dag-array) '(newsize))
                (<= n newsize) ;drop?
                (integerp newsize)
                (unsigned-byte-p-forced newsize x) ;switched to usb-forced? (also elsewhere!)
                (integerp x) ;drop
                (natp n))
           (equal (logtail n x)
                  (slice (+ -1 newsize) n x)))
  :hints (("Goal" :use (:instance logtail-becomes-slice-bind-free)
           :in-theory (e/d (unsigned-byte-p-forced) (logtail-becomes-slice-bind-free)))))
