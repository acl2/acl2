; Rules to chop arguments using trim
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-syntax")
(include-book "trim")
;(include-book "bvsx")
;(include-book "leftrotate32")
(include-book "bvnot")
(include-book "bvcat")
(include-book "bvif")
(include-book "bvplus")
(include-book "bvmult")
(include-book "bvminus")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "trim-rules") ; need these whenever we introduce trim

;; TODO: Should we only trim when the sizes involved are constants?

;BOZO lots more rules like this

(defthmd bvnot-trim-all
  (implies (and (syntaxp (term-should-be-trimmed size x ':all))
                (natp size))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename?
(defthm bvxor-trim-arg1
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize x) (innersize))
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
           (equal (bvxor outersize x y)
                  (bvxor outersize (trim outersize x) y)))
  :hints (("Goal" :in-theory (enable bvxor trim))))

;rename?
(defthm bvxor-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize y) (innersize))
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
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
                (integerp lowval)
                (integerp highval)
                (integerp lowval)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bvcat-trim-arg4
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'newsize lowval) (newsize))
                (syntaxp (quotep lowsize))
                (< lowsize newsize)
                (natp highsize)
                (natp newsize)
                (integerp lowval)
                (integerp highval)
                (integerp lowval)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvcat-of-bvchop-low trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvif-trim-arg3
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize x) (innersize)) ;bozo newsize is a bad name
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
           (equal (bvif outersize test x y)
                  (bvif outersize test (trim outersize x) y)))
  :hints (("Goal" :in-theory (enable bvif trim))))

(defthm bvif-trim-arg4
  (implies (and (bind-free (bind-var-to-bv-term-size-if-trimmable 'innersize y) (innersize)) ;bozo newsize is a bad name
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
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
