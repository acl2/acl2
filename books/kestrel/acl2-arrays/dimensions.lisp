; A lightweight book about the built-in function dimensions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable dimensions))

;; We prefer a call to the function DIMENSIONS instead of its expanded form,
;; but some functions use the expanded form directly, so we use this rule to
;; convert things into our normal form.
(defthm dimensions-intro
  (equal (cadr (assoc-keyword :dimensions (cdr (header name l))))
         (dimensions name l))
  :hints (("Goal" :in-theory (enable dimensions))))

(theory-invariant (incompatible (:rewrite dimensions-intro) (:definition dimensions)))

;; This one also collapses the call to header
;; Unfortunately, this has a free variable in the RHS.
(defthmd dimensions-intro2
  (equal (cadr (assoc-keyword :dimensions (cdr (assoc-equal :header l))))
         (dimensions name l))
  :hints (("Goal" :in-theory (e/d (dimensions header) (dimensions-intro)))))

(theory-invariant (incompatible (:rewrite dimensions-intro2) (:definition dimensions)))

(defthm true-listp-of-dimensions
  (implies (array1p array-name array)
           (true-listp (dimensions array-name array)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (dimensions)
                                  (dimensions-intro)))))

(defthm dimensions-of-cons
  (equal (dimensions array-name (cons entry alist))
         (if (eq :header (car entry))
             (cadr (assoc-keyword :dimensions (cdr entry)))
           (dimensions array-name alist)))
  :hints (("Goal" :in-theory (e/d (dimensions)
                                  (dimensions-intro)))))

(defthm natp-of-nth-of-0-and-dimensions-when-array1p
  (implies (array1p array-name array)
           (natp (nth 0 (dimensions array-name array))))
  :hints (("Goal" :in-theory (e/d (array1p dimensions) (dimensions-intro)))))

(defthm rationalp-of-nth-of-0-and-dimensions-when-array1p
  (implies (array1p array-name array)
           (rationalp (nth 0 (dimensions array-name array))))
  :hints (("Goal" :in-theory (e/d (array1p dimensions) (dimensions-intro)))))

(defthm consp-of-dimensions-when-array1p
  (implies (array1p dag-array-name dag-array)
           (consp (dimensions dag-array-name dag-array)))
  :hints (("Goal" :in-theory (e/d (array1p dimensions) (dimensions-intro)))))
