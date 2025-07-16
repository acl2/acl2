; A lightweight book about the built-in function assoc-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable assoc-equal))

(defthm assoc-equal-of-nil
  (equal (assoc-equal x nil)
         nil)
  :hints (("Goal" :in-theory (enable assoc-equal))))

;; Kept disabled for speed
(defthmd assoc-equal-when-not-consp
  (implies (not (consp alist))
           (equal (assoc-equal x alist)
                  nil))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-when-not-consp-cheap
  (implies (not (consp alist))
           (equal (assoc-equal x alist)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;; Disabled because this can fire on a call to ASSOC-EQUAL where the second
;; argument is a (non-empty) constant list.  See assoc-equal-of-cons-safe
;; below.
(defthmd assoc-equal-of-cons
  (equal (assoc-equal x (cons pair alist))
         (if (equal x (car pair))
             pair
           (assoc-equal x alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;; Avoids cases splits if the second argument to ASSOC-EQUAL is constant.
(defthm assoc-equal-of-cons-safe
  (implies (syntaxp (not (and (quotep pair)
                              (quotep alist))))
           (equal (assoc-equal x (cons pair alist))
                  (if (equal x (car pair))
                      pair
                    (assoc-equal x alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-of-acons
  (equal (assoc-equal x (acons key datum alist))
         (if (equal x key)
             (cons x datum)
           (assoc-equal x alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-of-acons-diff
  (implies (not (equal x key))
           (equal (assoc-equal x (acons key datum alist))
                  (assoc-equal x alist))))

(defthm assoc-equal-of-acons-same
  (equal (assoc-equal x (acons x datum alist))
         (cons x datum)))

(defthm assoc-equal-of-append-1
  (implies (assoc-equal x alist1)
           (equal (assoc-equal x (append alist1 alist2))
                  (assoc-equal x alist1)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-of-append-2
  (implies (and (not (assoc-equal x alist1))
                (or (alistp alist1)
                    x))
           (equal (assoc-equal x (append alist1 alist2))
                  (assoc-equal x alist2)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-of-append
  (implies (or (alistp alist1)
               x)
           (equal (assoc-equal x (append alist1 alist2))
                  (if (assoc-equal x alist1)
                      (assoc-equal x alist1)
                    (assoc-equal x alist2))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;; Better than the version in std.
;; Can help when assoc-equal-type cannot fire due to the hyps needing rewriting to be relieved.
(defthm consp-of-assoc-equal-gen
  (implies (or (alistp alist)
               key)
           (iff (consp (assoc-equal key alist))
                (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable alistp assoc-equal))))

;; Not sure which normal form is better
(defthmd assoc-equal-iff-member-equal-of-strip-cars
  (implies (or (alistp alist)
               key)
           (iff (assoc-equal key alist)
                (member-equal key (strip-cars alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm assoc-equal-when-member-equal-of-strip-cars-iff-cheap
  (implies (and (syntaxp (not (equal key ''nil))) ; prevent loops
                (member-equal key (strip-cars alist)))
           (iff (assoc-equal key alist)
                (if (equal nil key)
                    (assoc-equal nil alist) ; more concrete than the lhs
                  t)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :hints (("Goal" :in-theory (enable assoc-equal member-equal))))

;; Not sure which normal form is better
(defthmd member-equal-of-strip-cars-iff-assoc-equal
  (implies (or (alistp alist)
               key)
           (iff (member-equal key (strip-cars alist))
                (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;; Note: No hyp about alistp
(defthmd member-equal-of-strip-cars-when-assoc-equal
  (implies (assoc-equal key alist)
           (member-equal key (strip-cars alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(theory-invariant (incompatible (:rewrite assoc-equal-iff-member-equal-of-strip-cars)
                                (:rewrite member-equal-of-strip-cars-iff-assoc-equal)))

(defthm assoc-equal-type
  (implies (or x ;if X is nil, and ALIST contains an atom, ASSOC-EQUAL might return that atom
               (alistp alist))
           (or (consp (assoc-equal x alist))
               (null (assoc-equal x alist))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable alistp assoc-equal))))

(defthm <-of-0-and-len-of-assoc-equal-iff
  (implies (alistp alist)
           (iff (< 0 (len (assoc-equal key alist)))
                (assoc-equal key alist))))

(defthm car-of-assoc-equal-cheap
  (implies (assoc-equal x alist)
           (equal (car (assoc-equal x alist))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm car-of-assoc-equal-strong
  (equal (car (assoc-equal x alist))
         (if (assoc-equal x alist)
             x
           nil))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm acl2-count-of-assoc-equal-linear
  (<= (acl2-count (assoc-equal x alist))
      (acl2-count alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm acl2-count-of-assoc-equal-when-consp-linear
  (implies (or (assoc-equal x alist)
               (consp alist))
           (< (acl2-count (assoc-equal x alist))
              (acl2-count alist)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable assoc-equal))))
