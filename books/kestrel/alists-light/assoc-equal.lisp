; A lightweight book about the built-in function assoc-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

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

;; matches std
;; Can help when assoc-equal-type cannot fire due to the hyps needing rewriting to be relieved.
(defthm consp-of-assoc-equal
  (implies (alistp alist)
           (iff (consp (assoc-equal key alist))
                (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable alistp assoc-equal))))

(defthmd assoc-equal-iff
  (implies (alistp alist)
           (iff (assoc-equal key alist)
                (member-equal key (strip-cars alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

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
