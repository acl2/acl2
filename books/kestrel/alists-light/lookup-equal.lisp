; Lookup a key in an alist using EQUAL
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;; TODO: Standardize variable names in theorems.

;; Look up KEY in ALIST, using equal as the test.
(defund lookup-equal (key alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal key alist)))

(defthm lookup-equal-of-nil
  (equal (lookup-equal key nil)
         nil)
  :hints (("Goal" :in-theory (enable lookup-equal))))

;disabled in favor of lookup-equal-of-cons-safe
(defthmd lookup-equal-of-cons
  (equal (lookup-equal key (cons a rst))
         (if (equal key (car a))
             (cdr a)
           (lookup-equal key rst)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

;prevents splitting into many cases when lookup-equal's second argument is a big constant alist
(defthm lookup-equal-of-cons-safe
  (implies (syntaxp (not (and (quotep a)
                              (quotep rst))))
           (equal (lookup-equal key (cons a rst))
                  (if (equal key (car a))
                      (cdr a)
                    (lookup-equal key rst))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-of-acons
  (equal (lookup-equal key (acons a val rst))
         (if (equal key a)
             val
           (lookup-equal key rst)))
  :hints (("Goal" :in-theory (enable))))

(defthm lookup-equal-of-acons-same
  (equal (lookup-equal key (acons key x y))
         x))

(defthm lookup-equal-of-acons-diff
  (implies (not (equal key key2))
           (equal (lookup-equal key (acons key2 x y))
                  (lookup-equal key y))))

(defthmd lookup-equal-of-append
  (implies (or (alistp x)
               key)
           (equal (lookup-equal key (append x y))
                  (if (assoc-equal key x)
                      (lookup-equal key x)
                    (lookup-equal key y))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-of-caar
  ;;(implies t (consp pairs)
  (equal (lookup-equal (caar pairs) pairs)
         (cdar pairs))
  ;;)
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-when-not-consp-cheap
  (implies (not (consp alist))
           (equal (lookup-equal key alist)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-when-not-assoc-equal-cheap
  (implies (not (assoc-equal key alist))
           (equal (lookup-equal key alist)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable lookup-equal))))
