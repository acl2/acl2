; Rules about lookup-equal
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-equal-def")

(defthm lookup-equal-of-nil
  (equal (lookup-equal key nil)
         nil)
  :hints (("Goal" :in-theory (enable lookup-equal))))

;disabled but see lookup-equal-of-cons-safe below
(defthmd lookup-equal-of-cons
  (equal (lookup-equal key (cons pair alist))
         (if (equal key (car pair))
             (cdr pair)
           (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

;; The syntaxp hyp prevents splitting into many cases when lookup-equal's
;; second argument is a big constant alist (which ACL2 will unify with the call
;; of CONS).
(defthm lookup-equal-of-cons-safe
  (implies (syntaxp (not (and (quotep pair)
                              (quotep alist))))
           (equal (lookup-equal key (cons pair alist))
                  (if (equal key (car pair))
                      (cdr pair)
                    (lookup-equal key alist))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-of-cons-of-cons-safe
  (implies (syntaxp (and (quotep key)
                         (quotep key2)))
           (equal (lookup-equal key (cons (cons key2 val) alist))
                  (if (equal key key2) ; gets evaluated
                      val
                      (lookup-equal key alist))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-of-acons
  (equal (lookup-equal key (acons key2 val alist))
         (if (equal key key2)
             val
           (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable))))

(defthm lookup-equal-of-acons-same
  (equal (lookup-equal key (acons key val alist))
         val))

(defthm lookup-equal-of-acons-diff
  (implies (not (equal key key2))
           (equal (lookup-equal key (acons key2 val alist))
                  (lookup-equal key alist))))

(defthmd lookup-equal-of-append
  (implies (or (alistp alist1)
               key)
           (equal (lookup-equal key (append alist1 alist2))
                  (if (assoc-equal key alist1)
                      (lookup-equal key alist1)
                    (lookup-equal key alist2))))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm lookup-equal-of-caar
  (equal (lookup-equal (caar alist) alist)
         (cdar alist))
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

(defthm lookup-equal-forward-to-assoc-equal
  (implies (lookup-equal key alist)
           (assoc-equal key alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm assoc-equal-when-lookup-equal-cheap
  (implies (lookup-equal key alist)
           (assoc-equal key alist))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthmd cdr-of-assoc-equal-becomes-lookup-equal
  (equal (cdr (assoc-equal key alist))
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(theory-invariant (incompatible (:rewrite cdr-of-assoc-equal-becomes-lookup-equal) (:definition lookup-equal)))
