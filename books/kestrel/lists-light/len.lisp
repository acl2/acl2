; A lightweight book about the built-in function len.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable len))

;; same as in std
(defthm len-of-cons
  (equal (len (cons a x))
         (+ 1 (len x)))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-when-not-consp-cheap
  (implies (not (consp x))
           (equal (len x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable len))))

(defthm consp-when-len-greater
  (implies (and (< n (len x)) ;n is a free var
                (natp n))
           (consp x)))

(defthm equal-of-len-and-0
  (equal (equal 0 (len x))
         (not (consp x)))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-of-cdr-linear
  (<= (len (cdr x)) (len x))
  :rule-classes :linear)

(defthm len-of-cdr-linear-strong
  (implies (consp x)
           (= (len (cdr x)) (+ -1 (len x))))
  :rule-classes :linear)

(defthm len-positive-when-consp-linear-cheap
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes ((:linear :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable len))))

(defthm consp-forward-to-len-bound
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :forward-chaining)

(defthm <-of-0-and-len-forward-to-consp
  (implies (< 0 (len x))
           (consp x))
  :rule-classes :forward-chaining)

(defthm not-consp-of-cdr-forward-to-len-bound
  (implies (not (consp (cdr x)))
           (<= (len x) 1))
  :rule-classes :forward-chaining)

;; A pretty strong rule.
(defthm len-of-cdr
  (equal (len (cdr x))
         (if (equal 0 (len x))
             0
           (+ -1 (len x)))))

(theory-invariant (incompatible (:rewrite len-of-cdr) (:definition len)))

;rename
;; The RHS makes crystal clear the fact that we don't care about the values of x, only its length.
(defthmd consp-of-cdr
  (equal (consp (cdr x))
         (< 1 (len x)))
  :hints (("Goal" :in-theory (e/d (len) (len-of-cdr)))))

;loops with cdr-iff
(defthmd <-of-1-and-len-when-true-listp
  (implies (true-listp x)
           (iff (< 1 (len x))
                (cdr x)))
  :hints (("Goal" :in-theory (e/d (len) (len-of-cdr)))))

;pretty aggressive
(defthmd consp-to-len-bound
  (equal (consp x)
         (< 0 (len x)))
  :hints (("Goal" :in-theory (e/d (len) (len-of-cdr)))))

;; Disabled by default
(defthmd <-of-0-and-len
  (equal (< 0 (len x))
         (consp x))
  :hints (("Goal" :in-theory (e/d (len) (LEN-OF-CDR)))))

;todo: add versions with more cdrs?
(defthm consp-of-cdr-when-len-known
  (implies (and (equal (len x) k)
                (syntaxp (quotep k)))
           (equal (consp (cdr x))
                  (< 1 k) ;gets computed
                  ))
  :hints (("Goal" :in-theory (enable consp-of-cdr))))

(defthmd consp-from-len
  (implies (< 0 (len x))
           (consp x)))

(defthm consp-from-len-cheap
  (implies (< 0 (len x))
           (consp x))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthmd <-of-len-and-2-cases
  (equal (< (len x) 2)
         (or (not (consp x))
             (equal 1 (len x)))))

(defthmd equal-of-len-and-1
  (implies (true-listp x)
           (equal (equal 1 (len x))
                  (equal x (list (car x))))))

;; not needed for more than 3 cdrs if we turn those into nthcdr
(defthm len-of-cddr-when-equal-of-len
  (implies (and (equal (len x) k) ; k is a free var
                (syntaxp (quotep k))
                (<= 2 k))
           (equal (len (cddr x))
                  (+ -2 k))))

;if we know that the length is equal to something, turn a consp question into a question about that thing..
(defthm consp-when-len-equal-constant
  (implies (and (equal (len x) free) ;putting the free variable first made this a binding hyp, which led to loops
                (syntaxp (quotep free))) ;new to prevent loops with len-equal-0-rewrite-alt - could just require free to be smaller than (len x)?
           (equal (consp x)
                  (< 0 free)))
  :hints (("Goal" :in-theory (e/d (len) (len-of-cdr)))))
