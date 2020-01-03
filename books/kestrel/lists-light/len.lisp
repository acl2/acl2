; A lightweight book about the built-in function len.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
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

(defthmd consp-of-cdr
  (equal (consp (cdr x))
         (< 1 (len x)))
  :hints (("Goal" :in-theory (e/d (len) (len-of-cdr)))))

;pretty aggressive
(defthmd consp-to-len-bound
  (equal (consp x)
         (< 0 (len x)))
  :hints (("Goal" :in-theory (e/d (len) (len-of-cdr)))))

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
