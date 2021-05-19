; Alists from symbols to terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; See also symbol-pseudoterm-alistp in [books]/std/typed-alists/symbol-pseudoterm-alistp.lisp.

;; Recognize an alist from symbols to pseudo-terms
(defund symbol-term-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (consp (car x))
                (symbolp (car (car x)))
                (pseudo-termp (cdr (car x)))
                (symbol-term-alistp (cdr x))))))

(defthm symbol-term-alistp-of-cons
  (equal (symbol-term-alistp (cons pair alist))
         (and (consp pair)
              (symbolp (car pair))
              (pseudo-termp (cdr pair))
              (symbol-term-alistp alist)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbol-term-alistp-of-acons
  (equal (symbol-term-alistp (acons key val alist))
         (and (symbolp key)
              (pseudo-termp val)
              (symbol-term-alistp alist)))
  :hints (("Goal" :in-theory (enable acons))))

(defthm symbol-term-alistp-of-cdr
  (implies (symbol-term-alistp alist)
           (symbol-term-alistp (cdr alist)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

;; Disabled by default since this could be expensive, but see
;; symbolp-of-car-of-car-when-symbol-term-alistp-type below.
(defthmd symbolp-of-car-of-car-when-symbol-term-alistp
  (implies (symbol-term-alistp x)
           (symbolp (car (car x))))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbolp-of-car-of-car-when-symbol-term-alistp-type
  (implies (symbol-term-alistp x)
           (symbolp (car (car x))))
  :rule-classes :type-prescription
  :hints (("Goal" :by symbolp-of-car-of-car-when-symbol-term-alistp)))

;; TODO: Add a -cheap version and disable this one?
(defthm pseudo-termp-of-cdr-of-car-when-symbol-term-alistp
  (implies (symbol-term-alistp x)
           (pseudo-termp (cdr (car x))))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbol-alistp-when-symbol-term-alistp-cheap
  (implies (symbol-term-alistp x)
           (symbol-alistp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbol-term-alistp-forward-to-symbol-alistp
  (implies (symbol-term-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

(defthm consp-of-car-when-symbol-term-alistp-cheap
  (implies (symbol-term-alistp alist)
           (equal (consp (car alist))
                  (consp alist)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm iff-of-car-when-symbol-term-alistp-cheap
  (implies (symbol-term-alistp alist)
           (iff (car alist)
                alist))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

;; If there is no binding for form in alist, assco-equal give nil, which
;; happens to have a cdr (also nil) that is a pseudo-term.
(defthm pseudo-termp-of-cdr-of-assoc-equal-when-symbol-term-alistp
  (implies (symbol-term-alistp alist)
           (pseudo-termp (cdr (assoc-equal form alist))))
  :hints (("Goal" :in-theory (enable assoc-equal symbol-term-alistp))))

(defthm symbol-term-alistp-of-pairlis$
  (implies (and (symbol-listp syms)
                (pseudo-term-listp terms))
           (symbol-term-alistp (pairlis$ syms terms)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm symbol-term-alistp-of-pairlis$-alt
  (implies (equal (len vars) (len terms))
           (equal (symbol-term-alistp (pairlis$ vars terms))
                  (and (symbol-listp (true-list-fix vars))
                       (pseudo-term-listp (true-list-fix terms)))))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))
