; Lists of items that are either nodenums or nodenums wrapped in NOT
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

(include-book "kestrel/utilities/forms" :dir :system) ;for call-of
(include-book "kestrel/utilities/polarity" :dir :system) ;for want-to-weaken
(include-book "kestrel/typed-lists-light/all-less" :dir :system)

;; Recognizes an item of the form <nodenum> or (not <nodenum>).
(defund possibly-negated-nodenump (item)
  (declare (xargs :guard t))
  (or (natp item)
      (and (call-of 'not item)
           (true-listp item)
           (eql 1 (len (fargs item))) ;(consp (cdr item))
           (natp (farg1 item)))))

(defthm possibly-negated-nodenump-when-natp
  (implies (natp nodenum)
           (possibly-negated-nodenump nodenum))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

(defthm possibly-negated-nodenump-of-list-of-not
  (equal (possibly-negated-nodenump (list 'not nodenum))
         (natp nodenum))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

;we'll use consp as the normal form
(defthmd cdr-iff-when-possibly-negated-nodenump
  (implies (possibly-negated-nodenump item)
           (iff (cdr item)
                (consp item)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

;we'll use consp as the normal form
(defthmd consp-of-cdr-when-possibly-negated-nodenump
  (implies (possibly-negated-nodenump item)
           (equal (consp (cdr item))
                  (consp item)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))

(defthmd natp-of-cadr-when-possibly-negated-nodenump
  (implies (possibly-negated-nodenump item)
           (equal (natp (cadr item))
                  (consp item)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenump))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a true-list of possible-negated-nodenums
(defund possibly-negated-nodenumsp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (null lst) ;new
    (and (possibly-negated-nodenump (first lst))
         (possibly-negated-nodenumsp (rest lst)))))

(defthm possibly-negated-nodenumsp-forward-to-true-listp
  (implies (possibly-negated-nodenumsp items)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

;disable outside axe?
(defthm true-listp-when-possibly-negated-nodenumsp
  (implies (possibly-negated-nodenumsp context)
           (true-listp context))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenump-of-car
  (implies (possibly-negated-nodenumsp items)
           (equal (possibly-negated-nodenump (car items))
                  (consp items)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenumsp-of-cons
  (equal (possibly-negated-nodenumsp (cons item list))
         (and (possibly-negated-nodenump item)
              (possibly-negated-nodenumsp list)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenumsp-of-cdr
  (implies (possibly-negated-nodenumsp items)
           (possibly-negated-nodenumsp (cdr items)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp))))

;why? disable?
(defthm possibly-negated-nodenumsp-of-cdr-2
  (implies (possibly-negated-nodenump (car items))
           (equal (possibly-negated-nodenumsp (cdr items))
                  (possibly-negated-nodenumsp items))))

(defthm possibly-negated-nodenumsp-of-intersection-equal
  (implies (and (possibly-negated-nodenumsp context1)
                (possibly-negated-nodenumsp context2))
           (possibly-negated-nodenumsp (intersection-equal context1 context2))))

(defthm possibly-negated-nodenumsp-of-add-to-set-equal
  (implies (and (possibly-negated-nodenump item)
                (possibly-negated-nodenumsp context))
           (possibly-negated-nodenumsp (add-to-set-equal item context)))
  :hints (("Goal" :in-theory (enable add-to-set-equal possibly-negated-nodenumsp))))

;; (defthm possibly-negated-nodenumsp-of-singleton
;;   (implies (natp nodenum)
;;            (possibly-negated-nodenumsp (list nodenum)))
;;   :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
;;                                      possibly-negated-nodenump))))

(defthm integerp-of-car-when-possibly-negated-nodenumsp-weaken-cheap
  (implies (and (syntaxp (want-to-weaken (integerp (car items))))
                (possibly-negated-nodenumsp items)
                (consp items))
           (equal (integerp (car items))
                  (or (not (consp (car items)))
                      (not (eq 'not (car (car items))))
                      (not (natp (farg1 (car items))))
                      (cdr (fargs (car items))))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

(defthm consp-of-car-when-possibly-negated-nodenumsp-weaken-cheap
  (implies (and (syntaxp (want-to-weaken (consp (car items))))
                (possibly-negated-nodenumsp items)
                (consp items))
           (equal (consp (car items))
                  (not (natp (car items)))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil)))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     possibly-negated-nodenump))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund strip-not-from-possibly-negated-nodenum (item)
  (declare (xargs :guard (possibly-negated-nodenump item)
                  :guard-hints (("Goal" :in-theory (enable possibly-negated-nodenump)))))
  (if (consp item)
      (farg1 item)
    item))

(defthm natp-of-strip-not-from-possibly-negated-nodenum
  (implies (possibly-negated-nodenump item)
           (natp (strip-not-from-possibly-negated-nodenum item)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum
                                     possibly-negated-nodenump))))

(defthm rationalp-of-strip-not-from-possibly-negated-nodenum
  (implies (possibly-negated-nodenump item)
           (rationalp (strip-not-from-possibly-negated-nodenum item)))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

(defthm integerp-of-strip-not-from-possibly-negated-nodenum
  (implies (possibly-negated-nodenump item)
           (integerp (strip-not-from-possibly-negated-nodenum item)))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

(defthm <=-of-0-and-strip-not-from-possibly-negated-nodenum
  (implies (possibly-negated-nodenump item)
           (<= 0 (strip-not-from-possibly-negated-nodenum item)))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

(defthm strip-not-from-possibly-negated-nodenum-when-not-consp
  (implies (not (consp item))
           (equal (strip-not-from-possibly-negated-nodenum item)
                  item))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: instead of using this in a claim of the form (all-< (strip-nots-from-possibly-negated-nodenums items) dag-len), consider bounded-possibly-negated-nodenumsp
;; TODO: Consider a tail-recursive version, especially if we don't care about the order
(defund strip-nots-from-possibly-negated-nodenums (items)
  (declare (xargs :guard (possibly-negated-nodenumsp items)
                  :guard-hints (("Goal" :expand (possibly-negated-nodenumsp items)))))
  (if (endp items)
      nil
    (cons (strip-not-from-possibly-negated-nodenum (first items))
          (strip-nots-from-possibly-negated-nodenums (rest items)))))

(defthm rational-listp-of-strip-nots-from-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (rational-listp (strip-nots-from-possibly-negated-nodenums items)))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     possibly-negated-nodenumsp))))

(defthm nat-listp-of-strip-nots-from-possibly-negated-nodenums
  (implies (possibly-negated-nodenumsp items)
           (nat-listp (strip-nots-from-possibly-negated-nodenums items)))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     possibly-negated-nodenumsp))))

(defthm consp-of-strip-nots-from-possibly-negated-nodenums
  (equal (consp (strip-nots-from-possibly-negated-nodenums items))
         (consp items))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bounded-possibly-negated-nodenump (item bound)
  (declare (xargs :guard (rationalp bound))) ; say integerp?
  (or (and (natp item)
           (< item bound))
      (and (call-of 'not item)
           (consp (cdr item))
           (null (cddr item))
           (natp (farg1 item))
           (< (farg1 item) bound))))

(defthm possibly-negated-nodenump-when-bounded-possibly-negated-nodenump
  (implies (bounded-possibly-negated-nodenump item bound)
           (possibly-negated-nodenump item))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenump possibly-negated-nodenump))))

(defthm bounded-possibly-negated-nodenump-when-not-consp
  (implies (not (consp item))
           (equal (bounded-possibly-negated-nodenump item bound)
                  (and (natp item)
                       (< item bound))))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenump))))

(defthm <-of-strip-not-from-possibly-negated-nodenum
  (implies (bounded-possibly-negated-nodenump item bound)
           (< (strip-not-from-possibly-negated-nodenum item) bound))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum
                                     bounded-possibly-negated-nodenump))))

(defthmd <-of-cadr-when-bounded-possibly-negated-nodenump
  (implies (and (bounded-possibly-negated-nodenump item bound)
                (consp item))
           (< (cadr item) bound))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenump))))

(defthmd <-when-bounded-possibly-negated-nodenump
  (implies (bounded-possibly-negated-nodenump item bound)
           (< item bound))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenump))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;requires 0 <= nodenum < bound for all the nodenums in the context:
(defund bounded-possibly-negated-nodenumsp (items bound)
  (declare (type rational bound))
  (if (atom items)
      (null items) ;new
    (let ((item (first items)))
      (and (bounded-possibly-negated-nodenump item bound)
           (bounded-possibly-negated-nodenumsp (rest items) bound)))))

(defthm bounded-possibly-negated-nodenumsp-forward-to-true-listp
  (implies (bounded-possibly-negated-nodenumsp items bound)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp))))

(defthm bounded-possibly-negated-nodenumsp-forward-to-possibly-negated-nodenumsp
  (implies (bounded-possibly-negated-nodenumsp items bound)
           (possibly-negated-nodenumsp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp
                                     possibly-negated-nodenumsp))))

(defthm possibly-negated-nodenumsp-when-bounded-possibly-negated-nodenumsp
  (implies (bounded-possibly-negated-nodenumsp items bound)
           (possibly-negated-nodenumsp items))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenumsp))))

(defthm bounded-possibly-negated-nodenumsp-of-nil
  (bounded-possibly-negated-nodenumsp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp))))

(defthm bounded-possibly-negated-nodenumsp-of-cons
  (equal (bounded-possibly-negated-nodenumsp (cons item items) dag-len)
         (and (bounded-possibly-negated-nodenump item dag-len)
              (bounded-possibly-negated-nodenumsp items dag-len)))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp))))

(defthm bounded-possibly-negated-nodenumsp-of-cdr
  (implies (bounded-possibly-negated-nodenumsp items dag-len)
           (bounded-possibly-negated-nodenumsp (cdr items) dag-len))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp))))

(defthm bounded-possibly-negated-nodenums-of-car
  (implies (and (bounded-possibly-negated-nodenumsp items dag-len)
                (consp items))
         (bounded-possibly-negated-nodenump (car items) dag-len))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp))))

(defthm bounded-possibly-negated-nodenumsp-monotone
  (implies (and (bounded-possibly-negated-nodenumsp context bound1)
                (<= bound1 bound)
                (natp bound1)
                (natp bound))
           (bounded-possibly-negated-nodenumsp context bound))
  :hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp bounded-possibly-negated-nodenump))))

(defthm all-<-of-strip-nots-from-possibly-negated-nodenums
  (implies (bounded-possibly-negated-nodenumsp items bound)
           (all-< (strip-nots-from-possibly-negated-nodenums items) bound))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     bounded-possibly-negated-nodenumsp))))
