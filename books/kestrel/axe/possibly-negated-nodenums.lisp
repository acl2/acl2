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
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

(defthm strip-not-from-possibly-negated-nodenum-when-not-consp
  (implies (not (consp item))
           (equal (strip-not-from-possibly-negated-nodenum item)
                  item))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable strip-not-from-possibly-negated-nodenum))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: instead of using this in a claim of the form (all-< (strip-nots-from-possibly-negated-nodenums items) dag-len), consider bounded-possibly-negated-nodenumsp
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

;requires 0 <= nodenum < bound for all the nodenums in the context:
(defun bounded-possibly-negated-nodenumsp (lst bound)
  (declare (type rational bound))
  (if (atom lst)
      (null lst) ;new
    (let ((item (first lst)))
      (and (or (and (natp item)
                    (< item bound))
               (and (call-of 'not item)
                    (consp (cdr item))
                    (null (cddr item))
                    (natp (farg1 item))
                    (< (farg1 item) bound)))
           (bounded-possibly-negated-nodenumsp (rest lst) bound)))))

(defthm possibly-negated-nodenumsp-when-bounded-possibly-negated-nodenumsp
  (implies (bounded-possibly-negated-nodenumsp lst bound)
           (possibly-negated-nodenumsp lst))
  :hints (("Goal" :in-theory (enable possibly-negated-nodenumsp
                                     bounded-possibly-negated-nodenumsp))))
