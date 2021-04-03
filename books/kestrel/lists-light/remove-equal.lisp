; A lightweight book about the built-in function remove-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable remove-equal))

;; A simple/abbreviation rule.
(defthm remove-equal-of-nil
  (equal (remove-equal x nil)
         nil)
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthmd remove-equal-when-not-consp
  (implies (not (consp l))
           (equal (remove-equal x l)
                  nil))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm remove-equal-when-not-consp-cheap
  (implies (not (consp l))
           (equal (remove-equal x l)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm remove-equal-of-cons
  (equal (remove-equal x (cons y l))
         (if (equal x y)
             (remove-equal x l)
           (cons y (remove-equal x l))))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm remove-equal-of-cons-same
  (equal (remove-equal x (cons x l))
         (remove-equal x l))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm remove-equal-of-car-same
  (equal (remove-equal (car l) l)
         (remove-equal (car l) (cdr l)))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm len-of-remove-equal-linear
  (<= (len (remove-equal x l))
      (len l))
  :rule-classes ((:linear :trigger-terms ((len (remove-equal x l)))))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm equal-of-len-of-remove-equal-and-len-same
   (equal (equal (len (remove-equal a x)) (len x))
          (not (member-equal a x))))

(defthm <-of-len-of-remove-equal-and-len-same-iff
  (iff (< (len (remove-equal a x)) (len x))
       (member-equal a x)))

;; ACL2 puts in a loop-stopper.
(defthm remove-equal-of-remove-equal
  (equal (remove-equal x (remove-equal y l))
         (remove-equal y (remove-equal x l)))
  :hints (("Goal" :in-theory (enable remove-equal))))

(defthm not-member-equal-of-remove-equal
  (implies (not (member-equal x l))
           (not (member-equal x (remove-equal y l)))))

(defthm member-equal-of-remove-equal-irrel-iff
  (implies (not (equal x y))
           (iff (member-equal x (remove-equal y l))
                (member-equal x l))))

(defthm nat-listp-of-remove-equal
  (implies (nat-listp x)
           (nat-listp (remove-equal a x)))
  :hints (("Goal" :in-theory (enable remove-equal nat-listp))))
