; A lightweight book about the built-in function acl2-count
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider disabling acl2-count here.

;todo: use polarities?
(defthm acl2-count-hack
  (implies (<= (acl2-count x) y)
           (< (acl2-count x) (+ 1 y))))

;todo: name and trigger-terms
(defthm acl2-count-car-bound
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes (:rewrite :linear)
  )

;todo: name and trigger-terms
(defthm acl2-count-cdr-bound
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes (:rewrite :linear)
  )

;; i think the chaining rules let us handle any car, cadr, caadddadadadar, etc.

(defthm acl2-count-car-chaining
  (implies (<= (acl2-count y) (acl2-count x))
           (<= (acl2-count (car y)) (acl2-count x)))
  :hints (("Goal" :in-theory (disable acl2-count))))

(defthm acl2-count-cdr-chaining
  (implies (<= (acl2-count y) (acl2-count x))
           (<= (acl2-count (cdr y)) (acl2-count x)))
  :hints (("Goal" :in-theory (disable acl2-count))))

;; ;todo: trigger-terms
;; (defthm acl2-count-of-car-when-consp
;;   (implies (consp x)
;;            (< (acl2-count (car x))
;;               (acl2-count x)))
;;   :rule-classes (:rewrite :linear)
;;   )

;; ;todo: trigger-terms
;; (defthm acl2-count-of-cdr-when-consp
;;   (implies (consp x)
;;            (< (acl2-count (cdr x))
;;               (acl2-count x)))
;;   :rule-classes (:rewrite :linear)
;;   )

;; a pretty strong linear rule
(defthm acl2-count-when-consp-linear
  (implies (consp x)
           (equal (acl2-count x)
                  (+ 1 (acl2-count (car x))
                     (acl2-count (cdr x)))))
  :rule-classes :linear)

(defthm <=-of-acl2-count-of-nthcdr
  (<= (acl2-count (nthcdr n lst))
      (acl2-count lst))
  :rule-classes (:rewrite (:linear :trigger-terms ((acl2-count (nthcdr n lst)))))
  :hints (("Goal" :induct (NTHCDR N LST)
           :in-theory (enable nthcdr))))

(defthm <-of-acl2-count-of-nthcdr
  (implies (and (consp lst)
                (posp n))
           (< (acl2-count (nthcdr n lst))
              (acl2-count lst)))
  :hints (("Goal" :induct (NTHCDR N LST)
           :in-theory (enable nthcdr))))

(defthm acl2-count-of-cons
  (equal (acl2-count (cons x y))
         (+ 1 (acl2-count x)
            (acl2-count y))))

(defthm <-of-acl2-count-of-remove1-equal
  (implies (member-equal a x)
           (< (acl2-count (remove1-equal a x))
              (acl2-count x)))
  :rule-classes (:rewrite (:linear :trigger-terms ((acl2-count (remove1-equal a x)))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm <=-of-acl2-count-of-remove1-equal
  (<= (acl2-count (remove1-equal a x))
      (acl2-count x))
  :rule-classes (:rewrite (:linear :trigger-terms ((acl2-count (remove1-equal a x)))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm equal-of-acl2-count-of-remove1-equal-and-acl2-count
  (equal (equal (acl2-count (remove1-equal a x))
                (acl2-count x))
         (if (member-equal a x)
             nil
           (equal (acl2-count (true-list-fix x)) ;simplify?
                  (acl2-count x))))
  :hints (("Goal" :use (:instance <-of-acl2-count-of-remove1-equal)
           :in-theory (disable <-of-acl2-count-of-remove1-equal))))

(defthm <=-of-acl2-count-of-nth
  (<= (acl2-count (nth n lst))
      (acl2-count lst))
  :rule-classes (:rewrite (:linear :trigger-terms ((acl2-count (nth n lst)))))
  :hints (("Goal" :induct (NTH N LST)
           :in-theory (enable nth))))
