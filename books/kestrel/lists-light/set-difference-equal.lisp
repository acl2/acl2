; A lightweight book about the built-in function set-difference-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "member-equal"))
(local (include-book "remove1-equal"))

(in-theory (disable set-difference-equal))

;; Also in member-equal.lisp
(defthm member-equal-of-set-difference-equal
  (iff (member-equal a (set-difference-equal x y))
       (and (member-equal a x)
            (not (member-equal a y)))))

(defthm set-difference-equal-of-nil-arg1
  (equal (set-difference-equal nil y)
         nil)
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-of-nil-arg2
  (equal (set-difference-equal x nil)
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm consp-of-set-difference-equal
  (equal (consp (set-difference-equal x y))
         (not (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-iff
  (iff (set-difference-equal x y)
       (not (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm car-of-set-difference-equal-when-not-member-equal-of-car
  (implies (not (member-equal (car x) y))
           (equal (car (set-difference-equal x y))
                  (car x)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-of-set-difference-equal-arg1-same
  (equal (set-difference-equal (set-difference-equal x y) y)
         (set-difference-equal x y))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-of-cons-arg2
  (equal (set-difference-equal x (cons a y))
         (remove-equal a (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-of-add-to-set-equal-arg2
  (equal (set-difference-equal x (add-to-set-equal a y))
	 (remove-equal a (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-of-append
  (equal (set-difference-equal x (append y z))
         (set-difference-equal (set-difference-equal x y) z))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

;; ACL2 puts in a loop-stopper
(defthm set-difference-equal-of-set-difference-equal-arg1
  (equal (set-difference-equal (set-difference-equal x y) z)
         (set-difference-equal (set-difference-equal x z) y))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthmd set-difference-equal-of-remove1-equal-arg1-irrel
  (implies (not (member-equal a y))
           (equal (set-difference-equal (remove1-equal a x) y)
                  (remove1-equal a (set-difference-equal x y))))
  :hints (("Goal" :in-theory (enable set-difference-equal
                                     (:d remove1-equal)
                                     ))))

(defthmd set-difference-equal-of-remove1-equal-arg2-irrel
  (implies (not (member-equal a x))
           (equal (set-difference-equal x (remove1-equal a y))
                  (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal
                                     remove1-equal))))

(defthmd set-difference-equal-of-cdr-when-not-member-equal-of-car
  (implies (not (member-equal (car y) x))
           (equal (set-difference-equal x (cdr y))
                  (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthmd set-difference-equal-redef
  (implies (and (consp y)
                (no-duplicatesp-equal x) ;gen?
                ;;(no-duplicatesp-equal y)
                )
           (equal (set-difference-equal x y)
                  (remove1-equal (car y) (set-difference-equal x (cdr y)))))
  :hints (("Goal" :in-theory (enable set-difference-equal
                                     set-difference-equal-of-cdr-when-not-member-equal-of-car))))
