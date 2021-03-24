; A function to get the maximum of a list of numbers
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

(local (include-book "rational-listp"))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;todo: move
(defthmd update-nth-rw
  (implies (and (natp n)
                (< n (len lst)))
           (equal (update-nth n val lst)
                  (append (take n lst)
                          (list val)
                          (nthcdr (+ 1 n) lst)))))

(defstub negative-infinity () t)

;; Returns the largest element of a non-empty list.
(defund maxelem (lst)
  (declare (xargs :guard (rational-listp lst)))
  (if (endp lst)
      ;; It's not clear what the maximum element of an empty list should be, so
      ;; we return a special value:
      (negative-infinity) ;should not happen
    (if (endp (cdr lst))
        (car lst)
      (max (car lst) (maxelem (cdr lst))))))

(defthmd maxelem-of-append-helper
  (implies (and (consp x)
                (consp y))
           (equal (maxelem (append x y))
                  (max (maxelem x)
                       (maxelem y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable maxelem append))))

(defthm maxelem-of-true-list-fix
  (equal (maxelem (true-list-fix x))
         (maxelem x))
  :hints (("Goal" :in-theory (enable maxelem))))

;bozo adapt all maxelem thms to minelem
(defthm maxelem-when-non-consp
  (implies (not (consp x))
           (equal (maxelem x)
                  (negative-infinity)))
  :hints (("Goal" :in-theory (enable maxelem))))

;; (defthm maxelem-when-non-consp-hidden
;;   (implies (not (consp x))
;;            (equal (hide (maxelem x))
;;                   (negative-infinity)))
;;   :hints (("Goal" :expand (hide (maxelem x))
;;            :in-theory (enable maxelem (hide)))))

(defthm maxelem-of-append
  (implies (true-listp y) ;drop?
           (equal (maxelem (append x y))
                  (if (not (consp x))
                      (maxelem y)
                    (if (not (consp y))
                        (maxelem x)
                      (max (maxelem x)
                           (maxelem y))))))
  :hints (("Goal" :in-theory (disable (:e maxelem))
           :use (:instance maxelem-of-append-helper))))

(defthm maxelem-singleton
  (equal (maxelem (cons a nil))
         a)
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm maxelem-singleton-alt
  (implies (and (consp lst)
                (not (consp (cdr lst))))
           (equal (maxelem lst)
                  (car lst)))
  :hints (("Goal" :in-theory (enable maxelem))))

;; (thm
;;  (implies (and (integerp n)
;;                (<= 0 n)
;;                (< n (len lst)))
;;           (equal (MAXELEM (TAKE (+ 1 n) lst))
;;                  (max (nth (+ 1 n) lst)
;;                       (MAXELEM (TAKE n lst))))))

(defthm maxelem-of-cons
  (equal (maxelem (cons a lst))
         (if (endp lst)
             a
           (max a (maxelem lst))))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm integerp-of-maxelem
  (implies (and (integer-listp lst)
                (consp lst))
           (integerp (maxelem lst))))

;bozo make a theory of this for a generic (numeric?) type?
(defthm acl2-numberp-of-maxelem
  (implies (and (integer-listp lst) ;weaken?
                (consp lst))
           (acl2-numberp (maxelem lst))))

;slow?
(defthm maxelem-of-update-nth
  (implies (and (< n (len lst))
                (true-listp lst) ;bozo
;                (integerp val)
                (<= 0 n)
                (integerp n)
                )
           (equal (maxelem (update-nth n val lst))
                  (if (equal n (+ -1 (len lst)))
                      (if (zp n)
                          val
                        ;bozo phrase this using max?
                        (if (< val (maxelem (take (nfix n) lst)))
                            (maxelem (take (nfix n) lst))
                          val))
                    (if (zp n)
                        (if (<= val (maxelem (nthcdr (+ 1 (nfix n)) lst)))
                            (maxelem (nthcdr (+ 1 (nfix n)) lst))
                          val)
                      (if (and (<= val (maxelem (nthcdr (+ 1 (nfix n)) lst)))
                               (<= (maxelem (take (nfix n) lst)) (maxelem (nthcdr (+ 1 (nfix n)) lst))))
                          (maxelem (nthcdr (+ 1 (nfix n)) lst))
                        (if (< val (maxelem (take (nfix n) lst)))
                            (maxelem (take (nfix n) lst))
                          val))))))
  :hints (("Goal" :do-not-induct t
           :expand (MAXELEM (CDR LST))
           :in-theory (e/d (update-nth-rw;update-nth-rewrite nth-when-n-is-zp
                            update-nth
                            )
                           ((force))))))

;expensive?
;newly disabled
(defthmd not-<-car-when->=maxelem
  (implies (and (<= (maxelem lst) x)
                (consp lst))
           (not (< x (car lst)))))

(defthm <=-of-maxelem-when-member-equal
  (implies (member-equal a x)
           (<= a (maxelem x)))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm less-than-maxelem-when-less-than-some-elem
  (implies (and (< k elem) ;elem is a free variable
                (member-equal elem lst))
           (< k (maxelem lst)))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm maxelem-car-linear
  (implies (consp x)
           (<= (car x) (maxelem x)))
  :rule-classes ((:rewrite)
                 (:linear :trigger-terms ((maxelem lst)))))

;BOZO seems gross
(defthm nth-0-<-maxelem
  (implies (consp x)
           (<= (nth 0 x) (maxelem x)))
  :rule-classes ((:linear :trigger-terms ((maxelem x)))
                 :rewrite))

(defthm rationalp-of-maxelem
  (implies (and (consp items)
                (rational-listp items))
           (rationalp (maxelem items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm maxelem-of-strip-cars-linear
  (implies (consp dag)
           (<= (car (car dag)) (maxelem (strip-cars dag))))
  :rule-classes ((:linear :trigger-terms ((maxelem (strip-cars dag))))))

(defthm maxelem-of-cdr-linear
  (implies (< 1 (len lst))
           (<= (maxelem (cdr lst)) (maxelem lst)))
  :rule-classes ((:linear :trigger-terms ((maxelem (cdr lst)))))
  :hints (("Goal" :in-theory (enable maxelem))))
