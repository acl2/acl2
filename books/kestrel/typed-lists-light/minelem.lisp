; A function to get the minimum of a list of numbers
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(defthm member-equal-when-equal-of-len-and-1-cheap
  (implies (equal (len lst) 1)
           (iff (member-equal x lst)
                (equal x (car lst))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defstub infinity () t)

;; Returns the smallest element of a non-empty list.
(defund minelem (lst)
  (declare (xargs :guard (and (rational-listp lst)
                              (consp lst))))
  (if (endp lst)
      (infinity) ;bozo
    (if (endp (cdr lst))
        (car lst)
      (min (car lst) (minelem (cdr lst))))))

(defthm minelem-when-non-consp
  (implies (not (consp x))
           (equal (minelem x)
                  (infinity)))
  :hints (("Goal" :in-theory (enable minelem))))

(defthm minelem-of-append
  (implies (and (consp x) (consp y)) ;bozo move hyps to conclusion
           (equal (minelem (append x y))
                  (min (minelem x)
                       (minelem y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable minelem append))))

(defthm minelem-singleton
  (equal (minelem (cons a nil))
         a)
  :hints (("Goal" :in-theory (enable minelem))))

(defthm <=-of-minelem-when-member-equal
  (implies (member-equal a x)
           (<= (minelem x) a))
  :hints (("Goal" :in-theory (enable minelem))))

(defthmd minelem-when-subsetp-equal-helper
  (implies (and (subsetp-equal lst1 lst2)
                (consp lst1) ;handle..
                )
           (equal (< (minelem lst1) (minelem lst2))
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable minelem subsetp-equal))))

(defthm minelem-when-subsetp-equal
  (implies (subsetp-equal lst1 lst2)
           (equal (< (minelem lst1) (minelem lst2))
                  (if (consp lst1)
                      nil
                    (< (infinity) (minelem lst2)))))
  :hints (("Goal" :in-theory (enable minelem-when-subsetp-equal-helper))))

(defthm minelem-of-cons
  (equal (minelem (cons a lst))
         (if (endp lst)
             a
           (min a (minelem lst))))
  :hints (("Goal" :in-theory (enable minelem))))

(defthm not-greater-when-<=-of-minelem
  (implies (and (<= k (minelem bag)) ;bag is a free var
                (member-equal elem bag))
           (equal (< elem k)
                  nil))
  :hints (("Goal" :in-theory (enable minelem))))

(defthm minelem-of-nthcdr-peel-off-one
  (implies (and (<= k (nth n lst))
                (true-listp lst) ;bozo
                (< n (len lst))
                (natp n)
                (<= k (minelem (nthcdr (+ 1 n) lst))))
           (<= k (minelem (nthcdr n lst))))
  :hints (("Goal" :in-theory (enable minelem nthcdr))))
