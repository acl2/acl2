; A lightweight book about firstn.
;
; Copyright (C) 2018-2019 Kestrel Institute
; See books/coi/lists/basic.lisp for the copyright on firstn itself.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book provides the FIRSTN function from coi/lists without bringing in
;; anything else from coi/lists.  It also provides some theorems about FIRSTN.

;; Unlike TAKE, FIRSTN may return fewer than the requested number of elements
;; if the list is too short.

(local (include-book "nthcdr"))

;; From coi/lists/basic.lisp:
(defun firstn (n l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp l)
                              (integerp n)
                              (<= 0 n))))
  (cond ((endp l) nil)
        ((zp n) nil)
        (t (cons (car l)
                 (firstn (1- n) (cdr l))))))

(defthm firstn-of-nil
  (equal (firstn n nil)
         nil))

(defthm firstn-when-zp-cheap
  (implies (and (syntaxp (quotep n))
                (zp n))
           (equal (firstn n x)
                  nil))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm len-of-firstn
  (equal (len (firstn n l))
         (min (nfix n) (len l))))

(defthm firstn-of-singleton
  (implies (and (syntaxp (quotep n))
                (posp n))
           (equal (firstn n (cons x nil))
                  (cons x nil))))

;try disabled..
(defthm firstn-of-one-more
  (implies (and (syntaxp (not (quotep n))) ;stupid acl2 unifies n with a constant
                (< n (len lst))      ;bozo drop?
                (integerp n)
                (<= 0 n))
           (equal (firstn (+ 1 n) lst)
                  (append (firstn n lst) (list (nth n lst)))
                  ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (firstn append nth) ()))))

(defthm nth-of-firstn
  (equal (nth n1 (firstn n2 x))
         (if (< (nfix n1) (nfix n2))
             (nth n1 x)
           nil)))

(defthm nthcdr-of-firstn-same
  (equal (nthcdr n (firstn n x))
         nil))

(defthm firstn-of-true-list-fix
  (equal (firstn n (true-list-fix l))
         (firstn n l)))

(defthm firstn-becomes-take
  (implies (and (<= m (len lst))
                (natp m))
           (equal (firstn m lst)
                  (take m lst)))
  :hints (("Goal" :in-theory (enable firstn take))))

(defthm firstn-becomes-take-gen
  (implies (natp n)
           (equal (firstn n lst)
                  (if (<= n (len lst))
                      (take n lst)
                    (take (len lst) lst))))
  :hints (("Goal" :in-theory (enable firstn take))))

(defthm firstn-of-1
  (equal (firstn 1 lst)
         (if (consp lst)
             (list (car lst))
           nil))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm firstn-when-<=-of-len
  (implies (<= (len x) (nfix n))
           (equal (firstn n x)
                  (true-list-fix x)))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm append-of-firstn-and-nthcdr
  (equal (append (firstn n x) (nthcdr n x))
         (if (< (len x) (nfix n))
             (true-list-fix x)
           x))
  :hints (("Goal" :in-theory (e/d (nthcdr firstn append) (firstn-becomes-take-gen)))))
