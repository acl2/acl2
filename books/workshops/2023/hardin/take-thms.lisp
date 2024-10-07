;; Copyright (C) 2023-2024 David S. Hardin
;;
;; License: (An MIT/X11-style license)
;;
;;   Permission is hereby granted, free of charge, to any person obtaining a
;;   copy of this software and associated documentation files (the "Software"),
;;   to deal in the Software without restriction, including without limitation
;;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;   and/or sell copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following conditions:
;;
;;   The above copyright notice and this permission notice shall be included in
;;   all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

;;(include-book "data-structures/list-defthms" :dir :system)

(defthmd true-listp-eq-nth-eq--thm
  (implies (= x y)
           (= (nth j x) (nth j y))))

(defthm take-0--thm
  (= (take 0 lst) nil))

(defthm take-car--thm
  (implies (not (zp x))
           (= (car (take x lst)) (car lst))))

(defthm take-consp--thm
  (implies (not (zp i))
           (consp (take i lst))))

(defthm take-len--thm
  (implies (true-listp lst)
           (= (take (len lst) lst) lst)))

(defthm take-pos-x-of-non-empty-list-not-endp--thm
  (implies (not (zp x))
           (not (endp (take x lst)))))

(defthm take-cons-car-cdr--thm
  (implies (not (zp e))
           (= (cons (car x) (cdr (take e x))) (take e x))))

(defthmd take-cons-swap--thm
  (implies (not (zp j))
           (= (take j (cons a lst)) (cons a (take (1- j) lst)))))

(defthmd take-cdr-swap--thm
  (implies (not (zp n))
           (= (take n (cdr lst)) (cdr (take (1+ n) lst)))))


(defthm len-of-take
  (equal (len (take n x))
         (nfix n)))

(defthm take-nth--thm
  (implies
   (and (integerp j)
        (<= 0 j)
        (integerp n)
        (< j n))
    (= (nth j (take n x)) (nth j x))))

(DEFTHMD TAKE-EQ-NTH-EQ--THM
  (IMPLIES
   (AND (INTEGERP J)
        (INTEGERP N)
        (<= 0 J)
        (< J N)
        (= (TAKE N X) (TAKE N Y)))
   (= (NTH J X) (NTH J Y)))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM (TRUE-LISTP (TAKE N X)))
  (:CLAIM (= (LEN (TAKE N X)) N))
     (:CLAIM (= (NTH J (TAKE N X))
                (NTH J (TAKE N Y)))
             :HINTS (("Goal" :USE (:INSTANCE TRUE-LISTP-EQ-NTH-EQ--THM
                                             (X (TAKE N X))
                                             (Y (TAKE N X))))))
     (:CLAIM (= (NTH J (TAKE N X))
                (NTH J X))
             :HINTS (("Goal" :USE (:INSTANCE TAKE-NTH--THM))))
     (:CLAIM (= (NTH J (TAKE N Y))
                (NTH J Y))
             :HINTS (("Goal" :USE (:INSTANCE TAKE-NTH--THM (X Y)))))
     :BASH))

  
(defthmd take-xx-minus-1-nth-xx-minus-1--thm
  (implies
   (and (integerp xx)
        (> xx 0)
        (<= xx (len lst)))
   (= (take xx lst) (append (take (1- xx) lst) (list (nth (1- xx) lst))))))

(defthm take-j-of-take-i-where-j-le-i--thm
  (implies
   (and (true-listp lst)
        (integerp i)
        (<= j i))
   (= (take j (take i lst))
      (take j lst))))

(defthm take-append-le--thm
  (implies
   (and (true-listp lst1)
        (true-listp lst2)
        (integerp j) (<= 0 j) (<= j (len lst1)))
   (= (take j (append lst1 lst2))
      (take j lst1))))

(defthm take-update-i-nth-j-ge-i--thm
  (implies
   (and (true-listp lst)
        (integerp i) (<= 0 i) ;; (< i (len lst))
        (integerp j)
        (<= i j))
   (= (take i (update-nth j y lst))
      (take i lst))))

(defthm take-update-nth--thm
  (implies
   (and (true-listp lst)
        (<= 0 i))
   (= (take i (update-nth i y lst))
      (take i lst))))

(defthmd take-update-nth-swap--thm
  (implies
   (and  (true-listp lst)
         (integerp i)
         (integerp x)
         (<= 0 x)
         (< x i))
   (= (take i (update-nth x y lst))
      (update-nth x y (take i lst)))))

(defthm update-nth-append-take--thm
  (implies
   (and ;; (true-listp lst)
        (integerp i)
        (<= 0 i))
   (= (take (1+ i) (update-nth i y lst))
      (append (take i lst) (list y)))))

(defthm append-take-nthcdr--thm
  (implies
   (and ;; (true-listp lst)
        (<= 0 i)
        (<= i (len lst)))
   (= (append (take i lst) (nthcdr i lst)) lst)))

(defthm append-3-take-list-nth-nthcdr--thm
  (implies
   (and (true-listp lst)
        (integerp i)
        (<= 0 i)
        (< i (len lst)))
   (= (append (take i lst) (list (nth i lst)) (nthcdr (1+ i) lst)) lst)))


(defthm update-nth-append-take-nthcdr--thm
  (implies
   (and (true-listp lst)
        (integerp i)
        (<= 0 i))
   (= (append (take i lst) (list y) (nthcdr (1+ i) lst))
      (update-nth i y lst))))


(defthmd append-take-xx-minus-1-nth-xx-minus-1--thm
  (implies
   (and (integerp xx)
        (> xx 0)) ;; (<= xx (len lst)))
   (= (append (take (1- xx) lst) (list (nth (1- xx) lst))) (take xx lst))))


(defthm not-member-equal-take--thm
  (implies
   (and (not (null x))
        (not (member-equal x lst)))
   (not (member-equal x (take n lst)))))

(defthm take-x-of-integer-listp-x-le-len-preserves-integer-listp--thm
  (implies
   (and (integer-listp lst)
        ;; (<= 0 x)
        (<= x (len lst)))
   (integer-listp (take x lst))))


(defthmd take-j-plus-1-eq--thm
  (implies (= (take (1+ j) lst1) (take (1+ j) lst2))
           (= (take j lst1) (take j lst2))))
