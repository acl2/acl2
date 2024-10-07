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


(defthm nthcdr-0--thm
  (= (nthcdr 0 lst) lst))

(defthm car-nthcdr--thm
  (= (car (nthcdr n lst)) (nth n lst)))

(defthm consp-nthcdr--thm
  (implies
   (and (>= n 0)
        (< n (len l)))
   (consp (nthcdr n l))))

(defthm len-nthcdr-le-len-lst--thm
  (<= (len (nthcdr x lst)) (len lst)))

;; Accumulated Persistence
(defthmd nthcdr-of-len-lst--thm
  (implies
   (and (true-listp lst)
        (integerp xx)
        (>= xx (len lst)))
   (= (nthcdr xx lst) nil)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm nthcdr-cdr--thm
  (implies
   (and (integerp xx)
        (>= xx 0))
   (= (nthcdr xx (cdr lst)) (nthcdr (1+ xx) lst))))

(defthm cdr-nthcdr--thm
  (implies
   (and (integerp xx)
        (<= 0 xx))
   (= (cdr (nthcdr xx lst)) (nthcdr (1+ xx) lst))))

(defthm cons-nthcdr--thm
  (implies
   (and (integerp i)
        (<= 0 i)
        (< i (len lst)))
   (= (cons (nth i lst) (nthcdr (1+ i) lst)) (nthcdr i lst))))

(defthm nthcdr-of-cons--thm
  (implies (not (zp j))
           (= (nthcdr j (cons x lst)) (nthcdr (1- j) lst))))

(defthm append-nthcdr--thm
  (implies
   (and (not (zp i))
        (< i (len lst)))
   (= (append (list (nth i lst)) (nthcdr (1+ i) lst)) (nthcdr i lst))))

(defthmd cdr-nthcdr-minus-1--thm
  (implies
   (and (not (zp xx)))
   (= (nthcdr xx lst) (cdr (nthcdr (1- xx) lst)))))

(defthm nthcdr-len-minus-2--thm
  (implies
   (and (true-listp lst)
        (> (len lst) 1))
   (= (nthcdr (- (len lst) 2) lst)
      (list (nth (- (len lst) 2) lst)
            (nth (- (len lst) 1) lst)))))

(defthm nthcdr-member-nth--thm
  (implies
    (and (<= 0 xx)
         (< xx (len lst)))
    (member-equal (nth xx lst) (nthcdr xx lst))))

(defthm nthcdr-member-nth-1--thm
  (implies
   (and (<= 0 xx)
        (< (1+ xx) (len lst)))
   (member-equal (nth (1+ xx) lst) (nthcdr xx lst))))

(defthm nthcdr-len-minus-1--thm
  (implies
   (and (not (null x))
        (true-listp x))
   (= (nthcdr (1- (len x)) x)
      (list (nth (1- (len x)) x)))))

(defthm nthcdr-preserves-true-listp--thm
  (implies (true-listp lst)
           (true-listp (nthcdr x lst))))

(defthm nthcdr-ge-len-nil--thm
  (implies
   (and (true-listp x)
        (integerp q)
        (>= q (len x)))
   (= (nthcdr q x) nil)))

(defthm nthcdr-lt-len-not-nil--thm
  (implies
   (and (<= 0 q)
        (< q (len x)))
   (not (= (nthcdr q x) nil))))

(defthm len-nthcdr-minus-1-gt-len-nthcdr--thm
  (implies
   (and (not (zp q))
        (< q (len x)))
   (> (len (nthcdr (1- q) x)) (len (nthcdr q x)))))

(defthm nthcdr-update-nth--thm
  (implies
   (and (integerp ix)
        (<= 0 ix)
        (integerp iy)
        (< ix iy))
   (= (nthcdr iy (update-nth ix z lst))
      (nthcdr iy lst))))
