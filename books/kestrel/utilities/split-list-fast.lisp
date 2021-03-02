; A very fast function to split a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This book introduces the function split-list-fast, which splits a list into
;; two pieces of roughly the same size, where the order doesn't really matter
;; (e.g., for mergesort).

;; Note: "split-list" (without the "-fast") is already the name of a function
;; in the rtl library.

(in-theory (disable mv-nth)) ;; We always keep mv-nth disabled.  (we could go to nth, but then do we go to car if n=0?)

;;;
;;; split-list-fast-aux
;;;

;acc contains the elems that the slow-moving guy has passed
;; Returns (mv first-half second-half).
;This walks down TAIL twice as fast as it walks down LST
(defun split-list-fast-aux (lst tail acc)
  (declare (xargs :guard (and (true-listp tail)
                              (true-listp lst))))
  (if (or (endp tail)
          (endp (cdr tail)))
      (mv acc lst)
    (split-list-fast-aux (cdr lst) (cddr tail) (cons (car lst) acc))))

(defthm true-listp-of-mv-nth-0-of-split-list-fast-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 0 (split-list-fast-aux lst tail acc)))))

(defthm true-listp-of-mv-nth-1-of-split-list-fast-aux
  (implies (true-listp lst)
           (true-listp (mv-nth 1 (split-list-fast-aux lst tail acc)))))

(defthm len-of-split-list-fast-aux-bound
  (<= (len (mv-nth 1 (split-list-fast-aux lst tail acc)))
      (len lst)))

(defthm len-of-split-list-fast-aux-bound2
  (implies (and ;(consp tail)
                (consp (cdr tail))
                (<= (len tail) (len lst)))
           (< (len (mv-nth 1 (split-list-fast-aux lst tail acc)))
              (len lst)))
  :hints (("Goal" :in-theory (e/d (len) ()))))

(defthm len-of-split-list-fast-aux-bound3
  (implies (and ;(consp tail)
                (consp (cdr tail))
                (<= (len tail) (len lst)))
           (< (len (mv-nth 0 (split-list-fast-aux lst tail acc)))
              (+ (len lst) (len acc))))
  :hints (("Goal" :in-theory (e/d (len) ()))))

(defthm split-list-fast-aux-len-theorem
  (implies (<= (len tail) (len lst))
           (equal (+ (len (mv-nth 0 (split-list-fast-aux lst tail acc)))
                     (len (mv-nth 1 (split-list-fast-aux lst tail acc))))
                  (+ (len lst)
                     (len acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm consp-of-mv-nth-0-of-split-list-fast-aux
  (equal (consp (mv-nth 0 (split-list-fast-aux lst tail acc)))
         (or (consp acc)
             (consp (CDR TAIL))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm consp-of-mv-nth-1-of-split-list-fast-aux
  (equal (consp (mv-nth 1 (split-list-fast-aux lst tail acc)))
         (< (len tail) (* 2 (len lst))))
  :hints (("Goal" :induct (split-list-fast-aux lst tail acc)
           :in-theory (enable split-list-fast-aux))
          ("subgoal *1/2" :cases ((< (LEN (CDDR TAIL))
                                     (* 2 (LEN (CDR LST))))))))

;;;
;;; split-list-fast
;;;

;reuses the tail of the list
;; This is helpful when all we care about is splitting the list into two pieces of roughly the same size, not the order and not which elements go in which half), e.g., for mergesort.
;; Returns (mv first-half-rev second-half) where FIRST-HALF-REV is the first half of the elements in reverse.
;fixme would it be faster to compute the length of the list first and then walk down that many elements (would require arithmetic)?
(defund split-list-fast (lst)
  (declare (xargs :guard (true-listp lst)))
  (split-list-fast-aux lst lst nil))

(defthm true-listp-of-mv-nth-0-of-split-list-fast
  (true-listp (mv-nth 0 (split-list-fast lst)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm true-listp-of-mv-nth-1-of-split-list-fast
  (implies (true-listp lst)
           (true-listp (mv-nth 1 (split-list-fast lst))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm len-of-split-list-fast-bound
  (implies (and ;(consp lst)
                (consp (cdr lst)))
           (< (len (mv-nth 1 (split-list-fast lst)))
              (len lst)))
  :hints (("Goal" :use (:instance len-of-split-list-fast-aux-bound2 (tail lst) (acc nil))
           :in-theory (e/d (split-list-fast) (len-of-split-list-fast-aux-bound2)))))

(defthm len-of-split-list-fast-bound2
  (implies (and ;(consp lst)
                (consp (cdr lst)))
           (< (len (mv-nth 0 (split-list-fast lst)))
              (len lst)))
  :hints (("Goal" :use (:instance len-of-split-list-fast-aux-bound3 (tail lst) (acc nil))
           :in-theory (e/d (split-list-fast) (len-of-split-list-fast-aux-bound3)))))

(defthm split-list-fast-len-theorem
  (equal (+ (len (mv-nth 0 (split-list-fast lst)))
            (len (mv-nth 1 (split-list-fast lst))))
         (len lst))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm consp-of-mv-nth-0-of-split-list-fast
  (equal (consp (mv-nth 0 (split-list-fast lst)))
         (< 1 (len lst)))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm consp-of-mv-nth-1-of-split-list-fast
  (equal (consp (mv-nth 1 (split-list-fast lst)))
         (consp lst))
  :hints (("Goal" :in-theory (enable split-list-fast))))
