; Some rules about split-list-fast.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; See also split-list-fast-rules.lisp.

(include-book "split-list-fast-defs")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(in-theory (disable mv-nth)) ;; We always keep mv-nth disabled.  (we could go to nth, but then do we go to car if n=0?)

;;;
;;; Rules about split-list-fast-aux
;;;

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
  :hints (("Goal" :in-theory (enable len))))

(defthm len-of-split-list-fast-aux-bound3
  (implies (and ;(consp tail)
                (consp (cdr tail))
                (<= (len tail) (len lst)))
           (< (len (mv-nth 0 (split-list-fast-aux lst tail acc)))
              (+ (len lst) (len acc))))
  :hints (("Goal" :in-theory (enable len))))

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
;;; Rules about split-list-fast
;;;

;reuses the tail of the list
;; This is helpful when all we care about is splitting the list into two pieces of roughly the same size, not the order and not which elements go in which half), e.g., for mergesort.
;; Returns (mv first-half-rev second-half) where FIRST-HALF-REV is the first half of the elements in reverse.
;fixme would it be faster to compute the length of the list first and then walk down that many elements (would require arithmetic)?
;dup
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

(defthm len-of-split-list-fast-bound-linear
  (implies (and ;(consp lst)
                (consp (cdr lst)))
           (< (len (mv-nth 1 (split-list-fast lst)))
              (len lst)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance len-of-split-list-fast-aux-bound2 (tail lst) (acc nil))
           :in-theory (e/d (split-list-fast) (len-of-split-list-fast-aux-bound2)))))

(defthm len-of-split-list-fast-bound2
  (implies (and ;(consp lst)
                (consp (cdr lst)))
           (< (len (mv-nth 0 (split-list-fast lst)))
              (len lst)))
  :hints (("Goal" :use (:instance len-of-split-list-fast-aux-bound3 (tail lst) (acc nil))
           :in-theory (e/d (split-list-fast) (len-of-split-list-fast-aux-bound3)))))

(defthm len-of-split-list-fast-bound2-linear
  (implies (and ;(consp lst)
                (consp (cdr lst)))
           (< (len (mv-nth 0 (split-list-fast lst)))
              (len lst)))
  :rule-classes :linear
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

(local (in-theory (disable floor)))

;; We can probably use these to improve some proofs about split-list-fast:

(defthmd mv-nth-0-of-split-list-fast-aux
  (equal (mv-nth 0 (split-list-fast-aux lst tail acc))
         (append (reverse (take (floor (len tail) 2) lst))
                 acc)))

(defthmd mv-nth-1-of-split-list-fast-aux
 (equal (mv-nth 1 (split-list-fast-aux lst tail acc))
        (nthcdr (floor (len tail) 2)
                lst)))

(defthmd mv-nth-0-of-split-list-fast
  (equal (mv-nth 0 (split-list-fast lst))
         (reverse (take (floor (len lst) 2) lst)))
  :hints (("Goal" :in-theory (enable split-list-fast
                                     mv-nth-0-of-split-list-fast-aux))))

(defthmd mv-nth-1-of-split-list-fast
  (equal (mv-nth 1 (split-list-fast lst))
         (nthcdr (floor (len lst) 2) lst))
  :hints (("Goal" :in-theory (enable split-list-fast
                                     mv-nth-1-of-split-list-fast-aux))))

(local
 (defthm len-of-split-list-fast-aux
   (equal (len (split-list-fast-aux lst tail acc))
          2)
   :hints (("Goal" :in-theory (enable split-list-fast)))))

(local
 (defthm len-of-split-list-fast
   (equal (len (split-list-fast lst))
          2)
   :hints (("Goal" :in-theory (enable split-list-fast)))))

(defthmd split-list-fast-redef
  (equal (split-list-fast lst)
         (mv (reverse (take (floor (len lst) 2) lst))
             (nthcdr (floor (len lst) 2) lst)))
  :hints (("Goal" :use (mv-nth-0-of-split-list-fast
                        mv-nth-1-of-split-list-fast
                        len-of-split-list-fast)
           :expand (mv-nth 1 (split-list-fast lst))
           :in-theory (e/d (mv-nth) (len-of-split-list-fast)))))
