; Correctness of the ACL2 system function all-picks
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; ALL-PICKS (in induct.lisp) returns all the ways to pick one object from
;; each of a list of "pockets".  The induction formula is built with it.  Its
;; comments end: "It would be reassuring to see a mechanically checked proof
;; that this definition of all-picks is equivalent to Nqthm's."  This book
;; proves that: with RFLG = NIL, ALL-PICKS returns exactly what Nqthm's
;; ALL-PICKS returned, in the same order (and with RFLG = T, its reverse).

(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
;; Since they test for the end of a list with NULL, they can recur once on a
;; non-NIL atom, so we use measures that make NIL smaller than any other atom.
(verify-termination
  (all-picks2 (declare (xargs :measure (if (null pocket) 0 (+ 1 (acl2-count pocket)))))))
(verify-termination
  (all-picks2r (declare (xargs :measure (if (null pocket) 0 (+ 1 (acl2-count pocket)))))))
(verify-termination
  (all-picks1 (declare (xargs :measure (if (null picks) 0 (+ 1 (acl2-count picks)))))))
(verify-termination
  (all-picks (declare (xargs :measure (if (null pockets) 0 (+ 1 (acl2-count pockets)))))))

;; Nqthm's definition, from the "Historical Plaque" in the comments of
;; all-picks:
;;
;;   (DEFUN ALL-PICKS (POCKET-LIST)
;;    (COND ((NULL POCKET-LIST) (LIST NIL))
;;          (T (ITERATE FOR PICK IN (ALL-PICKS (CDR POCKET-LIST))
;;                      NCONC (ITERATE FOR CHOICE IN (CAR POCKET-LIST)
;;                                     COLLECT (CONS CHOICE PICK))))))

;; (ITERATE FOR CHOICE IN POCKET COLLECT (CONS CHOICE PICK))
(defun cons-each-onto (pocket pick)
  (if (endp pocket)
      nil
    (cons (cons (car pocket) pick)
          (cons-each-onto (cdr pocket) pick))))

;; (ITERATE FOR PICK IN PICKS NCONC (ITERATE FOR CHOICE IN POCKET ...))
(defun cons-each-onto-each (pocket picks)
  (if (endp picks)
      nil
    (append (cons-each-onto pocket (car picks))
            (cons-each-onto-each pocket (cdr picks)))))

(defun nqthm-all-picks (pockets)
  (if (endp pockets)
      (list nil)
    (cons-each-onto-each (car pockets) (nqthm-all-picks (cdr pockets)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm all-picks2-becomes-append
   (implies (true-listp pocket)
            (equal (all-picks2 pocket pick ans)
                   (append (cons-each-onto pocket pick) ans)))))

(local
 (defthm all-picks2r-becomes-revappend
   (implies (true-listp pocket)
            (equal (all-picks2r pocket pick ans)
                   (revappend (cons-each-onto pocket pick) ans)))))

(local
 (defthm true-listp-of-cons-each-onto-each
   (true-listp (cons-each-onto-each pocket picks))))

(local
 (defthm true-listp-of-nqthm-all-picks
   (true-listp (nqthm-all-picks pockets))))

;; Without RFLG, the segments for the PICKS end up in reverse order.
(local
 (defthm all-picks1-when-not-rflg
   (implies (and (true-listp pocket)
                 (true-listp picks))
            (equal (all-picks1 pocket picks ans nil)
                   (append (cons-each-onto-each pocket (reverse picks))
                           ans)))
   :hints (("Goal" :induct (all-picks1 pocket picks ans nil)
            :in-theory (enable reverse)))))

(local
 (defthm cons-each-onto-each-of-append
   (equal (cons-each-onto-each pocket (append x y))
          (append (cons-each-onto-each pocket x)
                  (cons-each-onto-each pocket y)))))

;; With RFLG, the whole result is reversed.
(local
 (defthm all-picks1-when-rflg
   (implies (and rflg
                 (true-listp pocket)
                 (true-listp picks))
            (equal (all-picks1 pocket picks ans rflg)
                   (revappend (cons-each-onto-each pocket picks)
                              ans)))
   :hints (("Goal" :induct (all-picks1 pocket picks ans rflg)
            :in-theory (enable revappend-normalize-acc)))))

(local
 (defthm revappend-of-nil-arg2-becomes-reverse
   (implies (true-listp x)
            (equal (revappend x nil)
                   (reverse x)))
   :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm reverse-of-reverse-when-true-listp
   (implies (true-listp x)
            (equal (reverse (reverse x))
                   x))
   :hints (("Goal" :in-theory (e/d (reverse) (revappend-of-nil-arg2-becomes-reverse))))))

(local
 (defthm true-listp-of-all-picks2
   (implies (true-listp ans)
            (true-listp (all-picks2 pocket pick ans)))))

(local
 (defthm true-listp-of-all-picks2r
   (implies (true-listp ans)
            (true-listp (all-picks2r pocket pick ans)))))

(local
 (defthm true-listp-of-all-picks1
   (implies (true-listp ans)
            (true-listp (all-picks1 pocket picks ans rflg)))))

(local
 (defthm true-listp-of-all-picks
   (true-listp (all-picks pockets rflg))))

;; The answer to the question in the comments of all-picks.
(defthm all-picks-correct
  (implies (true-list-listp pockets)
           (equal (all-picks pockets rflg)
                  (if rflg
                      (reverse (nqthm-all-picks pockets))
                    (nqthm-all-picks pockets))))
  :hints (("Goal" :induct (all-picks pockets rflg)
           :in-theory (disable reverse all-picks1))))

;; So with RFLG = NIL, which is how ACL2 calls it, ALL-PICKS is Nqthm's
;; function.
(defthm all-picks-of-nil-is-nqthm-all-picks
  (implies (true-list-listp pockets)
           (equal (all-picks pockets nil)
                  (nqthm-all-picks pockets))))
