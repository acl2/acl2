; Copyright (C) 2020, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Lemmas Supporting the Examples of Rewrite-Quoted-Constant Rules in Use
; J Strother Moore
; August, 2020

; This book supports rewrite-quoted-constant-examples.lisp.  In this book we
; establish that set-equalp is an equivalence relation, we define cardinality,
; and we prove that set-equalp is a congruence for the argument of cardinality,
; i.e., that set-equalp lists have the same (equal) cardinalities.

; Sketch: How do you prove that set-equalp lists have equal cardinalities?  The
; proof I use is based on the idea that if a is a subset of b, then the
; cardinality of a is less than or equal than that of b, and vice versa.  Since
; set-equalp is defined as conjoined subsets, we're done.  So how do you prove
; the key lemma?

; (defthm subsetp-equal-len
;   (implies (and (subsetp-equal a b)
;                 (no-duplicatesp a)
;                (no-duplicatesp b))
;            (<= (len a) (len b)))
;   :hints (("Goal" :induct (my-subsetp-equal a b))))

; Proving subsetp-equal-len involves inducting on a and b at the same time.  I
; defined what amounts to an alternative version of subsetp-equal, called
; my-subsetp-equal, which in turn is defined in terms of my-remove1 so that
; each time (my-subsetp-equal a b) finds (car a) is in b it cdrs a and removes
; (car a) from b.  If you do the induction hinted above, you just need a few
; lemmas relating my-remove1 to the concepts in the theorem to finish the
; proof.  But the whole journey is longer than I ever anticipated and if
; someone finds a shorter proof (for my definition of set-equalp and my
; definition of cardinality) I'd love to see it!

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)
(include-book "sorting/isort" :dir :system)

; The following events define drop-dups-and-sort and prove that it maintains
; set-equalp.  We do not yet create any :rewrite-quoted-constant rules!
; We're just setting the stage.

(defun fix-list (lst)
  (cond ((atom lst) nil)
        (t (cons (car lst) (fix-list (cdr lst))))))

(defun drop-dups-and-sort (lst)
  (isort (remove-duplicates-equal (fix-list lst))))

(local
 (encapsulate
   nil
   (defthm set-equalp-fix-list
     (set-equalp (fix-list lst) lst))

   (defthm set-equalp-remove-duplicates-equal
     (set-equalp (remove-duplicates-equal lst) lst))

   (defthm set-equalp-insert
     (set-equalp (insert e lst) (cons e lst)))

   (defthm set-equalp-isort
     (set-equalp (isort lst) lst))))

; Note:  This could be a Form [2] :rewrite-quoted-constant rule, but we
; don't want it stored that way yet.

(defthm set-equalp-drop-dups-and-sort
  (set-equalp (drop-dups-and-sort lst) lst)
  :rule-classes :rewrite)

(defun cardinality (lst)
  (len (drop-dups-and-sort lst)))

(local
 (encapsulate
   nil
   (defthm len-isort
     (equal (len (isort x)) (len x)))

   (defun my-remove1 (e lst)
     (cond ((endp lst) lst)
           ((equal e (car lst)) (cdr lst))
           (t (cons (car lst) (my-remove1 e (cdr lst))))))

   (defun my-subsetp-equal (a b)
     (cond ((endp a) t)
           ((member-equal (car a) b)
            (my-subsetp-equal (cdr a) (my-remove1 (car a) b)))
           (t nil)))

   (defthm lemma0
     (implies (not (member e b))
              (not (member e (my-remove1 d b)))))

   (defthm lemma1
     (IMPLIES (SUBSETP-EQUAL A (MY-REMOVE1 E B))
              (SUBSETP-EQUAL A B)))

   (defthm lemma2
     (implies (and (MEMBER-EQUAL A1 B)
                   (not (equal a1 e)))
              (member-equal a1 (my-remove1 e b))))

   (defthm lemma3
     (IMPLIES (not (member-equal e a))
              (equal (subsetp-equal a (my-remove1 e b))
                     (subsetp-equal a b))))

   (defthm lemma4
     (implies (no-duplicatesp-equal b)
              (no-duplicatesp-equal (my-remove1 e b))))

   (defthm lemma5
     (implies (member-equal e b)
              (equal (len (my-remove1 e b))
                     (- (len b) 1))))))

(defthm subsetp-equal-len
  (implies (and (subsetp-equal a b)
                (no-duplicatesp a)
                (no-duplicatesp b))
           (<= (len a) (len b)))
  :hints (("Goal" :induct (my-subsetp-equal a b))))

(local
 (defthm no-duplicatesp-equal-remove-duplicates-equal
   (no-duplicatesp (remove-duplicates-equal x))))

(defcong set-equalp equal (cardinality lst) 1
  :hints (("Goal"
           :use
           ((:instance subsetp-equal-len
                       (a (REMOVE-DUPLICATES-EQUAL (FIX-LIST LST)))
                       (b (REMOVE-DUPLICATES-EQUAL (FIX-LIST LST-EQUIV))))
            (:instance subsetp-equal-len
                       (b (REMOVE-DUPLICATES-EQUAL (FIX-LIST LST)))
                       (a (REMOVE-DUPLICATES-EQUAL (FIX-LIST LST-EQUIV))))))))

