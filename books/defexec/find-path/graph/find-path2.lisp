; An Exercise in Graph Theory
; J Strother Moore

; This file is an ACL2 book.  To certify it, execute:
;
; (certify-book "find-path2")

; This file is a cleaned up version of the file find-path1.lisp, which
; you should read first.

; To produce this file I removed from find-path1.lisp all the list
; processing lemmas and put them in the new book helpers.lisp.  Then I
; added the second include-book below to bring them all into the data
; base.  This book is just the graph theory part of the exercise.

; The indentation was left unchanged.  But you should understand that
; this book was not created by using The Method, despite what might be
; suggested by the indentation!  The main reason I created this book
; was to make two nice exercises for you.

; 1. You could do just the first of the two include-books below
;    and then try to process each event in this file.  You will have
;    to discover the list processing lemmas for yourself, using The
;    Method.

; 2. More ambitiously, you could do the two include-books below and then
;    try to do the graph theory problem by proving each of the four
;    Observations.  In this exercise you will have all the ``necessary''
;    list processing lemmas but will have to discover the graph theory
;    lemmas.  This is a little harder since the graph theory lemmas are
;    about concepts that are less familiar to you than append and member.
;    I say ``necessary'' because you may well need other list processing
;    lemmas, depending on which graph theory lemmas you invent.  But at
;    least it is a start.

; ---------------------------------------------------------------------------
; Getting Started

(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(include-book "helpers")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

; ---------------------------------------------------------------------------
; The Primitives of Directed Graphs

(defun all-nodes (g)
  (cond ((endp g) nil)
        (t (cons (car (car g))
                 (all-nodes (cdr g))))))

(defun graph1p (g nodes)
  (cond ((endp g) t)
        (t (and (consp (car g))
                (true-listp (cdr (car g)))
                (subsetp (cdr (car g)) nodes)
                (no-duplicatesp (cdr (car g)))
                (graph1p (cdr g) nodes)))))

(defun graphp (g)
  (and (alistp g)
       (no-duplicatesp (all-nodes g))
       (graph1p g (all-nodes g))))

(defun nodep (x g)
  (member x (all-nodes g)))

(defun neighbors (node g)
  (cond ((endp g) nil)
        ((equal node (car (car g))) (cdr (car g)))
        (t (neighbors node (cdr g)))))

(defun pathp (p g)
  (cond ((endp p) nil)
        ((endp (cdr p))
         (equal (cdr p) nil))
        (t (and (member (car (cdr p))
                        (neighbors (car p) g))
                (pathp (cdr p) g)))))

(defun path-from-to (p a b g)
  (and (pathp p g)
       (equal (car p) a)
       (equal (car (last p)) b)))

(defthm Example1
  (let ((g '((A B)
             (B B C)
             (C A C D)
             (D A B C))))

    (and (graphp g)
         (not (graphp (cdr g)))
         (nodep 'A g)
         (not (nodep 'E g))
         (pathp '(A B C D C A B B) g)
         (path-from-to '(A B B C) 'A 'C g)
         (not (pathp '(A B D) g))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; The Specification of Find-Path

; (no events)

; ---------------------------------------------------------------------------
; The Definitions of Find-Path and Find-Next-Step

(defun count-non-members (x y)
  (cond ((endp x) 0)
        ((member (car x) y) (count-non-members (cdr x) y))
        (t (+ 1 (count-non-members (cdr x) y)))))

(defun measure (c stack g)
  (cons (+ 1 (count-non-members (all-nodes g) stack))
        (len c)))

(defun find-next-step (c stack b g)
  (declare (xargs :measure (measure c stack g)))
  (cond
   ((endp c) 'failure)
   ((member (car c) stack)
    (find-next-step (cdr c) stack b g))
   ((equal (car c) b) (rev (cons b stack)))
   (t (let ((temp (find-next-step (neighbors (car c) g)
                                  (cons (car c) stack)
                                  b g)))
        (if (equal temp 'failure)
            (find-next-step (cdr c) stack b g)
          temp)))))

(defun find-path (a b g)
  (cond ((equal a b) (list a))
        (t (find-next-step (neighbors a g)
                           (list a)
                           b g))))

(defthm Example2
  (let ((g '((A B)
             (B C F)
             (C D F)
             (D E F)
             (E F)
             (F B C D E))))
    (and (graphp g)
         (equal (find-path 'A 'E g) '(A B C D E))
         (path-from-to '(A B C D E) 'A 'E g)
         (path-from-to '(A B F E)   'A 'E g)
         (equal (find-path 'F 'A g) 'failure)))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Sketch of the Proof of Our Main Theorem

; (no events)

; --------------------------------------------------------------------------
; Observation 0

      (defthm pathp-append
        (implies (and (true-listp p1)
                      (true-listp p2))
                 (iff (pathp (append p1 p2) g)
                      (cond ((endp p1) (pathp p2 g))
                            ((endp p2) (pathp p1 g))
                            (t (and (pathp p1 g)
                                    (pathp p2 g)
                                    (member (car p2)
                                            (neighbors (car (last p1))
                                                       g))))))))

   (defthm pathp-find-next-step
     (implies (and (true-listp stack)
                   (consp stack)
                   (pathp (rev stack) g)
                   (subsetp c (neighbors (car stack) g))
                   (not (equal (find-next-step c stack b g) 'failure)))
              (pathp (find-next-step c stack b g) g)))

   (defthm car-find-next-step
     (implies (and (true-listp stack)
                   (consp stack)
                   (not (equal (find-next-step c stack b g) 'failure)))
              (equal (car (find-next-step c stack b g))
                     (car (last stack)))))

   (defthm car-last-find-next-step
     (implies (and (true-listp stack)
                   (consp stack)
                   (not (equal (find-next-step c stack b g) 'failure)))
              (equal (car (last (find-next-step c stack b g)))
                     b)))

(defthm Observation-0
  (implies (not (equal (find-path a b g) 'failure))
           (path-from-to (find-path a b g) a b g))
  :rule-classes nil)

; --------------------------------------------------------------------------
; Observation 1

(defun simple-pathp (p g)
  (and (no-duplicatesp p)
       (pathp p g)))

   (defun chop (e p)
     (cond ((endp p) nil)
           ((equal e (car p)) p)
           (t (chop e (cdr p)))))

(defun simplify-path (p)
  (cond ((endp p) nil)
        ((member (car p) (cdr p))
         (simplify-path (chop (car p) (cdr p))))
        (t (cons (car p) (simplify-path (cdr p))))))

      (defthm car-chop
        (implies (member e p)
                 (equal (car (chop e p)) e)))

   (defthm car-simplify-path
     (equal (car (simplify-path p)) (car p)))

         (defthm chop-iff-consp
           (implies (member e p)
                    (consp (chop e p))))

      (defthm simplify-path-iff-consp
        (iff (consp (simplify-path p)) (consp p)))

      (defthm car-last-chop
        (implies (member e p)
                 (equal (car (last (chop e p))) (car (last p)))))

   (defthm car-last-simplify-path
     (equal (car (last (simplify-path p))) (car (last p))))

      (defthm pathp-chop
        (implies (and (member e p)
                      (pathp p g))
                 (pathp (chop e p) g)))

   (defthm pathp-simplify-path
     (implies (pathp p g)
              (pathp (simplify-path p) g)))

         (defthm not-member-chop
           (implies (not (member x p))
                    (not (member x (chop e p)))))

      (defthm not-member-simplify-path
        (implies (not (member x p))
                 (not (member x (simplify-path p)))))

   (defthm no-duplicatesp-simplify-path
     (no-duplicatesp (simplify-path p)))

(defthm Observation-1
  (implies (path-from-to p a b g)
           (and (simple-pathp (simplify-path p) g)
                (path-from-to (simplify-path p) a b g)))
  :rule-classes nil)

; --------------------------------------------------------------------------
; Observation 2

(defun find-all-next-steps (c stack b g)
  (declare (xargs :measure (measure c stack g)))
  (cond
   ((endp c) nil)
   ((member (car c) stack)
    (find-all-next-steps (cdr c) stack b g))
   ((equal (car c) b)
    (cons (rev (cons b stack))
          (find-all-next-steps (cdr c) stack b g)))
   (t (append (find-all-next-steps (neighbors (car c) g)
                                   (cons (car c) stack)
                                   b g)
              (find-all-next-steps (cdr c) stack b g)))))

(defun find-all-simple-paths (a b g)
  (if (equal a b)
      (list (list a))
    (find-all-next-steps (neighbors a g)
                         (list a)
                         b g)))

(defun induction-hint-function (p c stack g)
  (declare (xargs :measure (measure c stack g)))
  (cond
   ((endp c) (list p c stack g)) ; Base Case
   ((member (car c) stack) ; Induction Step 1
    (induction-hint-function p (cdr c) stack g))
   ((equal (car c) (car p)) ; Induction Step 2
    (induction-hint-function (cdr p)
                             (neighbors (car c) g)
                             (cons (car c) stack)
                             g))
   (t (induction-hint-function p (cdr c) stack g))))


            (defthm subsetp-find-all-next-steps-neighbors
              (implies (and (not (member e stack))
                            (not (equal e b))
                            (member e d))
                       (subsetp (find-all-next-steps (neighbors e g)
                                                     (cons e stack) b g)
                                (find-all-next-steps d stack b g))))

            (defthm member-find-all-next-steps
              (implies (and (not (member c1 stack))
                            (member c1 d))
                       (member (append (rev stack) (list c1))
                               (find-all-next-steps d stack c1 g))))

         (defthm subsetp-find-all-next-steps
           (implies (subsetp c d)
                    (subsetp (find-all-next-steps c stack b g)
                             (find-all-next-steps d stack b g))))

         (defthm subsetp-member-member
           (implies (and (subsetp a b)
                         (member e a))
                    (member e b)))

      (defthm Crux-cdr
        (implies (and (consp c)
                      (member p (find-all-next-steps (cdr c) stack b g)))
                 (member p (find-all-next-steps c stack b g)))

        :hints (("Goal"
                 :use
                 (:instance
                  subsetp-member-member
                  (a (find-all-next-steps (cdr c) stack b g))
                  (b (find-all-next-steps c stack b g))
                  (e p))
                 :in-theory (disable subsetp-member-member))))

   (defthm Crux
     (implies (and (true-listp stack)
                   (consp stack)
                   (pathp p g)
                   (member (car p) c)
                   (no-duplicatesp (append stack p)))
              (member (append (rev stack) p)
                      (find-all-next-steps c stack (car (last p)) g)))
     :hints
     (("Goal"
       :induct (induction-hint-function p c stack g)))
     :rule-classes nil)

(defthm Observation-2
  (implies (and (simple-pathp p g)
                (path-from-to p a b g))
           (member p (find-all-simple-paths a b g)))
  :rule-classes nil
  :hints (("Goal"
           :use (:instance Crux
                           (c (neighbors (car p) g))
                           (stack (list (car p)))
                           (p (cdr p))
                           (g g)))))

; --------------------------------------------------------------------------
; Observation 3

   (defthm find-all-next-steps-v-find-next-step
     (iff (find-all-next-steps x stack b g)
          (not (equal (find-next-step x stack b g) 'failure))))

(defthm Observation-3
  (iff (find-all-simple-paths a b g)
       (not (equal (find-path a b g) 'failure)))
  :rule-classes nil)

; --------------------------------------------------------------------------
; The Main Theorem

(defthm Main
  (implies (path-from-to p a b g)
           (path-from-to (find-path a b g) a b g))
  :hints (("Goal"
           :use (Observation-0
                 Observation-1
                 (:instance Observation-2 (p (simplify-path p)))
                 Observation-3)
           :in-theory (disable find-path
                               find-all-simple-paths))))

; ---------------------------------------------------------------------------
; The Specification of Find-Path

(defthm Spec-of-Find-Path
  (implies (and (graphp g)
                (nodep a g)
                (nodep b g)
                (path-from-to p a b g))
           (path-from-to (find-path a b g) a b g))
  :hints (("Goal" :in-theory (disable path-from-to find-path))))
