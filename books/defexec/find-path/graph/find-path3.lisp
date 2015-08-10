; An Exercise in Graph Theory
; J Strother Moore

; This file is an ACL2 book.  To certify it, execute:
;
; (certify-book "find-path3")
;
; This file is a cleaned up version of the file find-path2.lisp.  In it, I
; have introduced the top-down macro and used it to structure my graph
; theory proof more or less as it is described in the paper.

; You should be able to read this book in lieu of the paper, if you
; know ACL2.

; ---------------------------------------------------------------------------
; Getting Started

(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
(include-book "helpers")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defmacro top-down (main &rest others)
  `(progn ,@others ,main))

; ---------------------------------------------------------------------------
; The Primitives of Directed Graphs

(top-down

 (defun graphp (g)
   (and (alistp g)
        (no-duplicatesp (all-nodes g))
        (graph1p g (all-nodes g))))

 ; where

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
                 (graph1p (cdr g) nodes))))))

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

(top-down

 (defun measure (c stack g)
   (cons (+ 1 (count-non-members (all-nodes g) stack))
         (len c)))

 ; where

 (defun count-non-members (x y)
   (cond ((endp x) 0)
         ((member (car x) y) (count-non-members (cdr x) y))
         (t (+ 1 (count-non-members (cdr x) y))))))

(top-down

 (defun find-path (a b g)
   (cond ((equal a b) (list a))
         (t (find-next-step (neighbors a g)
                            (list a)
                            b g))))

 ; where

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
           temp))))))

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

(top-down

 (defthm Main
   (implies (path-from-to p a b g)
            (path-from-to (find-path a b g) a b g))

; Proof of Main:
; The proof follows from four observations, as indicated below.

   :hints (("Goal"
            :use (Observation-0
                  Observation-1
                  (:instance Observation-2 (p (simplify-path p)))
                  Observation-3)
            :in-theory (disable find-path
                                find-all-simple-paths))))

; Now we state and prove the observations.

; --------------------------------------------------------------------------
; Observation 0

 (top-down

  (defthm Observation-0
    (implies (not (equal (find-path a b g) 'failure))
             (path-from-to (find-path a b g) a b g))
    :rule-classes nil)

  ; Proof

  (top-down

   (defthm pathp-find-next-step
     (implies (and (true-listp stack)
                   (consp stack)
                   (pathp (rev stack) g)
                   (subsetp c (neighbors (car stack) g))
                   (not (equal (find-next-step c stack b g) 'failure)))
              (pathp (find-next-step c stack b g) g)))

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
                                                    g)))))))))

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
                    b))))  ; Q.E.D. Observation-0

; --------------------------------------------------------------------------
; Observation 1

; To state the next observation we need these concepts.

 (defun simple-pathp (p g)
   (and (no-duplicatesp p)
        (pathp p g)))

 (top-down

  (defun simplify-path (p)
    (cond ((endp p) nil)
          ((member (car p) (cdr p))
           (simplify-path (chop (car p) (cdr p))))
          (t (cons (car p) (simplify-path (cdr p))))))

  ; where

  (defun chop (e p)
    (cond ((endp p) nil)
          ((equal e (car p)) p)
          (t (chop e (cdr p))))))

; Note that chop is actually equal to member.  But I prefer the name
; chop for pedagogical reasons:  it makes it easier to see lemmas that
; are ``predicted'' by general patterns.

; It is helpful to observe the following fact about simplify-path.

 (top-down

  (defthm simplify-path-iff-consp
    (iff (consp (simplify-path p)) (consp p)))

  (defthm chop-iff-consp
    (implies (member e p)
             (consp (chop e p)))))

; Here is next observation.

 (top-down

  (defthm Observation-1
    (implies (path-from-to p a b g)
             (and (simple-pathp (simplify-path p) g)
                  (path-from-to (simplify-path p) a b g)))
    :rule-classes nil)

  ; Proof

  (top-down

   (defthm car-simplify-path
     (equal (car (simplify-path p)) (car p)))

   (defthm car-chop
     (implies (member e p)
              (equal (car (chop e p)) e))))

  (top-down

   (defthm car-last-simplify-path
     (equal (car (last (simplify-path p))) (car (last p))))

   (defthm car-last-chop
     (implies (member e p)
              (equal (car (last (chop e p))) (car (last p))))))

  (top-down

   (defthm pathp-simplify-path
     (implies (pathp p g)
              (pathp (simplify-path p) g)))


   (defthm pathp-chop
     (implies (and (member e p)
                   (pathp p g))
              (pathp (chop e p) g))))

  (top-down

   (defthm no-duplicatesp-simplify-path
     (no-duplicatesp (simplify-path p)))

   (top-down

    (defthm not-member-simplify-path
      (implies (not (member x p))
               (not (member x (simplify-path p)))))

    (defthm not-member-chop
      (implies (not (member x p))
               (not (member x (chop e p)))))))) ; Q.E.D. Observation-1

; --------------------------------------------------------------------------
; Observation 2

; The next observation requires these concepts.

 (top-down

  (defun find-all-simple-paths (a b g)
    (if (equal a b)
        (list (list a))
      (find-all-next-steps (neighbors a g)
                           (list a)
                           b g)))

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
                (find-all-next-steps (cdr c) stack b g))))))

 (top-down

  (defthm Observation-2
    (implies (and (simple-pathp p g)
                  (path-from-to p a b g))
             (member p (find-all-simple-paths a b g)))
    :rule-classes nil

    ; Proof

    :hints (("Goal"
             :use (:instance Crux
                             (c (neighbors (car p) g))
                             (stack (list (car p)))
                             (p (cdr p))
                             (g g)))))

  ; where

  (top-down

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

   ; where the induction hint is given by:

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

   ; Proof of Crux

   (top-down

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

       (top-down

        (defthm subsetp-find-all-next-steps
          (implies (subsetp c d)
                   (subsetp (find-all-next-steps c stack b g)
                            (find-all-next-steps d stack b g))))

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
                           (find-all-next-steps d stack c1 g)))))

    (defthm subsetp-member-member
      (implies (and (subsetp a b)
                    (member e a))
               (member e b)))))) ; Q.E.D. Crux-cdr, Crux, and Observation-2

; --------------------------------------------------------------------------
; Observation 3

 (top-down

  (defthm Observation-3
    (iff (find-all-simple-paths a b g)
         (not (equal (find-path a b g) 'failure)))
    :rule-classes nil)

  (defthm find-all-next-steps-v-find-next-step
    (iff (find-all-next-steps x stack b g)
         (not (equal (find-next-step x stack b g) 'failure))))))

; Q.E.D. Observation-3 and Main

; --------------------------------------------------------------------------
; The Main Theorem

; (no more events)

; ---------------------------------------------------------------------------
; The Specification of Find-Path

(defthm Spec-of-Find-Path
  (implies (and (graphp g)
                (nodep a g)
                (nodep b g)
                (path-from-to p a b g))
           (path-from-to (find-path a b g) a b g))
  :hints (("Goal" :in-theory (disable path-from-to find-path))))

