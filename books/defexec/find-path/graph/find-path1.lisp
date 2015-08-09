; An Exercise in Graph Theory
; J Strother Moore

; This file is an ACL2 book.  To certify it, execute:
;
; (certify-book "find-path1")

; The exercise in question is to prove that a certain function
; correctly finds a path between two nodes in a directed graph, if
; such a path exists.  The article in the Case Studies book explains
; the problem and my solution in complete detail.

; This file is my first solution.  However, it has been formatted in a
; rather peculiar way to give you some clue as to how it evolved.
; First, I have added sections corresponding to the paper, to help you
; find your way around.

; More peculiarly, I have indented certain commands to show which
; commands were typed in support of others while applying The Method.
; All commands that start on the left-margin were in my initial
; script.  That is, essentially before I ever tried to prove anything
; with ACL2, I typed in the problem, the four observations, the Main
; theorem and the Spec-of-Find-Path.  (Actually, I submitted the
; defuns as I entered them in the script and debugged the definitions
; with examples.)

; Thereafter, whenever I entered a new supporting lemma while
; following The Method, I indented it three spaces further than the
; goal it was intended to support.  This gives a rather peculiar
; outline form, which nevertheless gives you a good bit of information
; about when I "discovered" what.

; Here is a made-up example of this form.  Pretend the left margin is
; where the vertical bar is shown below.

; |      (defthm A1 ...)
; |      (defthm A2 ...)
; |   (defthm A ...)
; |      (defthm B1 ...)
; |   (defthm B ...)
; |(defthm THM ...)

; Then you can deduce that I started to prove THM and discovered that
; I needed A and B.  These discoveries were made by looking at failed
; proofs of THM.  What this notation DOES NOT tell you is whether I
; discovered A and B by looking at the one failed proof of THM, or
; whether I discovered A, proved it, tried THM again, looked at
; another failed proof, and discovered B.  My style generally leads to
; the second kind of history: add one thing at a time.  But in any
; case, you can tell I proved A and B in support of THM, that I didn't
; think of them until I saw a failed proof of THM, and that I proved A
; before B.

; Not to belabor this point, but the made-up script below suggests the
; following history with The Method:

; command issued to ACL               result

; (defthm THM ...)                    failed proof
; (defthm A ...)                      failed proof
; (defthm A1 ...)                     Q.E.D.
; (defthm A ...)                      failed proof
; (defthm A2 ...)                     Q.E.D.
; (defthm A ...)                      Q.E.D.
; (defthm THM ...)                    failed proof
; (defthm B ...)                      failed proof
; (defthm B1 ...)                     Q.E.D.
; (defthm B ...)                      Q.E.D.
; (defthm THM ...)                    Q.E.D.

; In the actual script below, there are some lemmas that having
; nothing to do with the graph problem per se, but are just nice facts
; about list processing functions.  I have marked those with comments.
; Once I proved Spec-of-Find-Path, I moved those lemmas into a
; separate book, helpers, and named the remainder of this file
; find-path2.

; ---------------------------------------------------------------------------
; Getting Started

(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)
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

; list processing
(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

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

         ; list processing
         (defthm append-right-id
           (implies (true-listp a)
                    (equal (append a nil) a)))

         ; list processing
         (defthm consp-append
           (implies (consp a)
                    (consp (append a b)))
           :rule-classes :type-prescription)

         ; list processing
         (defthm car-append
           (equal (car (append x y))
                  (if (consp x) (car x) (car y))))

      ; The next theorem is proveable without the help above.  But I
      ; saw that they would be used if available and recognized them
      ; as probably useful in the remainder of this exercise, so I
      ; proved them.

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

      ; Below you will see that this region is in support of
      ; pathp-find-next-step.  The lemma above, pathp-append, was
      ; suggested by a failed proof of that theorem.  But when I tried
      ; pathp-find-next-step after proving pathp-append, the
      ; expression (pathp (append ...) ...) still occurred in the
      ; proof.  That means ACL2 wasn't able to relieve (at least one
      ; of) the two true-lists hypotheses of pathp-append.  So I
      ; proved the next two lemmas.

      ; list processing
      (defthm true-listp-append-rewrite
        (equal (true-listp (append a b))
               (true-listp b)))

      ; list processing
      (defthm true-listp-rev
        (true-listp (rev x)))

         ; list processing
         (defthm subsetp-cons
           (implies (subsetp x y)
                    (subsetp x (cons e y))))

      ; An instance of the following lemma arose in the next failed
      ; attempt at pathp-find-next-step.

      ; list processing
      (defthm subsetp-x-x
        (subsetp x x))

      ; An instance of the term (car (last (rev ...))) arose in the
      ; the next failed attempt at pathp-find-next-step.  That gave
      ; rise to car-last-rev, below, which led me to prove the next
      ; two lemmas.

         ;  This next event was proved because I saw its need in the
         ;  first attempt at car-last-rev.  But then I proved
         ;  last-append, below, and then car-last-rev was proved
         ;  without needing this.  But it is a nice fact that is used
         ;  later anyway.

         ; list processing
         (defthm assoc-of-append
           (equal (append (append a b) c)
                  (append a (append b c))))

         ; list processing
         (defthm last-append
           (implies (consp b)
                    (equal (last (append a b))
                           (last b))))

      ; list processing
      (defthm car-last-rev
        (equal (car (last (rev x)))
               (car x)))

   (defthm pathp-find-next-step
     (implies (and (true-listp stack)
                   (consp stack)
                   (pathp (rev stack) g)
                   (subsetp c (neighbors (car stack) g))
                   (not (equal (find-next-step c stack b g) 'failure)))
              (pathp (find-next-step c stack b g) g)))

; My commentary is more sparse now, because I assume you've gotten
; used to this inside-out notation.  Obviously, I next tried to prove
; car-find-next-step, which gave rise to trying to prove car-rev,
; which suggested proving consp-rev, ...

         ; list processing
         (defthm consp-rev
           (implies (consp x)
                    (consp (rev x)))
           :rule-classes :type-prescription)

      ; list processing
      (defthm car-rev
        (equal (car (rev x)) (car (last x))))

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

      ; As the indentation suggests, the next event was discovered
      ; while trying to prove car-last-simplify-path.  It is used in
      ; that proof.  But it is also used in the proof of
      ; pathp-simplify-path.  So in the final script I decided to move
      ; it to before both.

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

   ; Obviously, before I typed this induction hint, I worked out a
   ; hand proof of Crux.

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


                  ; list processing
                  (defthm member-append
                    (iff (member x (append a b))
                         (or (member x a)
                             (member x b))))

               ; The next lemma is sort of strange because it is
               ; really two.  Each conjunct is stored as a rewrite
               ; rule.  I put them together like this just for
               ; elegance.  I didn't want to think about whether I
               ; knew (subsetp a b) or (subsetp a c).

               ; list processing
               (defthm subsetp-append-2
                 (and (implies (subsetp a b)
                               (subsetp a (append b c)))
                      (implies (subsetp a c)
                               (subsetp a (append b c)))))

            (defthm subsetp-find-all-next-steps-neighbors
              (implies (and (not (member e stack))
                            (not (equal e b))
                            (member e d))
                       (subsetp (find-all-next-steps (neighbors e g)
                                                     (cons e stack) b g)
                                (find-all-next-steps d stack b g))))

            ; list processing
            (defthm subsetp-append-1
              (iff (subsetp (append a b) c)
                   (and (subsetp a c)
                        (subsetp b c))))

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

      ; list processing
      (defthm equal-append
        (equal (equal (append x y)
                      (append x z))
               (equal y z)))

      ; list processing
      (defthm duplicatesp-preserved-by-append
        (implies (not (no-duplicatesp y))
                 (not (no-duplicatesp (append x y)))))

      ; I think this next fact is really pretty.

      ; list processing
      (defthm no-duplicatesp-append-cons
        (equal (no-duplicatesp (append a (cons e b)))
               (and (not (member e a))
                    (not (member e b))
                    (no-duplicatesp (append a b)))))

      ; list processing
      (defthm member-car-last
        (iff (member (car (last x)) x)
             (consp x)))

   ; The first submission of Crux via The Method gave rise to
   ; Crux-cdr.  Once I proved that, I submitted Crux again, of course.
   ; The Method dictates paying special attention to the first
   ; unproved subgoal that is stable under simplification.  But in
   ; that next submission of Crux, that unproved subgoal was actually
   ; proved by the subsequent destructor elimination.  The same thing
   ; happened with several subsequent stable subgoals.  Basically,
   ; elim is being used in this proof to identify p with (list (car
   ; p)) when p is a singleton, and to identify p with (cons (car c)
   ; (cdr p)) when (car c) is (car p).  So I accepted destructor
   ; elimination as a key technique in the proof and stopped looking
   ; at the first stable subgoal.  Instead, I started scanning for the
   ; next checkpoints, e.g., generalizations.  That led me to the
   ; sequence of list processing lemmas between here and Crux-cdr
   ; above.

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
