; Solutions to the Exercises for:

;   An Exercise in Graph Theory
;   by J Strother Moore

; This is an ACL2 file but it is not a book.  It contains expressions
; that are not allowed in certified books.

; I provide solutions to the exercises in my chapter.  To find the
; solution for exercise n, search for ``; Exercise n''.  Some of the
; exercises just call for explanations.  But others call for ACL2
; commands to lead the system to some proof.  So the explanations are
; all comments here and the commands are not.  Every exercise that
; contains commands starts with a command to configure the ACL2
; database appropriately.  The most common such command here is
; (ubt! 1), which means ``undo back through command 1 (without 
; asking any questions).  The other common such context-setting
; command here is to use LD to load one of the support files mentioned
; in the chapter.  I use the :ld-pre-eval-filter option of LD to
; load the file up through a given event.  By starting every command
; sequence with a context-setting command, each solution can be executed
; independently.  But it does mean that processing them all is a lot slower
; than it could be, since each command sets the context from scratch.

; Before you try to execute any of these solutions, you should install
; in some directory the supporting books

;  find-path1.lisp
;  find-path2.lisp
;  find-path3.lisp
;  helpers.lisp
;  linear-find-path.lisp

; then select that directory as the connected directory and start
; ACL2.

; You may be tempted to load this file into ACL2, with ld, rather than
; to execute individual commands from within this file.  I recommend
; against just loading the whole file.  Most of the pedagogical material
; here is in comments that won't show up when you load the file.
; You should consider this file the explanation of my solutions and you
; should execute the individual commands in it as necessary to explore
; my solutions.

; Also, remember that if you have proved different lemmas than I
; prove, then my solution to any given exercise will not necessarily
; work in your context.

; -----------------------------------------------------------------
; Exercise 1

; (defthm member-append
;   (equal (member x (append a b))
;          (or (member x a)
;              (member x b))))

; is not a theorem because member is not Boolean-valued.  Instead of
; returning T it returns a tail of its second argument, indicating where
; the first argument occurs as an element.

; For example, (member 1 '(0 1 2 3)) is (1 2 3).  Hence, here is a counter-
; example to the conjecture above.

(let ((x 1)
      (a '(0 1 2))
      (b '(3 4 5)))
  (equal (member x (append a b))
         (or (member x a)
             (member x b))))

; The expression above evaluates to nil, because the member-expression
; on the left-hand side evaluates to (1 2 3 4 5) but the or-expression
; on the right-hand side evaluates to (1 2).

; When looking for counterexamples, I sometimes type expressions like
; this,

(let ((x 1)
      (a '(0 1 2))
      (b '(3 4 5)))
  (list (member x (append a b))
        (or (member x a)
            (member x b))))

; where I've replaced the EQUAL with LIST.  This way I get to see the
; values of the two allegedly equal terms.

; Here is a corrected version of the conjecture.

(ubt! 1)

(defthm member-append
  (iff (member x (append a b))
       (or (member x a)
           (member x b))))

; This theorem is proved automatically by ACL2 in its initial state.  It
; is just a simple induction on a.  As a rewrite rule, it replaces
; instances of (member x (append a b)) by the corresponding instances of
; the or-expression, in contexts in which we are just concerned about
; propositional equivalence.

; -----------------------------------------------------------------
; Exercise 2

(ubt! 1)

(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defthm car-last-rev
  (equal (car (last (rev x)))
         (car x)))

; ACL2 proves car-last-rev without help, from its initial state.
; However, The Method suggests a lemma about last and append.  So let me
; undo the last theorem,

(u)

; and prove the following lemma first.

(defthm last-append
  (implies (consp b)
           (equal (last (append a b))
                  (last b))))

; Now the proof of car-last-rev is more direct: no induction is required.

(defthm car-last-rev
  (equal (car (last (rev x)))
         (car x)))

; Note that a stronger theorem about last and append is possible:

(defthm strong-last-append
  (equal (last (append a b))
         (if (consp b)
             (last b)
           (if (consp a)
               (cons (car (last a)) b)
             b))))


; -----------------------------------------------------------------
; Exercise 3

; The rewrite rule suggested to me is shown below.  To prove it
; I first have to prove the previously mentioned member-append.

(ubt! 1)

(defthm member-append
  (iff (member x (append a b))
       (or (member x a)
           (member x b))))

(defthm no-duplicatesp-append-cons
  (equal (no-duplicatesp (append a (cons e b)))
         (and (not (member e a))
              (not (member e b))
              (no-duplicatesp (append a b)))))

; -----------------------------------------------------------------
; Exercise 4

; Find-next-step terminates because on each recursion either the number
; of unvisited nodes decreases or else the number of unvisted nodes
; stays fixed but the number of neighbors (of the current node) to be
; tried decreases.  Here, by ``unvisited nodes'' we mean ``nodes of g
; that are not listed in stack.''  Notice that we have just described a
; measure containing two components and we are using a lexicographic
; comparison.

; Here is the definition.  You will not be able to execute this because
; we haven't defined the necessary graph functions (e.g., neighbors).
; But I need to talk about its parts.  I've enclosed this definition in
; the expression comment delimiters, #| ... |#, so it is really just a
; comment here.

#|
(defun find-next-step (c stack b g)
  (cond
   ((endp c) 'failure)
   ((member (car c) stack)
    (find-next-step (cdr c) stack b g))        ; Call 1
   ((equal (car c) b)
    (rev (cons b stack)))
   (t (let ((temp (find-next-step              ; Call 2
                    (neighbors (car c) g)
                    (cons (car c) stack)
                    b g)))
        (if (equal temp 'failure)
            (find-next-step (cdr c) stack b g) ; Call 3
          temp)))))
|#

; In Calls 1 and 3, the first component of the measure stays fixed
; (because stack and g stay fixed) but the second component decreases
; (because c is replaced by (cdr c), where c is known to be a consp).
; In Call 2, the first component appears to decrease -- because an
; element is added to stack and, by hypothesis, that element is not
; already in stack.  That is, the number of unvisited nodes seems to
; decrease.  But, as pointed out in the paper, we have to think about
; what happens if the element added to the stack is not a node.  This
; is discussed in Exercise 7, below.

; -----------------------------------------------------------------
; Exercise 5

; The formal version of the measure is shown below.

; (defun measure (c stack g)
;   (cons (+ 1 (count-non-members (all-nodes g) stack))
;         (len c)))

; Observe that count-non-members, defined below, computes the first
; component and len computes the second.  We add one to the first and
; cons it onto the second to produce an ordinal.  As discussed in
; the book, the pair <i,j> is lexicographically below <m,n> iff either
; i<m, or i=m and j<n.  If i and j are natural numbers, then 
; (cons (+ 1 i) j) is an ordinal.  Furthermore, such ordinals are
; compared lexicographically with e0-ord-<.  This can be said formally
; by just noting that the following is a theorem:

(ubt! 1)

; After the Computer-Aided Reasoning book was written, the
; representation and handling of ordinals in ACL2 has changed. The
; following two forms allow us to revert back to the previous handling
; of ordinals.
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(thm (implies (and (integerp i) (<= 0 i)
                   (integerp j) (<= 0 j)
                   (integerp m) (<= 0 m)
                   (integerp n) (<= 0 n))
              (and (e0-ordinalp (cons (+ 1 i) j))
                   (iff (e0-ord-< (cons (+ 1 i) j)
                                  (cons (+ 1 m) n))
                        (or (< i m)
                            (and (equal i m)
                                 (< j n)))))))

; Thus, the construction of measure, above, captures what we intended.

; It should be noted that the definitional principle requires that we
; be able to prove (e0-ordinalp (measure c stack g)), without any
; restrictions on c, stack and g.  Thus, while the thm above shows us
; that a cons like that in the defun of measure constructs an ordinal
; under appropriate conditions, we actually have to prove that an
; ordinal is constructed under all conditions.  In the case of the
; defun of measure, we rely on the facts that count-non-members and
; len both return natural numbers, regardless of their arguments.

; -----------------------------------------------------------------
; Exercise 6

; Here is a definition of count-non-members.

(ubt! 1)

(defun count-non-members (x y)
  (cond ((endp x) 0)
        ((member (car x) y)
         (count-non-members (cdr x) y))
        (t (+ 1 (count-non-members (cdr x) y)))))

; We could, of course, define this many other ways, e.g.,

(defun set-diff (x y)
  (if (endp x)
      nil
    (if (member (car x) y)
        (set-diff (cdr x) y)
      (cons (car x) (set-diff (cdr x) y)))))

(defun count-non-members-alt (x y)
  (len (set-diff x y)))

; That is, the following is a theorem.

(thm (equal (count-non-members x y)
            (count-non-members-alt x y)))

; -----------------------------------------------------------------
; Exercise 7

; At issue is why our measure decreases in Call 2,

#|
(defun find-next-step (c stack b g)
  (cond
   ((endp c) 'failure)
   ((member (car c) stack)
    (find-next-step (cdr c) stack b g))        ; Call 1
   ((equal (car c) b)
    (rev (cons b stack)))
   (t (let ((temp (find-next-step              ; Call 2
                    (neighbors (car c) g)
                    (cons (car c) stack)
                    b g)))
        (if (equal temp 'failure)
            (find-next-step (cdr c) stack b g) ; Call 3
          temp)))))
|#

; if (car c) is not a node of g.  The first component of the measure
; stays fixed in this case, even though the stack has an additional item
; on it.  But if (car c) is not a node of g, then (neighbors (car c) g)
; is nil.  Hence, the second component of the measure decreases because
; it was (len c) -- which is non-0 since c is non-empty -- and it is now
; (len (neighbors (car c) g)) -- which is 0.

; -----------------------------------------------------------------
; Exercise 8

; The lemma suggested to me by 

; (pathp (append (rev stack)
;                (list (car c)))
;        g)

; is the following.  The exercise doesn't require you to prove it, so
; I've just commented it out.  However, you can see the events leading
; up to a proof of it by looking for pathp-append in find-path1.lisp.

#|
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
|#

; That is, (append p1 p2) is a path, for true lists p1 and p2, precisely
; when both p1 and p2 are paths and the source of path p2 is among the
; neighbors of the target of path p1, with appropriate handling of the
; cases that p1 and/or p2 is empty.

; Find-next-step creates a path by (rev (cons b stack)).  This expands
; to (append (rev stack) (list b)).  Proving that this is a path
; involves reasoning about when (append p1 p2) is a path.  Of course, we
; could formulate a slightly simpler, more restrictive, version based on
; the observation that for our purposes p2 will always be a singleton
; list.

; -----------------------------------------------------------------
; Exercise 9

; The exercise initializes the database as follows.

(ubt! 1)

(rebuild "find-path1.lisp"
         'pathp-append)

; Notice that this initialization includes pathp-append, from Exercise
; 8.

; Using The Method, I repeatedly try to prove pathp-find-next-step,
; below.  Except for the last time, each attempt fails and I see a
; term that suggests a list processing lemma.

; The first time I see (NOT (PATHP (APPEND (REV STACK) (LIST (CAR C)))
; G)) which suggests that the pathp-append lemma isn't being applied.
; Since pathp-append is enabled and matches, the only reason it can
; fail to apply is that ACL2 cannot establish the hypotheses.  This
; suggests proving that (REV STACK) is a true-listp.  So I prove
; true-listp-rev, which also leads me to prove true-listp-append
; first.

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b))
         (true-listp b)))

(defthm true-listp-rev
  (true-listp (rev x)))

; Trying pathp-find-next-step again I see the term (CAR (LAST (REV STACK))).
; This suggests last-rev, which in turn suggests last-append.

(defthm last-append
  (implies (consp b)
           (equal (last (append a b))
                  (last b))))

(defthm last-rev
  (equal (last (rev x))
         (if (endp x)
             nil
           (cons (car x) nil))))

; Trying pathp-find-next-step again, I see 
; (NOT (SUBSETP (NEIGHBORS (CAR C) G)
;               (NEIGHBORS (CAR C) G)))
; which suggests subsetp-x-x.  But to prove it I need subsetp-cons.

(defthm subsetp-cons
  (implies (subsetp x y)
           (subsetp x (cons e y))))

(defthm subsetp-x-x
  (subsetp x x))

; Trying pathp-find-next-step again succeeds.

(defthm pathp-find-next-step
  (implies (and (true-listp stack)
                (consp stack)
                (pathp (rev stack) g)
                (subsetp c (neighbors (car stack) g))
                (not (equal (find-next-step c stack b g) 'failure)))
           (pathp (find-next-step c stack b g) g)))

; -----------------------------------------------------------------
; Exercise 10

; I create the database produced by doing Exercise 9 as follows.

(rebuild "find-path1.lisp"
         'pathp-find-next-step)

; This exercise requires me to prove car-find-next-step and
; car-last-find-next-step.  I use The Method, starting with a failed proof
; of car-find-next-step.

; In the failed proof I see see that I must prove car-rev, below.  Its
; proof succeeds but suggest that I might be better off proving
; consp-rev first.

(defthm consp-rev
  (implies (consp x)
           (consp (rev x)))
  :rule-classes :type-prescription)

(defthm car-rev
  (equal (car (rev x)) (car (last x))))

; The next attempt at car-find-next-step succeeds.

(defthm car-find-next-step
  (implies (and (true-listp stack)
                (consp stack)
                (not (equal (find-next-step c stack b g)
                            'failure)))
           (equal (car (find-next-step c stack b g))
                  (car (last stack)))))

; Then I try car-last-find-next-step, as required by the exercise, and
; it succeeds too.

(defthm car-last-find-next-step
  (implies (and (true-listp stack)
                (consp stack)
                (not (equal (find-next-step c stack b g) 'failure)))
           (equal (car (last (find-next-step c stack b g)))
                  b)))

; -----------------------------------------------------------------
; Exercise 11

; We have been asked to supply the induction hint for Crux.  That is the
; definition below.  But I wanted the solution to show you the induction
; that is done in response to this hint.  So I will first load the database
; to contain my original script up through Crux.

(ubt! 1)

(rebuild "find-path1.lisp"
         'Crux)

; Then I will undo the last event, Crux.

(u)

; Now here is the induction hint.  It has actually already been added
; to the database by the rebuild above, so this defun is redundant.

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

; And here is the proof of Crux using this hint.  If you look at the
; output in response to this sequence of commands, you will see the
; hinted induction scheme.

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

; -----------------------------------------------------------------
; Exercise 12

; We do not offer a hand proof here, just a mechanical one.  If you
; have ACL2 do the proof below, it will essentially print out our
; hand proof.

; Notice in the rebuild below we load find-path2.lisp, as directed by
; the exercise, not find-path1.lisp, which we have been using.  The
; difference is that find-path2.lisp loads all of the list processing
; lemmas we need.  So in applying The Method to prove
; subsetp-find-all-next-steps we just have to look out for
; graph-theory lemmas.

(ubt! 1)

(rebuild "find-path2.lisp"
         'induction-hint-function)

; The first checkpoint in the first attempt at proving
; subsetp-find-all-next-steps is a formula suggestive of the following.

(defthm subsetp-find-all-next-steps-neighbors
  (implies (and (not (member e stack))
                (not (equal e b))
                (member e d))
           (subsetp (find-all-next-steps (neighbors e g) 
                                         (cons e stack) b g)
                    (find-all-next-steps d stack b g))))

; The first checkpoint in the next attempt to prove
; subsetp-find-all-next-steps is a formula suggestive of the
; following.

(defthm member-find-all-next-steps
  (implies (and (not (member c1 stack))
                (member c1 d))
           (member (append (rev stack) (list c1))
                   (find-all-next-steps d stack c1 g))))

; Now we can prove the desired result.

(defthm subsetp-find-all-next-steps
  (implies (subsetp c d)
           (subsetp (find-all-next-steps c stack b g)
                    (find-all-next-steps d stack b g))))

; -----------------------------------------------------------------
; Exercise 13

; This exercise is just like the last one, except we start with 
; find-path1.lisp, which means we don't have the list processing lemmas
; we need.

(ubt! 1)

(rebuild "find-path1.lisp"
         'induction-hint-function)

; This time, before we can prove
; subsetp-find-all-next-steps-neighbors, we must prove the two list
; processing theorems shown below.  These are discovered by using The
; Method.

(defthm member-append
  (iff (member x (append a b))
       (or (member x a)
           (member x b))))

; The next lemma is sort of strange because it is really two.  Each
; conjunct is stored as a rewrite rule.  I put them together like this
; just for elegance.  I didn't want to think about whether I knew
; (subsetp a b) or (subsetp a c).

(defthm subsetp-append-2
  (and (implies (subsetp a b)
                (subsetp a (append b c)))
       (implies (subsetp a c)
                (subsetp a (append b c)))))


; Now this succeeds.

(defthm subsetp-find-all-next-steps-neighbors
  (implies (and (not (member e stack))
                (not (equal e b))
                (member e d))
           (subsetp (find-all-next-steps (neighbors e g) 
                                         (cons e stack) b g)
                    (find-all-next-steps d stack b g))))

; So we turn to member-find-all-next-steps and discover we need
; the following first.

(defthm subsetp-append-1
  (iff (subsetp (append a b) c)
       (and (subsetp a c)
            (subsetp b c))))

; Now the next goal succeeds.

(defthm member-find-all-next-steps
  (implies (and (not (member c1 stack))
                (member c1 d))
           (member (append (rev stack) (list c1))
                   (find-all-next-steps d stack c1 g))))

; And so does the main one.

(defthm subsetp-find-all-next-steps
  (implies (subsetp c d)
           (subsetp (find-all-next-steps c stack b g)
                    (find-all-next-steps d stack b g))))

; -----------------------------------------------------------------
; Exercise 14

(ubt! 1)

(rebuild "find-path1.lisp"
         'Crux)

; Here is the instantiation of Crux that leads to a direct proof of
; Observation-2.

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

; -----------------------------------------------------------------
; Exercise 15

; Here we recreate the database constructed in Exercise 14.

(ubt! 1)

(rebuild "find-path1.lisp"
         'Observation-2)

; We need one lemma, suggested by The Method.

(defthm find-all-next-steps-v-find-next-step
  (iff (find-all-next-steps x stack b g)
       (not (equal (find-next-step x stack b g) 'failure))))

; Then we get our goal.

(defthm Observation-3
  (iff (find-all-simple-paths a b g)
       (not (equal (find-path a b g) 'failure)))
  :rule-classes nil)

; -----------------------------------------------------------------
; Exercise 16

(ubt! 1)

(rebuild "find-path1.lisp"
         'Main)

; To use Main as a rewrite rule in the proof of Spec-of-Find-Path we
; have to disable the non-recursively defined functions path-from-to
; and find-path, so that the target term rewritten by the conclusion
; of Main is not first expanded away.

(defthm Spec-of-Find-Path
  (implies (and (graphp g)
                (nodep a g)
                (nodep b g)
                (path-from-to p a b g))
           (path-from-to (find-path a b g) a b g))
  :hints (("Goal" :in-theory (disable path-from-to find-path))))

; -----------------------------------------------------------------
; Exercise 17

; In this exercise we are asked to find an alternative proof not
; involving find-all-simple-paths.  Essentially I replace
; Observation-2 and Observation-3 with a direct proof of
; Observation-2A below, which says that find-path succeeds if there is
; a simple path.  This was Matt Kaufmann's approach, carried out by
; him as he was proof-reading my chapter.  The events below are my
; proof of his Observation-2A, which isn't too hard from my library.

(ubt! 1)

(include-book "find-path3")

; The following lemma is trivial to prove and is a weaker theorem than
; its namesake.

(defthm Crux-cdr-2A
  (implies (and (not (equal (find-next-step (cdr c)
                                            stack (car (last p))
                                            g)
                            'failure))
                (pathp p g)
                (member (car p) c)
                (no-duplicatesp (append p stack)))
           (not (equal (find-next-step c stack (car (last p))
                                       g)
                       'failure)))
  :hints (("Goal" :expand (find-next-step c stack (car (last p)) g))))


; The Crux lemma has exactly the same inductive argument.

(defthm Crux-2A
  (implies (and (pathp p g)
                (member (car p) c)
                (no-duplicatesp (append p stack)))
           (not (equal (find-next-step c
                                       stack
                                       (car (last p))
                                       g)
                       'failure)))
  :rule-classes nil
  :hints
  (("Goal" :induct (induction-hint-function p c stack g))))

; I need the next lemma to argue that (no-duplicatesp (append p nil))
; is (no-duplicatesp p).

(defthm true-listp-pathp
  (implies (pathp p g)
           (true-listp p)))

; So here is the direct observation that the existence of a simple
; path implies that find-path succeeds.

(defthm Observation-2A
  (implies (and (simple-pathp p g)
                (path-from-to p a b g))
           (not (equal (find-path a b g) 'failure)))
  :rule-classes nil
  :hints (("Goal"
           :use (:instance Crux-2A
                           (c (neighbors (car p) g))
                           (p (cdr p))
                           (stack (list (car p)))))))

; Just to show that this is sufficient, here is the proof that
; Observation-2A (along with the already proved observations 0 and 1)
; gives us Main.  Note that I disable Main below.

(defthm main-a
  (implies (path-from-to p a b g)
           (path-from-to (find-path a b g) a b g))
  :rule-classes nil
  :hints
  (("Goal"
    :use (observation-0
          observation-1
          (:instance observation-2a (p (simplify-path p))))
    :in-theory (disable main find-path))))

; Minor Technical Note: This list of commands does not demonstrate
; that we did not use find-all-simple-paths!  It is defined in
; find-path3, which we included above.  And many facts about it are
; proved there, e.g., Observation-2 and Observation-3.  So we don't
; KNOW, just by the success of the commands here, that ACL2 found the
; new proof of Main and not the old.  To be sure, logically, we should
; not define that function or not have those old observations around.
; But inspection of the output confirms that the proof was the new
; one.

; -----------------------------------------------------------------
; Exercise 18

(ubt! 1)

; Let's start by playing with the definition in :program mode.

(defun f (x)
  (declare (xargs :mode :program))
  (if (zp x)
      0
      (+ 1 (f (f (- x 1))) )))

; Here are some tests:
; ACL2 !>(f 3)
; 3
; ACL2 !>(f 10)
; 10

; It seems to terminate and to return its argument (for natural numbers,
; at least).

; We could try to admit the function in :logic mode, using the measure
; (acl2-count x), just by typing:

; (verify-termination f)

; That will generate the measure conjectures for acl2-count.  The first
; two are trivial and are not printed by ACL2.  The third is not proved
; and the admission attempt fails.

; But that doesn't mean it is impossible.  Suppose we imagine a new
; measure, m.  Here are the conjectures required by the definitional
; principle.

; (e0-ordinalp (m x))

; (implies (not (zp x))
;          (e0-ord-< (m (- x 1)) (m x)))

; (implies (not (zp x))
;          (e0-ord-< (m (f (- x 1))) (m x)))

; If the last could be proved BEFORE f IS DEFINED, then we could prove
; anything!

; Why?  Because if we could prove the last measure conjecture without
; using the definition of f, then we could define (g x) = (+ 1 x) and
; prove

; (implies (not (zp x))
;          (e0-ord-< (m (g (- x 1))) (m x)))

; using exactly the same proof.  But once we prove the formula above, about
; g, we can get

; (implies (not (zp x))
;          (e0-ord-< (m x) (m x)))

; by expanding the definition of g and using arithmetic.

; Clearly we are in trouble.  To put a bow on it: if the formula above
; is a theorem, then so is nil.  We know (not (e0-ord-< z z)).  So the
; theorem above reduces to the theorem (zp x), which allows us to prove
; (zp 1), which reduces to nil.

; Hence, there is just no measure m for which you can prove the third
; measure conjecture without a definition of f! 

; The definition of f is therefore inadmissible.

; -----------------------------------------------------------------
; Exercise 19
; Exercise 20
; Exercise 21

; I will do all three of these sequentially so I don't have to keep
; repeating myself to rebuild the database constructed by the previous
; exercise.

; Here is a suitable m.

(ubt! 1)

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defun m (x) (acl2-count x))

(defun f (x)
  (declare (xargs :measure (m x)))
  (if (zp x)
      0
      (if (e0-ord-< (m (f (- x 1))) (m x))
          (+ 1 (f (f (- x 1))))
          'impossible)))

; The measure conjectures are as shown in Exercise 18, except in
; addition to the test (not (zp x)) we get the test

; (e0-ord-< (m (f (- x 1))) (m x)). 

; This makes the third measure conjecture trivial.  This is the answer
; to exercise 19.

; Having admitted f we prove the following two interesting facts.

; First, f is actually the identity function (on naturals).

(defthm f-is-identity
  (equal (f x) (nfix x)))

; And hence, it is the case that the e0-ord-< test is always t

(defthm test-is-always-t
  (implies (not (zp x))
           (e0-ord-< (m (f (- x 1))) (m x))))

; Thus the f defined above actually satisfies the originally desired
; equation.

(defthm f-satisfies-original-equation
  (equal (f x)
         (if (zp x)
             0
           (+ 1 (f (f (- x 1))))))
  :rule-classes
  ((:definition :controller-alist ((f t)))))

; The :rule-classes above tells ACL2 to use this equation as though it
; were a recursive definition ``measured'' by the first (only)
; argument of f.  That is, ACL2 uses its definitional heuristics to
; apply this equality, rather than its standard rewrite heuristics.

; So we have now given the answer to exercise 20.

; We now turn to exercise 21, proving uniqueness.

; Here we constrain g to satisfy the original f equation. Obviously,
; we use f as our witness.

(encapsulate ((g (x) t))
             (local (defun g (x) (f x)))
             (defthm g-constraint
               (equal (g x)
                      (if (zp x)
                          0
                        (+ 1 (g (g (- x 1))))))
               :rule-classes
               ((:definition :controller-alist ((g t))))))

; And then here is an inductive proof that g is f!

(defthm g-must-be-f
  (equal (g x) (f x))
  :hints (("Goal" :induct (f x))))

; -----------------------------------------------------------------
; Exercise 22
; Exercise 23

; The solutions to these two exercises are found in the book
; linear-find-path.lisp.  In that book I admit a linear-time find-path
; following the strategy used above for f in exercises 19-21.  Then I
; prove that it is equivalent to find-path.

(ubt! 1)

(include-book "linear-find-path")

; But for the record, here is the definition:

(defun linear-find-next-step (c stack b g mt)
  (declare (xargs :measure (measure c mt g)))
  (cond
   ((endp c) (mv 'failure mt))
   ((markedp (car c) mt)
    (linear-find-next-step (cdr c) stack b g mt))
   ((equal (car c) b)
    (mv (rev (cons b stack))
        mt))
   (t (mv-let (temp new-mt)
              (linear-find-next-step (neighbors (car c) g)
                                     (cons (car c) stack)
                                     b g
                                     (mark (car c) mt))
              (cond
               ((e0-ord-< (measure (cdr c) new-mt g)
                          (measure c mt g))
                (if (eq temp 'failure)
                    (linear-find-next-step (cdr c) stack b g new-mt)
                  (mv temp mt)))
               (t (mv 'impossible 'impossible)))))))

(defun linear-find-path (a b g)
  (cond ((equal a b) (list a))
        (t (mv-let (temp mt)
                   (linear-find-next-step (neighbors a g)
                                          (list a)
                                          b g
                                          (mark a nil))
                   (declare (ignore mt))
                   temp))))

; Note the e0-ord-< test in linear-find-next-step.  I prove that this
; test is always t.  Then I show that linear-find-next-step satisfies
; the original equation and that the solution is unique.

; Finally, I prove that

(defthm linear-find-path-is-find-path
  (equal (linear-find-path a b g)
         (find-path a b g)))

; -----------------------------------------------------------------
; Now return to the initial state.

(ubt! 1)
