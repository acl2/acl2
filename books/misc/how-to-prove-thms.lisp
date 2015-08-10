; Copyright (C) 2013, Regents of the University of Texas
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Solutions to the Exercises
;            in

; How To Prove Theorems Formally
; Matt Kaufmann   J Strother Moore

; This file contains our solutions to the exercises in the paper
; above.  Remember, your solutions may be different but just as
; nice -- or nicer!

; This is a certified book.  Assuming the connected book directory
; (see set-cbd) is set to the directory containing this file, to
; recertify it, execute

; (certify-book "how-to-prove-thms")

; To include this book in a new session, execute

; (include-book "how-to-prove-thms")

; (or use the full pathname to this file from wherever directory
; you are on).

; However, we don't think this is a useful certified book and we certify
; it just to reassure ourselves that every event in it succeeds.  The
; real value of this book is to read it or to read the output produced
; by recertifying it.

; Another way to use the book is to load it into ACL2 and then use
; :ubt to undo back through some event in it so you can play with
; alternative scripts for some problem.

; (ld "how-to-prove-thms.lisp" :ld-pre-eval-print t)

; The output shown here is that for ACL2 Version 2.8.  It may well be
; different from the output of newer ACL2 releases.  But we expect
; the reported behavior to be very very similar.

; ---------------------------------------------------------------------------

(in-package "ACL2")

; ---------------------------------------------------------------------------
; Section 4 - Programming in ACL2

; The definitions of and, or, not, implies, and iff are part of the
; ACL2 system.  You can print them with :pe, e.g.,
; ACL2 !>:pe implies
;  V    -4864  (DEFUN IMPLIES (P Q)
;                     (DECLARE (XARGS :MODE :LOGIC :GUARD T))
;                     (IF P (IF Q T NIL) T))
; You will note that AND and OR are macros.

; Here are the other functions defined in the section:

(defun dup (x)
  (if (consp x)
      (cons (car x)
            (cons (car x)
                  (dup (cdr x))))
      nil))

(defthm dup-examples
  (and (equal (dup '(1 2 3)) '(1 1 2 2 3 3))
       (equal (dup '(hello)) '(hello hello))
       (equal (dup '(A B C . D)) '(A A B B C C)))
  :rule-classes nil)

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defthm app-examples
  (and (equal (app '(1 2 3) '(4 5 6)) '(1 2 3 4 5 6))
       (equal (app '(3 2 1) '(0)) '(3 2 1 0))
       (equal (app '(A B C . D) '(E F)) '(A B C E F)))
  :rule-classes nil)

(defun memp (e x)
  (if (consp x)
      (if (equal e (car x))
          t
        (memp e (cdr x)))
    nil))

(defthm memp-examples
  (and (memp 1 '(0 1 2 3))
       (not (memp 5 '(0 1 2 3)))
       (not (memp 2 '((0) (1) (2))))
       (memp '(2) '((0) (1) (2)))
       (not (memp 2 '(0 1 . 2))))
  :rule-classes nil)

(defun rev (x)
  (if (consp x)
      (app (rev (cdr x)) (cons (car x) nil))
    nil))

(defthm rev-examples
  (and (equal (rev '(1 2 3)) '(3 2 1))
       (equal (rev '(ok)) '(ok))
       (equal (rev '(1 2 3 . END)) '(3 2 1)))
  :rule-classes nil)

(defun rev1 (x a)
  (if (consp x)
      (rev1 (cdr x) (cons (car x) a))
    a))

(defthm rev1-examples
  (and (equal (rev1 '(1 2 3) nil) '(3 2 1))
       (equal (rev1 '(ok) nil) '(ok))
       (equal (rev1 '(1 2 3 . END) nil) '(3 2 1))
       (equal (rev1 '(A B C) '(1 2 3)) '(C B A 1 2 3)))
  :rule-classes nil)

; Solutions to the Exercises in Section 4:

; Problem 4.1:
(defun properp (x)
  (if (consp x)
      (properp (cdr x))
    (equal x nil)))

(defthm properp-examples
  (and (properp '(1 2 3))
       (not (properp '(1 2 3 . END)))
       (properp '((a . 1) (b . 2) (c . 3)))
       (properp nil)
       (not (properp 7)))
  :rule-classes nil)

; Problem 4.2
(defun mapnil (x)
  (if (consp x)
      (cons nil (mapnil (cdr x)))
    nil))

(defthm mapnil-examples
  (and (equal (mapnil '(1 2 3)) '(nil nil nil))
       (equal (mapnil '(hello)) '(nil)))
  :rule-classes nil)

; Problem 4.3
(defun swaptree (x)
  (if (consp x)
      (cons (swaptree (cdr x))
            (swaptree (car x)))
    x))

(defthm swaptree-examples
  (and (equal (swaptree '((a . b) . (c . d)))
              '((d . c) . (b . a)))
       (equal (swaptree '(a b c d))
              '((((nil . d) . c) . b) . a)))
  :rule-classes nil)

; Problem 4.4
(defun ziplists (x y)
  (if (consp x)
      (cons (cons (car x) (car y))
            (ziplists (cdr x) (cdr y)))
    nil))

(defthm ziplists-examples
  (and (equal (ziplists '(a b c) '(1 2 3 4))
              '((a . 1) (b . 2) (c . 3)))
       (equal (ziplists '(a b c) '(1 2))
              '((a . 1) (b . 2) (c . nil))))
  :rule-classes nil)

; Problem 4.5
(defun lookup (x a)
  (if (consp a)
      (if (equal x (car (car a)))
          (cdr (car a))
        (lookup x (cdr a)))
    nil))

(defthm lookup-examples
  (and (equal (lookup 'b '((a . 1) (b . 2) (c . 3) (a . 4))) 2)
       (equal (lookup 'a '((a . 1) (b . 2) (c . 3) (a . 4))) 1)
       (equal (lookup 'x '((a . 1) (b . 2) (c . 3) (a . 4))) nil)
       (equal (lookup 'j '((i . 1) (j . nil) (k . 123))) nil))
  :rule-classes nil)

; Problem 4.6
(defun foundp (x a)
  (if (consp a)
      (if (equal x (car (car a)))
          t
        (foundp x (cdr a)))
    nil))

(defthm foundp-examples
  (and (equal (foundp 'b '((a . 1) (b . 2) (c . 3) (a . 4))) t)
       (equal (foundp 'a '((a . 1) (b . 2) (c . 3) (a . 4))) t)
       (equal (foundp 'x '((a . 1) (b . 2) (c . 3) (a . 4))) nil)
       (equal (foundp 'j '((i . 1) (j . nil) (k . 123))) t))
  :rule-classes nil)

; Problem 4.7
(defun subp (x y)
  (if (consp x)
      (if (memp (car x) y)
          (subp (cdr x) y)
        nil)
    t))

(defthm subp-examples
  (and (subp '(a b b a) '(a b))
       (subp '(a b c) '(e d c b a))
       (not (subp '(a b) '(a c a d a f))))
  :rule-classes nil)

; Problem 4.8
(defun int (x y)
  (if (consp x)
      (if (memp (car x) y)
          (cons (car x) (int (cdr x) y))
        (int (cdr x) y))
    nil))

(defthm int-examples
  (and (equal (int '(a b c) '(a b a d)) '(a b))
       (equal (int '(a b c) '(x y z)) nil)
       (equal (int '(a a b b) '(a b c)) '(a a b b)))
  :rule-classes nil)

; Problem 4.9
; We define (loneseomep e lst) to determine whether e occurs exactly
; once in lst.  We do it without arithmetic, since we haven't
; introduced arithmetic yet.  The idea is to determine if e is a
; member of lst and not a member of the sublist that starts after that
; occurrence of e.  To make this definition we need:

(defun mem (e x) ; where does e occur in x?
  (if (consp x)
      (if (equal e (car x))
          x
        (mem e (cdr x)))
    nil))

(defun lonesomep (e lst)
  (if (mem e lst)
      (not (mem e (cdr (mem e lst))))
    nil))


(defun collect-lonesomep (a b)
; collect elements of a that are lonesome in b
  (if (consp a)
      (if (lonesomep (car a) b)
          (cons (car a)
                (collect-lonesomep (cdr a) b))
        (collect-lonesomep (cdr a) b))
    nil))

(defun leaves (x) ; the leaves of x
  (if (consp x)
      (app (leaves (car x))
           (leaves (cdr x)))
    (cons x nil)))

(defun lonesomes (x)
   (collect-lonesomep (leaves x) (leaves x)))


(defthm lonesomes-examples
  (and (equal (lonesomes '((a . b) . (c . a))) '(b c))
       (equal (lonesomes '((a . a) . a)) nil)
       (equal (lonesomes '(((a . b) . (b . c))
                           .
                           ((x . y) . (c . x))))
              '(a y)))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Section 5 - Elementary Proofs in the ACL2 Logic

(defun treecopy (x)
  (if (consp x)
      (cons (treecopy (car x))
            (treecopy (cdr x)))
     x))

(defthm treecopy-is-id
  (equal (treecopy x) x))

; Solutions to Exercises in Section 5

; Problem 5.1
(defthm associativity-of-app
  (equal (app (app a b) c) (app a (app b c))))

; Problem 5.2
(defthm dup-app
  (equal (dup (app a b)) (app (dup a) (dup b))))

; Problem 5.3
(defthm dup-mapnil
  (equal (dup (mapnil a))
         (mapnil (dup a))))

; Problem 5.4
(defthm properp-app-nil
  (properp (app a nil)))

; Problem 5.5
(defthm swaptree-swaptree
  (equal (swaptree (swaptree x)) x))

; Problem 5.6
(defthm memp-app
  (equal (memp e (app a b))
         (or (memp e a) (memp e b))))

; ---------------------------------------------------------------------------
; Section 6 - Three Basic Proof Techniques

; Solution to the Exercises in Section 6

; The single exercise in this section was not numbered because it is
; not really solvable.  But here is our discussion of the problem.
; Pretend the problem was named 6.1.

; If you undo or disable memp-app above and try to prove the theorem
; of Problem 6.1 you get the failed proof, partially reproduced, below:

#|
(defthm problem-6-1
  (equal (memp e (app a a)) (memp e a)))

Name the formula above *1.

Perhaps we can prove *1 by induction.  Two induction schemes are suggested
by this conjecture.  Subsumption reduces that number to one.

We will induct according to a scheme suggested by (MEMP E A).  This
suggestion was produced using the :induction rules APP and MEMP.  If
we let  (:P A E) denote *1 above then the induction scheme we'll use
is
(AND (IMPLIES (NOT (CONSP A)) (:P A E))
     (IMPLIES (AND (CONSP A)
                   (NOT (EQUAL E (CAR A)))
                   (:P (CDR A) E))
              (:P A E))
     (IMPLIES (AND (CONSP A) (EQUAL E (CAR A)))
              (:P A E))).
This induction is justified by the same argument used to admit MEMP,
namely, the measure (ACL2-COUNT A) is decreasing according to the relation
O< (which is known to be well-founded on the domain recognized by O-
P).  When applied to the goal at hand the above induction scheme produces
the following three nontautological subgoals.

Subgoal *1/3
(IMPLIES (NOT (CONSP A))
         (EQUAL (MEMP E (APP A A)) (MEMP E A))).

But simplification reduces this to T, using the :definitions APP and
MEMP and the :executable-counterpart of EQUAL.

Subgoal *1/2
(IMPLIES (AND (CONSP A)
              (NOT (EQUAL E (CAR A)))
              (EQUAL (MEMP E (APP (CDR A) (CDR A)))
                     (MEMP E (CDR A))))
         (EQUAL (MEMP E (APP A A)) (MEMP E A))).

This simplifies, using the :definitions APP and MEMP, primitive type
reasoning and the :rewrite rules CAR-CONS and CDR-CONS, to

Subgoal *1/2'
(IMPLIES (AND (CONSP A)
              (NOT (EQUAL E (CAR A)))
              (EQUAL (MEMP E (APP (CDR A) (CDR A)))
                     (MEMP E (CDR A))))
         (EQUAL (MEMP E (APP (CDR A) A))
                (MEMP E (CDR A)))).

The destructor terms (CAR A) and (CDR A) can be eliminated by using
CAR-CDR-ELIM to replace A by (CONS A1 A2), (CAR A) by A1 and (CDR A)
by A2.  This produces the following goal.

... <much omitted> ...

Subgoal *1.1.1/1'''
(IMPLIES (AND (NOT (EQUAL (MEMP E (APP A6 (CONS A1 A6)))
                          (MEMP E (APP A6 A6))))
              (EQUAL (MEMP E (APP A6 (LIST* A1 A5 A6)))
                     (MEMP E (APP A6 (CONS A5 A6))))
              (NOT (EQUAL E A1))
              (NOT (EQUAL E A3))
              (NOT (EQUAL E A5)))
         (EQUAL (MEMP E (APP A6 (LIST* A1 A3 A5 A6)))
                (MEMP E (APP A6 (LIST* A3 A5 A6))))).

Name the formula above *1.1.1.2.


This formula is subsumed by one of its parents, *1.1, which we're in
the process of trying to prove by induction.  When an inductive proof
gives rise to a subgoal that is less general than the original goal
it is a sign that either an inappropriate induction was chosen or that
the original goal is insufficiently general.  In any case, our proof
attempt has failed.

Summary
Form:  ( DEFTHM PROBLEM-6-1 ...)
Rules: ((:DEFINITION APP)
        (:DEFINITION MEMP)
        (:ELIM CAR-CDR-ELIM)
        (:EXECUTABLE-COUNTERPART EQUAL)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:INDUCTION APP)
        (:INDUCTION MEMP)
        (:REWRITE CAR-CONS)
        (:REWRITE CDR-CONS))
Warnings:  None
Time:  0.14 seconds (prove: 0.09, print: 0.05, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
|#

; Note the checkpoint formula, Subgoal *1/2', above.  See how we have
; (APP (CDR A) (CDR A)) in the hypothesis and (APP (CDR A) A) in the
; conclusion?  That's a strong suggestion that the theorem is not strong
; enough.

; If we proved the more general memp-app, the proof of Problem 6.1 is
; trivial:

(defthm problem-6-1
  (equal (memp e (app a a)) (memp e a))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Section 7 - ACL2's Proof Strategy

; Problem 7.1
; We have already run the theorem prover on Problems 5.1 - 5.6 above.

; Section 8 - Decomposition into Lemmas - The Method

; Below we reproduce the script shown in the paper for triple-rev and
; then show the final scripts produced by The Method for the problems
; in this section.  You should realize however that there are always
; alternatives to any particular lemma decomposition.  So take our
; solutions merely as examples of working solutions.

; --- Script for proving triple-rev ---
(defthm properp-app
  (equal (properp (app a b))
         (properp b)))

(defthm properp-rev
  (properp (rev x)))

(defthm app-right-identity
  (implies (properp x)
           (equal (app x nil) x)))

(defthm rev-app
  (equal (rev (app a b))
         (app (rev b) (rev a))))

(defthm rev-rev
  (implies (properp z)
           (equal (rev (rev z)) z)))

(defthm triple-rev
  (equal (rev (rev (rev a))) (rev a)))
; --- The End ---

; ---------------------------------------------------------------------------
; Solutions to the Exercises of Section 8

; Problem 8.1

; --- Script for proving complicated-memp-theorem ---

; These two lemmas are just obvious and are developed
; as the initial plan for the proof.

(defthm memp-rev
  (equal (memp e (rev x)) (memp e x)))

(defthm memp-dup
  (equal (memp e (dup x)) (memp e x)))

(defthm complicated-memp-theorem
  (implies (memp e c)
           (memp e (rev (dup (dup c)))))
  :rule-classes nil)
; --- The End ---

; Problem 8.2
; --- Script for proving leaves-swaptree ---

; If you haven't, define the leaves of a binary tree as

(defun leaves (x)
  (if (consp x)
      (app (leaves (car x)) (leaves (cdr x)))
      (cons x nil)))

(defthm leaves-swaptree
  (equal (leaves (swaptree x))
         (rev (leaves x))))

; Note that the proof depends on rev-app, proved earlier.
; --- The End ---

; Problem 8.3
; --- Script for proving subp-x-x ---

(defthm subp-cdr
  (implies (subp x (cdr y)) (subp x y)))

(defthm subp-reflexive
  (subp x x))
; --- The End ---

; Problem 8.4
; --- Script for proving int-x-x

(defthm subp-int
  (implies (and (properp x)
                (subp x y))
           (equal (int x y) x)))

(defthm int-x-x
  (implies (properp x)
           (equal (int x x) x)))

; --- The End ---

; Problem 8.5
; --- Script for proving subp-transitive

; Subp-transitive is actually proved without help right now,
; using subp-cdr and three inductions.  But using the method
; we discover a generally useful lemma.

; The first checkpoint in the (successful) proof of subp-transitive
; here is:
; Subgoal *1/3'
; (IMPLIES (AND (CONSP X)
;               (NOT (MEMP (CAR X) Z))
;               (MEMP (CAR X) Y)
;               (SUBP (CDR X) Y))
;          (NOT (SUBP Y Z)))

; Swap the conclusion and the second hyp (unnegating both) to get
; the equivalent:

; (implies (and (consp x)
;               (subp y z)
;               (memp (car x) y)
;               (subp (cdr x) y))
;          (memp (car x) z))

; Observe the key lemma here is:

(defthm memp-subp
  (implies (and (subp y z)
                (memp e y))
           (memp e z)))

; The lemma above contains a free variable, y.  That is, to apply this
; theorem to rewrite (memp alpha beta), the theorem prover must find a
; term, say gamma, such that it can prove (subp gamma beta) and (memp
; alpha gamma).  It is not very good at guessing instantiations of
; free variables.  See :doc free-variables.

(defthm subp-transitive
  (implies (and (subp x y)
                (subp y z))
           (subp x z)))
; --- The End ---

; Problem 8.6
; --- Script for proving subp-app-a-a

(defthm subp-app-1
  (equal (subp (app a b) c)
         (and (subp a c)
              (subp b c))))

(defthm subp-app-a-a
  (subp (app a a) a))

; --- The End ---

; Problem 8.7
; --- Script for proving seteqp-rev

(defun seteqp (x y)
  (and (subp x y)
       (subp y x)))

(defthm subp-app-2
  (implies (subp a b)
           (subp a (app b c))))

(defthm seteq-rev
  (seteqp (rev a) a))

; --- The End ---

; Problem 8.8
; --- Script for proving app-commutative

(defthm subp-app-3
  (implies (subp a c)
           (subp a (app b c))))

(defthm app-commutative
  (seteqp (app a b) (app b a)))

; --- The End ---

; Problem 8.9

; This problem illustrates the utility of introducing a new concept,
; namely, that of a list of atoms.  The basic idea is that if you take
; the leaves of a list of atoms, you get the same list back with an
; extra NIL at the end.  Then you just observe that (leaves x) is a
; list of atoms.  The thing about (leaves (leaves x)) that is
; suggestive of a problem is that leaves "wants" to explore the car
; and cdr of its argument, but produces a linear list.  So an
; induction to unwind the inner leaves is feeding the outer leaves
; something it cannot very well recur on.  You could probably find
; lemmas to tear it apart, through the apps produced by the inner
; leaves, but this decomposition is much nicer.

; --- Script for proving leaves-leaves

(defun list-of-atomsp (x)
  (if (consp x)
      (and (not (consp (car x)))
           (list-of-atomsp (cdr x)))
    t))

; Note: We could have required the terminator to be nil.  But had we
; done that, the following beautiful theorem would not hold.  We'll
; just add a properp hypothesis when we need it.

(defthm list-of-atomsp-app
  (equal (list-of-atomsp (app a b))
         (and (list-of-atomsp a)
              (list-of-atomsp b))))

(defthm list-of-atomsp-leaves
  (list-of-atomsp (leaves x)))

(defthm leaves-of-list-of-atoms
  (implies (and (properp x)
                (list-of-atomsp x))
           (equal (leaves x) (app x '(nil)))))

(defthm properp-leaves
  (properp (leaves x)))

(defthm leaves-leaves
  (equal (leaves (leaves x)) (app (leaves x) '(nil))))
; --- The End ---

; Problem 8.10
; --- Script for proving memp-lonesomes

(defthm lemma8-10a
  (implies (not (mem e leaves))
           (not (memp e
                      (collect-lonesomep lst leaves)))))

(defthm lemma8-10b
  (implies (mem e (cdr (mem e leaves)))
           (not (memp e (collect-lonesomep lst leaves)))))



(defthm memp-collect-lonesomep
  (iff (memp e (collect-lonesomep lst leaves))
       (and (memp e lst)
            (lonesomep e leaves)))
  )

; Note: Actually, we would not use the lemma decomposition shown above
; because we don't like the lemmas.  But they do achieve a "simplify,
; induct, simplify" proof.  The reason they're needed is that when the
; theorem prover tries to prove memp-collect-lonesomep it invents an
; inductive argument that is a mixture of collect-lonesomep and memp.
; Its invention in this case is unfortunate and leads to an
; excessively complicated proof.  By telling it to do the induction
; suggested by collect-lonesomep alone, the proof is immediate.

; So in our first use of The Method here we looked at the induction
; argument generated, didn't like it, and added the following hint
; argument to the defthm for memp-collect-lonesomep:

;       :hints (("Goal" :induct (collect-lonesomep lst leaves)))

; And it went through simply.  However, since the student hasn't been
; told how to use hints, we decided this solution was not fair and
; followed The Method using only the techniques available to the reader.

(defthm memp-lonesomes
  (iff (memp e (lonesomes x))
       (and (memp e (leaves x))
            (lonesomep e (leaves x)))))

; --- The End ---

; Problem 8.11

; Do not be put off by the number of lemmas.  Just look how beautiful
; they are!  You are developing the first few lemmas of a treastise on
; Peano arithmetic.

; --- Script for proving raise-add ---

(defun nump (x)
  (if (consp x)
      (and (equal (car x) nil)
           (nump (cdr x)))
    (equal x nil)))

(defun add (x y)
  (if (consp x)
      (cons nil (add (cdr x) y))
    (mapnil y)))

(defun mult (x y)
  (if (consp x)
      (add y (mult (cdr x) y))
    nil))

(defun raise (x y)
  (if (consp y)
      (mult x (raise x (cdr y)))
    '(nil)))

(defthm nump-mapnil (nump (mapnil x)))

(defthm nump-add (nump (add x y)))

(defthm nump-mult (nump (mult x y)))

(defthm nump-raise (nump (raise x y)))

(defthm add-identity
  (implies (nump x)
           (equal (add x nil) x)))

(defthm raise-mapnil (equal (raise i (mapnil j)) (raise i j)))

(defthm mult-mapnil-1 (equal (mult (mapnil i) j) (mult i j)))

(defthm mapnil-nump (implies (nump x) (equal (mapnil x) x)))

(defthm add-mapnil-1
  (equal (add (mapnil i) j) (add i j)))

(defthm add-associativity
  (equal (add (add a b) c)
         (add a (add b c))))

(defthm mult-add-distributivity-2
  (equal (mult (add i j) k)
         (add (mult i k) (mult j k))))

(defthm mult-associative
  (equal (mult (mult a b) c)
         (mult a (mult b c))))

(defthm raise-add
  (equal (raise b (add i j))
         (mult (raise b i) (raise b j))))

; --- The End ---

; One of the primary motivations of the remaining problems is just to
; set up enough basic simulated arithmetic to make the factorial
; proof go through.

; Problem 8.12
; --- Script for proving add-commutativity ---
(defthm add-identity-2
  (implies (not (consp j))
           (equal (add i j) (mapnil i))))

(defthm add-cons
  (equal (add i (cons x j))
         (cons nil (add i j))))

(defthm add-commutativity
  (equal (add i j) (add j i)))

; --- The End ---

; Problem 8.13
; --- Script for proving add-commutativity-2 ---

(defthm add-mapnil-2
  (equal (add i (mapnil j)) (add i j)))

(defthm add-commutativity2
  (equal (add i (add j k)) (add j (add i k))))

; --- The End ---

; Problem 8.14
; --- Script for proving mult-commutativity ---

(defthm mult-zero
  (implies (not (consp j))
           (equal (mult i j) nil)))

(defthm mult-cons
  (equal (mult i (cons x j))
         (add i (mult i j))))

(defthm mult-commutativity
  (equal (mult i j) (mult j i)))

; --- The End ---

; Problem 8.15
; --- Script for proving mult-commutativity-2 ---

(defthm mult-mapnil-2
  (equal (mult i (mapnil j)) (mult i j)))

(defthm mult-add-distributivity-1
  (equal (mult k (add i j))
         (add (mult k i) (mult k j))))

(defthm mult-commutativity2
  (equal (mult i (mult j k)) (mult j (mult i k))))

; --- The End ---


; ---------------------------------------------------------------------------
; Section 9 - Accumulators

; --- Script for proving rev1-nil-is-rev ---

(defthm rev1-is-app-rev
      (equal (rev1 x a)
             (app (rev x) a)))

(defthm rev1-nil-is-rev
  (equal (rev1 x nil) (rev x)))

; --- The End ---

; Solutions to the Exercises in Section 9

; Problem 9.1
; --- Script for proving fact1-is-fact ---

(defun fact (n)
  (if (consp n)
      (mult n (fact (cdr n)))
    '(nil)))

(defun fact1 (n a)
  (if (consp n)
      (fact1 (cdr n) (mult n a))
    a))

(defthm fact1-is-fact-generalized
  (implies (nump a)
           (equal (fact1 n a) (mult (fact n) a))))

(defthm nump-fact
  (nump (fact n)))

(defthm fact1-is-fact
  (equal (fact1 n '(nil)) (fact n)))
; --- The End ---

; Problem 9.2
; --- Script for proving mc-flatten ---

(defun mc-flatten (x a)
  (if (consp x)
      (mc-flatten (car x)
                  (mc-flatten (cdr x) a))
    (cons x a)))

(defthm mc-flatten-is-leaves-generalized
  (equal (mc-flatten x a) (app (leaves x) a)))

(defthm properp-leaves
  (properp (leaves x)))

(defthm mc-flatten-is-leaves
  (equal (mc-flatten x nil) (leaves x)))

; --- The End ---
