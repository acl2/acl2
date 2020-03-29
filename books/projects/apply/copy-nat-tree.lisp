; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; A Brief Tutorial on Loop$ Recursion Induction
; J Strother Moore
; March, 2020

; Abstract: This book contains inductive theorems about a rather silly but
; instructive loop$-recursive function.  We introduce a data structure called a
; ``nat tree,'' an example of which is (NATS (NATS 1 2 3) 4 (NATS 5 6)), and a
; function that copies such a tree, and we prove that the copy function indeed
; copies.  We illustrate some of the principles mentioned in :doc
; loop$-recursion-induction.  We also relate the loop$-recursive copy function
; to its mutually-recursive version and to a flagged function capturing that
; mutual recursion.

; Since ACL2 does not automatically compute appropriate induction schemes for
; loop$-recursive functions, we have to provide an explicit :induction hint.
; We regard this burden (which we would normally consider a burden) as salutary
; here because it clearly shows what has to be done for this particular
; loop$-recursive function.  This should enable the reader to either use this
; same methodology in his or her own proofs about loop$-recursive functions or
; to automate the methodology with some helpful book.  However, we are working
; on such a book ourselves and this file illustrates the direction of our
; thinking.

; All theorems proved in this book have rule-classes nil so we can be confident
; that proofs are not dependent on proving one theorem before another.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)
(include-book "misc/eval" :dir :system)

; -----------------------------------------------------------------
; Definitions

; Here is the definition of nat-treep, two examples illustrating the predicate,
; and the function that copies nat trees.  Both functions use loop$ recursion.
; The copy function, copy-nat-tree, is unnecessarily complicated because it
; copies the natural numbers in it.  That is, it reconstructs each natural by
; adding 1 to the result of copying the non-0 predecessor natural.  We do this
; to illustrate recursion and induction both inside and outside the loop$.

(defun$ nat-treep (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((atom x) (natp x))
   (t (and (true-listp x)
           (eq (car x) 'NATS)
           (loop$ for e in (cdr x) always (nat-treep e))))))

(defthm examples-of-nat-treep
  (implies
   (warrant nat-treep)
   (and (equal (nat-treep '(nats
                            (nats 1 2 3)
                            4
                            (nats 5 (nats 6 7 8) 9))) t)
        (equal (nat-treep '(nats (nats 1 2 3) bad)) nil)))
  :rule-classes nil)

(defun$ copy-nat-tree (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((atom x)
    (if (natp x)
        (if (equal x 0)
            0
            (+ 1 (copy-nat-tree (- x 1))))
        x))
   (t (cons 'nats
            (loop$ for e in (cdr x) collect (copy-nat-tree e))))))

; -----------------------------------------------------------------
; Failures Illustrating General Principles and the Induction Hint

; We now illustrate the general principles mentioned in :doc
; loop$-recursion-induction.

; The following will fail for many reasons.  But the reason we want to
; highlight is the absence of the warrants for nat-treep and copy-nat-tree!

(must-fail
 (defthm failure-0 ; no warrants!
   (implies (nat-treep x)
            (equal (copy-nat-tree x) x))))

; We now provide the necessary warrants, but loop$-recursive functions do not
; automatically suggest induction schemes, so this will fail.

(must-fail
 (defthm failure-1 ; no induction is suggested by loop$-recursion
   (implies (and (warrant nat-treep copy-nat-tree)
                 (nat-treep x))
            (equal (copy-nat-tree x) x))))

; An induction scheme appropriate for copy-nat-tree contains a ``(- x 1)''
; induction hyp for naturals, and a car/cdr induction hyp for conses.  The
; car/cdr induction hyp is necessary because as

; (loop$ for e in x collect (copy-nat-tree e))

; expands it introduces a recursive call of copy-nat-tree on (car x) and
; ``recursive call of the loop$'' on (cdr x).

(defun induction-hint (x)
  (cond ((atom x)
         (if (natp x)
             (if (equal x 0)
                 'base
                 (induction-hint (- x 1)))
             'base))
        (t
         (cons (induction-hint (car x))
               (induction-hint (cdr x))))))

; So now we offer the induction hint to the previously failing proof attempt.
; It still fails because the formula to be proved does not tell us,
; inductively, what (loop$ ... collect (copy-nat-tree ...)) does.

(must-fail
 (defthm failure-2 ; insufficiently strong
   (implies (and (warrant nat-treep copy-nat-tree)
                 (nat-treep x))
            (equal (copy-nat-tree x) x))
   :hints (("Goal" :induct (induction-hint x)))))

; We attempt to fix that by conjoining another conjecture, this one about the
; the loop$ statement inside the definition of copy-nat-tree.  One positive
; contribution of this example is that it first illustrates the use of an
; loop$/always to require that every element of (cdr x) is a nat-treep.

; (loop$ for e in (cdr x) always (nat-treep e))

; Generally speaking, when stating a theorem about the behavior of a loop$
; in a loop$-recursive function you have to constrain the target appropriately
; for the function to behave as specified.  Put another way, as we think about
; the ``loop$ version'' of (implies (nat-treep x) (equal (copy-nat-tree x) x))
; we need to think about the loop$ both the hypthesis and the conclusion, i.e.,
; in nat-treep and in copy-nat-tree.

; Despite this thinking, the following proof attempt fails too.  We need a
; GENERAL statement about what the loop$ does on an arbitrary target, not just
; on (cdr x)!

(must-fail
 (defthm failure-3 ; insufficiently strong
   (implies (warrant nat-treep copy-nat-tree)
            (and (implies (nat-treep x) (equal (copy-nat-tree x) x))
                 (implies (and (true-listp x)
                               (loop$ for e in (cdr x) always (nat-treep e)))
                          (equal (loop$ for e in (cdr x) collect (copy-nat-tree e))
                                 (cdr x)))))
   :hints (("Goal" :induct (induction-hint x)))
   :rule-classes nil))

; -----------------------------------------------------------------
; A Provable Form of the Desired Theorem

; Finally, this conjunction succeeds.  It is a conjunction of our original
; conjecture together with its loop$ version, it comes with the warrants we
; need, the loop$ versions are phrased about a variable target, x, not just the
; target used in the main function, and we provide an induction hint that
; catches both (- x 1) recursion and car/cdr recursion.

(defthm finally-success!
  (implies (warrant nat-treep copy-nat-tree)
           (and (implies (nat-treep x) (equal (copy-nat-tree x) x))
                (implies (and (true-listp x)
                              (loop$ for e in x always (nat-treep e)))
                         (equal (loop$ for e in x collect (copy-nat-tree e))
                                x))))
  :hints (("Goal" :induct (induction-hint x)))
  :rule-classes nil)

; -----------------------------------------------------------------
; Comparing Loop$-Recursion to the Corresponding Mutually-Recursive Definition

; Next we turn to comparing the loop$-recursive function copy-nat-tree to its
; mutual-recursion version.

(mutual-recursion
 (defun mr-copy-nat-tree (x)
   (cond
    ((atom x)
     (if (natp x)
         (if (equal x 0)
             0
             (+ 1 (mr-copy-nat-tree (- x 1))))
         x))
    (t (cons 'nats
             (mr-copy-nat-tree-list (cdr x))))))

 (defun mr-copy-nat-tree-list (x)
   (cond
    ((endp x) nil)
    (t (cons (mr-copy-nat-tree (car x))
             (mr-copy-nat-tree-list (cdr x)))))))

; The following proof may come as a surprise to some ACL2 users.  It shows that
; the induction hint that is appropriate for copy-nat-tree -- an induction that
; uses both (- x 1) recursion and car/cdr recursion -- can be used successfully
; on a conjunction of theorems about a mutually recursive function.

(defthm mr-copy-nat-tree-copies
  (implies (warrant nat-treep)
           (and (implies (nat-treep x)
                         (equal (mr-copy-nat-tree x) x))
                (implies (and (true-listp x)
                              (loop$ for e in x always (nat-treep e)))
                         (equal (mr-copy-nat-tree-list x) x))))
  :hints (("Goal" :induct (induction-hint x)))
  :rule-classes nil)

; Note also that the theorem above uses the loop$-recursive function nat-treep
; to constrain the input to the mutually recursive functions.  Thus, we need
; the warrant for nat-treep.

; In a similiar vein, we can prove that the loop$-recursive function is
; equivalent to its mutually recursive counterpart.

(defthm copy-nat-tree-is-mr-copy-nat-tree
  (implies (warrant nat-treep copy-nat-tree)
           (and (implies (nat-treep x)
                         (equal (copy-nat-tree x)
                                (mr-copy-nat-tree x)))
                (implies (and (true-listp x)
                              (loop$ for e in x always (nat-treep e)))
                         (equal (loop$ for e in x collect (copy-nat-tree e))
                                (mr-copy-nat-tree-list x)))))
  :hints (("Goal" :induct (induction-hint x)))
  :rule-classes nil)

; -----------------------------------------------------------------
; Eliminating Loop$-Recursion in Favor of Flagged Mutual Recursion

; Finally, another way to approach proofs about loop$-recursive functions is to
; introduce the ``flagged mutually recursive'' version and prove equivalence.
; We hope this approach isn't used regularly because it requires defining yet
; another function and the beauty of loop$ recursion is that it avoids defining
; helper functions.  However, as a last resort, you can reduce the
; loop$-recursive function to a flagged mutually recursive function and then
; use conventional methods to prove properties.

; In the following flagged version, flg=t means x is treated as a nat-treep and
; flg=nil means it is treated as a list of nat-treeps.

(defun flagged-mr-copy-nat-tree (flg x)
  (if flg
      (cond
       ((atom x)
        (if (natp x)
            (if (equal x 0)
                0
                (+ 1 (flagged-mr-copy-nat-tree t (- x 1))))
            x))
       (t (cons 'nats
                (flagged-mr-copy-nat-tree nil (cdr x)))))
      (cond
       ((endp x) nil)
       (t (cons (flagged-mr-copy-nat-tree t (car x))
                (flagged-mr-copy-nat-tree nil (cdr x)))))))

; Then we can prove that the flagged function is either copy-nat-tree or its
; loop$ counterpart, depending on the flag.  No induction hint is necessary
; because the term (flagged-mr-copy-nat-tree flg x) suggests the right
; induction.  We still need the warrant for copy-nat-tree.

(defthm flagged-equivalence
  (implies (warrant copy-nat-tree)
           (equal (flagged-mr-copy-nat-tree flg x)
                  (if flg
                      (copy-nat-tree x)
                      (loop$ for e in x collect (copy-nat-tree e)))))
  :rule-classes nil)

; The following trivial corollary, if proved as a :rewrite rule, will
; eliminate the loop$ recursion in favor of flagged mutual recursion.

(defthm eliminate-copy-nat-tree
  (implies (warrant copy-nat-tree)
           (and (equal (copy-nat-tree x) (flagged-mr-copy-nat-tree t x))
                (equal (loop$ for e in x collect (copy-nat-tree e))
                       (flagged-mr-copy-nat-tree nil x))))
  :hints (("Goal" :use ((:instance flagged-equivalence (flg t))
                        (:instance flagged-equivalence (flg nil)))))
  :rule-classes nil)

