(in-package "ACL2")

; Here we take a slightly different approach to the key problem, that
; of proving that (alpha) and (beta) are permutations.  This
; presentation is slightly out of order because the person who
; provided it wanted to get right to the heart of the problem.

(include-book "perm")

;;; Events copied from mergesort.lisp:

(defun split-list (x)
  (cond ((atom x) (mv nil nil))
	((atom (cdr x)) (mv x nil))
	(t (mv-let (a b)
		   (split-list (cddr x))
		   (mv (cons (car x) a) (cons (cadr x) b))))))

(defun merge2 (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((atom x) y)
	((atom y) x)
	((< (car x) (car y))
	 (cons (car x) (merge2 (cdr x) y)))
	(t (cons (car y) (merge2 x (cdr y))))))

(defthm split-list-smaller
  (implies (and (consp x) (consp (cdr x)))
           (and (< (acl2-count (car (split-list x)))
                   (acl2-count x))
                ;; Originally we used (cadr ..) instead of (mv-nth 1 ..) below,
                ;; but the mv-nth didn't open up to cadr in the termination
                ;; proof of mergesort, so we are going with mv-nth below.
                (< (acl2-count (mv-nth 1 (split-list x)))
                   (acl2-count x)))))

(defun mergesort (x)
  (cond ((atom x) nil)
	((atom (cdr x)) x)
	(t (mv-let (a b)
		   (split-list x)
		   (merge2 (mergesort a) (mergesort b))))))

;;; End of events copied from mergesort.lisp:

; ---------------------------------------------------------------------------
; Exercise 11.47

(defun how-many (e x)
  (cond
   ((endp x)
    0)
   ((equal e (car x))
    (1+ (how-many e (cdr x))))
   (t
    (how-many e (cdr x)))))

; ---------------------------------------------------------------------------
; Exercise 11.50

(encapsulate
 ((alpha () t)
  (beta  () t))

 (local (defun alpha () nil))

 (local (defun beta () nil))

 (defthm how-many-is-same-for-a-and-b
   (equal (how-many e (alpha))
          (how-many e (beta))))
 )

;;; Start of proof of perm-a-b.

; Our approach will be to try to find a counterexample cntrex to (perm
; x y) as a function of lists x and y.  We will prove that this
; counterexample is an element that occurs a different number of times
; in x than in y.  Thus, if cntrex does occur the same number of times
; in x and in y, then x and y are permutations of each other.  We then
; will apply that result to x = (a) and y = (b).

; Thus, the following definition is modeled after the definition of perm.

(defun cntrex (x y)
  (cond ((atom x)
         (car y))
        ((not (in (car x) y))
         (car x))
        (t (cntrex (cdr x) (del (car x) y)))))

; When we try to prove cntrex-is-counterexample, we get the following as the
; first simplification checkpoint.

#|
Subgoal *1/3.2'
(IMPLIES (AND (CONSP X)
              (IN (CAR X) Y)
              (NOT (EQUAL (CNTREX (CDR X) (DEL (CAR X) Y))
                          (CAR X)))
              (NOT (PERM (CDR X) (DEL (CAR X) Y)))
              (NOT (EQUAL (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                                    Y)
                          (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                                    (DEL (CAR X) Y)))))
         (NOT (EQUAL (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                               (CDR X))
                     (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                               Y))))
|#

; The right-hand side of the equal term in the last hypothesis suggests the
; following rewrite rule.  (We return to this issue later.)

(defthm how-many-del
  (implies (not (equal a b))
           (equal (how-many a (del b x))
                  (how-many a x))))

; When we now try cntrex-is-counterexample, the first simplification checkpoint
; is as follows.

#|
Subgoal *1/2.5
(IMPLIES (AND (CONSP X)
              (NOT (IN (CAR X) Y))
              (NOT (PERM (CDR X) (DEL (CAR X) Y)))
              (NOT (EQUAL (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                                    (CDR X))
                          (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                                    (DEL (CAR X) Y)))))
         (NOT (EQUAL (+ 1 (HOW-MANY (CAR X) (CDR X)))
                     (HOW-MANY (CAR X) Y))))
|#

; The second hypothesis suggests a potential simplification of the del
; term in the last hypothesis, as indicated by the following lemma.
; Unfortunately, this lemma is not true except for true lists.  We will manage
; that problem later, but for now, we prove this lemma and then resume by
; proving a lemma cntrex-is-counterexample-for-true-lists, shown below.

(defthm not-in-implies-del-is-no-op
  (implies (and (not (in a x))
                (true-listp x))
           (equal (del a x) x)))

; The first simplification checkpoint for the proof of
; cntrex-is-counterexample-for-true-lists is:

#|
Subgoal *1/3.2
(IMPLIES (AND (CONSP X)
              (IN (CAR X) Y)
              (NOT (EQUAL (CNTREX (CDR X) (DEL (CAR X) Y))
                          (CAR X)))
              (NOT (TRUE-LISTP (DEL (CAR X) Y)))
              (TRUE-LISTP (CDR X))
              (TRUE-LISTP Y)
              (NOT (PERM (CDR X) (DEL (CAR X) Y))))
         (NOT (EQUAL (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                               (CDR X))
                     (HOW-MANY (CNTREX (CDR X) (DEL (CAR X) Y))
                               Y))))
|#

; The fourth hypothesis above suggests the following lemma.  Since it is about
; true-listp, we make it a :type-prescription rule.

(defthm true-listp-del
  (implies (true-listp x)
           (true-listp (del a x)))
  :rule-classes :type-prescription)

; Lemma cntrex-is-counterexample-for-true-lists now yields the following as the
; first simplification checkpoint.

#|
Subgoal *1/2.5'
(IMPLIES (AND (CONSP X)
              (NOT (IN (CAR X) Y))
              (NOT (PERM (CDR X) Y))
              (NOT (EQUAL (HOW-MANY (CNTREX (CDR X) Y) (CDR X))
                          (HOW-MANY (CNTREX (CDR X) Y) Y)))
              (TRUE-LISTP (CDR X))
              (TRUE-LISTP Y))
         (NOT (EQUAL (+ 1 (HOW-MANY (CAR X) (CDR X)))
                     (HOW-MANY (CAR X) Y))))
|#

; The second hypothesis, (NOT (IN (CAR X) Y)), should cause the last how-many
; term above to simplify to 0.  The following lemma does this.

(defthm not-in-implies-how-many-is-0
  (implies (not (in a x))
           (equal (how-many a x)
                  0)))

; The first simplification checkpoint for
; cntrex-is-counterexample-for-true-lists is now as follows.

#|
Subgoal *1/2.2'
(IMPLIES (AND (CONSP X)
              (EQUAL (CNTREX (CDR X) (DEL (CAR X) Y))
                     (CAR X))
              (NOT (PERM (CDR X) (DEL (CAR X) Y)))
              (NOT (EQUAL (HOW-MANY (CAR X) (CDR X))
                          (HOW-MANY (CAR X) (DEL (CAR X) Y))))
              (TRUE-LISTP (CDR X))
              (TRUE-LISTP Y))
         (NOT (EQUAL (+ 1 (HOW-MANY (CAR X) (CDR X)))
                     (HOW-MANY (CAR X) Y))))
|#

; Perhaps we can make progress by simplifying the last how-many term in the
; hypothesis.  Let us prove a more general rule than the previous
; rule how-many-del.

(defthm how-many-del-general
  (equal (how-many a (del b x))
         (if (and (equal a b) (in a x))
             (1- (how-many a x))
           (how-many a x))))

(defthm cntrex-is-counterexample-for-true-lists
  (implies (and (true-listp x)
                (true-listp y))
           (iff (perm x y)
                (equal (how-many (cntrex x y) x)
                       (how-many (cntrex x y) y))))
  :rule-classes nil)

; It remains to prove cntrex-is-counterexample from the lemma above.  We define
; the following function to coerce a list to a true list, and things fall into
; place.

(defun tlfix (x)
  (if (endp x)
      nil
    (cons (car x) (tlfix (cdr x)))))

(defthm perm-tlfix
  (perm (tlfix x) x))

(defthm cntrex-tlfix-1
  (equal (cntrex (tlfix x) y)
         (cntrex x y)))

; The first simplification checkpoint for cntrex-tlfix-2 suggests the following
; lemma.

(defthm del-tlfix
  (equal (del a (tlfix x))
         (tlfix (del a x))))

; The first simplification checkpoint for cntrex-tlfix-2 at this point now
; suggests the following lemma.

(defthm in-tlfix
  (equal (in a (tlfix x))
         (in a x)))

(defthm cntrex-tlfix-2
  (equal (cntrex x (tlfix y))
         (cntrex x y)))

; Finally, we will need this in order for the :use hint below to work.

(defthm how-many-tlfix
  (equal (how-many a (tlfix x))
         (how-many a x)))

(defthm cntrex-is-counterexample
  (iff (perm x y)
       (equal (how-many (cntrex x y) x)
              (how-many (cntrex x y) y)))
  :hints (("Goal" :use
           ((:instance cntrex-is-counterexample-for-true-lists
                       (x (tlfix x))
                       (y (tlfix y)))))))

; So here is the conclusion of Exercise 11.50.

(defthm perm-alpha-beta
  (perm (alpha) (beta)))

; ---------------------------------------------------------------------------
; Exercise 11.48

;;; Now we prove the how-many result for mergesort.

; We start with corresponding lemmas that we fully expect to need for merge2.
; We expect to need one for split-list as well, but we wait on that since we
; are not sure what syntactic form of such a lemma will be appropriate.

(defthm how-many-merge2
  (equal (how-many a (merge2 x y))
         (+ (how-many a x) (how-many a y))))

; The first simplification checkpoint for how-many-mergesort is as follows.

#|
Subgoal *1/3.2''
(IMPLIES (AND (CONSP X)
              (CONSP (CDR X))
              (EQUAL (HOW-MANY (CAR X)
                               (MERGESORT (CAR (SPLIT-LIST X))))
                     (HOW-MANY (CAR X) (CAR (SPLIT-LIST X))))
              (EQUAL (HOW-MANY (CAR X)
                               (MERGESORT (MV-NTH 1 (SPLIT-LIST X))))
                     (HOW-MANY (CAR X)
                               (MV-NTH 1 (SPLIT-LIST X)))))
         (EQUAL (+ (HOW-MANY (CAR X) (CAR (SPLIT-LIST X)))
                   (HOW-MANY (CAR X)
                             (MV-NTH 1 (SPLIT-LIST X))))
                (+ 1 (HOW-MANY (CAR X) (CDR X)))))
|#

; The left-hand side of the equality in the conclusion above suggests an
; appropriate form for the result we expected to need about split-list.

(defthm how-many-split-list
  (equal (+ (how-many a (car (split-list x)))
            (how-many a (mv-nth 1 (split-list x))))
         (how-many a x)))

(defthm how-many-mergesort
  (equal (how-many a (mergesort x))
         (how-many a x)))

; ---------------------------------------------------------------------------
; Exercise 11.49 - this discussion is identical to that in
; how-many-soln1.lisp.

; We hope you didn't waste too much time on this problem!

; As noted in the errata:

; On page 220, Exercise 11.49 is simply wrong.  The formula alleged not
; to be a theorem is a theorem, so no counterexample is possible!  What
; we had in mind has nothing to do with mergesort but instead is an
; observation about perm, how-many, and quantification.  The exercise
; should have been:

;  Exercise 11.49  The following is a theorem in a suitable logic
;  permitting ACL2 terms and first-order quantification.

;    (perm a b)
;  <->
;    (ALL e (equal (how-many e a)
;                  (how-many e b)))

; Here, by ALL we mean the universal quantifier.  The universal
; quantifier in the above theorem is important.  The similar looking
; ACL2 formula

; (iff (perm a b)
;      (equal (how-many e a)
;             (how-many e b)))

; is not a theorem.  Exhibit a counterexample.

; Here is our solution to THAT problem!

(defthm counterexample-49
  (equal
   (let ((a '(1 2))
         (b '(1 3))
         (e 1))
     (iff (perm a b)
          (equal (how-many e a)
                 (how-many e b))))
   nil)
  :rule-classes nil)

; Note that to make this command a suitable event for a book, we had to
; phrase it as a theorem.  Our theorem is just that a certain instance
; of the formula evaluates to nil.

; ---------------------------------------------------------------------------
; Exercise 11.51

; And now, the result we have been shooting for.

(defthm perm-mergesort
  (perm (mergesort x) x))

; The theorem above is proved by using cntrex-is-counterexample to
; rewrite the perm, above, into

; (equal (how-many (cntrex (mergesort x) x)
;                  (mergesort x))
;        (how-many (cntrex (mergesort x) x)
;                  x))

; and then rewriting that to t with how-many-mergesort.

