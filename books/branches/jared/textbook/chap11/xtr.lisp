(in-package "ACL2")

; This is a surprising tricky little problem.  We do it two ways.  See
; xtr2.lisp for the other way.

; ---------------------------------------------------------------------------
; Exercise 11.52

(defun nats (n)
  (if (zp n)
      nil
    (cons (- n 1) (nats (- n 1)))))

(defun xtr (map lst)
  (if (endp map)
      nil
    (cons (nth (car map) lst)
          (xtr (cdr map) lst))))

; Here is the definition of rev (along its supporting function, app) from the
; book.

(defun app (x y)
  (if (endp x)
      y
    (cons (car x)
          (app (cdr x) y))))

(defun rev (x)
  (if (endp x)
      nil
    (app (rev (cdr x)) (list (car x)))))

; The proof of xtr-nats-len fails with the following as the first
; simplification checkpoint.

#|
Subgoal *1/2''
(IMPLIES (AND (CONSP X)
              (EQUAL (XTR (NATS (LEN (CDR X))) (CDR X))
                     (REV (CDR X))))
         (EQUAL (XTR (NATS (+ 1 (LEN (CDR X)))) X)
                (APP (REV (CDR X)) (LIST (CAR X))))).
|#

; Somehow the second call of nats is not opening up, so we help the prover out
; by attempting to prove lemma nats-+1 below.  That proof fails, however,
; leading to the following simplification checkpoint.

#|
Subgoal *1/4''
(IMPLIES (AND (INTEGERP N)
              (< 0 N)
              (EQUAL (NATS (+ 1 -1 N))
                     (CONS (+ -1 N) (NATS (+ -1 N)))))
         (EQUAL (NATS (+ 1 N))
                (CONS N (NATS (+ 1 -1 N)))))
|#

; So we simply prove a lemma to simplify the term (+ 1 -1 N).  Perhaps we
; should include an arithmetic book instead.

(defthm one-minus-one
  (equal (+ 1 -1 n)
         (fix n)))

; The proof of nats-+1 still fails, even with the hint to expand (nats (+ 1
; n))!  We see the following simplification checkpoint:

#|
Subgoal *1/4''
(IMPLIES (AND (INTEGERP N) (< 0 N))
         (EQUAL (NATS (+ -1 1 N))
                (CONS (+ -1 N) (NATS (+ -1 N)))))
|#

; So we prove:

(defthm neg-1-plus-1
  (equal (+ -1 1 n)
         (fix n)))

; Now that we can prove nats-+1, we expect not to need it, so it is commented
; out:

#|
(defthm nats-+1
  (implies (and (integerp n)
                (not (< n 0)))
           (equal (nats (+ 1 n))
                  (cons n (nats n)))))
|#

; Our first simplification checkpoint for xtr-nats-len is now as follows.

#|
Subgoal *1/2''
(IMPLIES (AND (CONSP X)
              (EQUAL (XTR (NATS (LEN (CDR X))) (CDR X))
                     (REV (CDR X))))
         (EQUAL (CONS (NTH (LEN (CDR X)) X)
                      (XTR (NATS (LEN (CDR X))) X))
                (APP (REV (CDR X)) (LIST (CAR X)))))
|#

; The calls of xtr in the inductive hypothesis and the conclusion do not match:
; one has a second argument of (cdr x), the other, x.  This is a clue that we
; need to think at a high level about the proof.  We have a hunch that since
; nats counts down, it may be easier to reason about its application to (rev x)
; than to x.  We attempt to prove lemma xtr-nats-len-rev below, anticipating
; that we will ultimately instantiae x by (rev x) to obtain the desired result
; xtr-nats-len.  This leads to the following simplification checkpoint.

; NOTE:  This is not the only way to solve this problem!  An alternate
; approach, for example, is to define a version (rev2 n x) of reverse, where n
; is the number of elements to pull from x starting at the end, and prove an
; analogous result for rev2 instead, then deriving the desired result by a
; connecting rev2 and rev.

#|
Subgoal *1/3'''
(IMPLIES (AND (CONSP X)
              (EQUAL (XTR (NATS (LEN (CDR X))) (REV (CDR X)))
                     (CDR X)))
         (EQUAL (CONS (NTH (LEN (CDR X))
                           (APP (REV (CDR X)) (LIST (CAR X))))
                      (XTR (NATS (LEN (CDR X)))
                           (APP (REV (CDR X)) (LIST (CAR X)))))
                X))
|#

; The end is now in sight.  Each of the two arguments to cons above suggests a
; rewrite rule, although in order for ACL2 to apply these rules we will need to
; teach it the following fact.

(defthm len-rev
  (equal (len (rev x))
         (len x)))

; The first rewrite rule is the second one below, which we derive as a
; corollary of the first since the second does not succeed (ACL2 cannot
; construct an appropriate induction scheme for it).

(defthm nth-len-app-lemma
  (equal (nth (len x) (app x y))
         (car y)))

(defthm nth-len-app
  (implies (equal len (len x))
           (equal (nth len (app x y))
                  (car y))))

; The second lemma we need is xtr-nats-app below.  An attempt to prove it
; leads to the following.

#|
Subgoal *1/3''
(IMPLIES (AND (INTEGERP N)
              (< 0 N)
              (EQUAL (XTR (NATS (+ -1 N)) (APP X Y))
                     (XTR (NATS (+ -1 N)) X))
              (<= N (LEN X)))
         (EQUAL (NTH (+ -1 N) (APP X Y))
                (NTH (+ -1 N) X)))
|#

; So, we prove:

(defthm nth-app
  (implies (and (integerp n)
                (<= 0 n)
                (< n (len x)))
           (equal (nth n (app x y))
                  (nth n x))))

(defthm xtr-nats-app
  (implies (<= n (len x))
           (equal (xtr (nats n) (app x y))
                  (xtr (nats n) x))))

(defthm xtr-nats-len-rev
  (implies (true-listp x)
           (equal (xtr (nats (len x)) (rev x))
                  x))
  ;; We will be using this explicitly:
  :rule-classes nil)

(defthm rev-rev
  (implies (true-listp x)
           (equal (rev (rev x)) x)))

; The attempt to prove xtr-nats-len leads to the following simplification
; checkpoint:

#|
Subgoal 2
(TRUE-LISTP (REV X))
|#

(defthm true-listp-rev
  (true-listp (rev x))
  ;; This is an ideal type-prescription rule.
  :rule-classes :type-prescription)

; The proof of xtr-nats-len still fails, but now we have:

#|
Goal'''
(IMPLIES (EQUAL (XTR (NATS (LEN X)) (REV (REV X)))
                (REV X))
         (EQUAL (XTR (NATS (LEN X)) X) (REV X)))
|#

; Let us write a simple function corresponding to (rev (rev x)).  We will prove
; what we need to about it.  "Tlfix" stands for "true-listp fix."

(defun tlfix (x)
  (if (endp x)
      nil
    (cons (car x) (tlfix (cdr x)))))

(defthm rev-rev-again
  (equal (rev (rev x))
         (tlfix x)))

; Inspection of the goal above suggests that we need the lemma xtr-tlfix below.
; In order to prove it, we will surely need the following lemma, since xtr
; calls nth.

(defthm nth-tlfix
  (equal (nth n (tlfix x))
         (nth n x)))

(defthm xtr-tlfix
  (equal (xtr map (tlfix x))
         (xtr map x)))

; And now finally:

(defthm xtr-nats-len
  (equal (xtr (nats (len x)) x) (rev x))
  :hints (("Goal" :use
           ((:instance xtr-nats-len-rev
                       (x (rev x)))))))

