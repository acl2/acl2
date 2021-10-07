; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains examples of inductive theorems about loop$-recursive
; functions.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)
(include-book "std/testing/must-eval-to" :dir :system)

; The book projects/apply/definductor-tests.lisp contains many (pathological)
; loop$-recursive functions -- most of which return 0 -- and inductive proofs
; about them.  But there are two more interesting examples,

; (defthm copy-nat-tree-copies
;   (implies (warrant nat-treep copy-nat-tree)
;            (and (implies (nat-treep x) (equal (copy-nat-tree x) x))
;                 (implies (and (true-listp x)
;                               (loop$ for e in x always (nat-treep e)))
;                          (equal (loop$ for e in x collect (copy-nat-tree e))
;                                 x))))
;   :rule-classes nil)

; (defthm pstermp-is-pseudo-termp
;    (implies (warrant pstermp)
;             (and (equal (pstermp x) (pseudo-termp x))
;                  (equal (and (true-listp x)
;                              (loop$ for e in x always (pstermp e)))
;                         (pseudo-term-listp x))))
;    :rule-classes nil)

; where an example nat-treep is

; (nat-treep '(NATS
;              (NATS 1 2 3)
;              4
;              (NATS 5 (NATS 6 7 8) 9)))

; and pstermp is just a loop$-recursive version of pseudo-termp.

; In this file we focus on functions and their properties like those above,
; i.e., that are in some sense realistic applications of loop$ recursion and
; induction.

; -----------------------------------------------------------------
; An unusual way to compute (expt 2 (- n 1))

(defun$ 2^n-1 (n)
  (declare (xargs :guard (natp n)
                  :loop$-recursion t
                  :verify-guards nil
                  :measure (acl2-count n)))
  (if (zp n)
      1
      (loop$ for i of-type (satisfies natp)
             from 0 to (- n 1)
             sum (2^n-1 i))))

(must-eval-to (value (time$ (2^n-1 20)))
              (expt 2 19)
              :with-output-off nil)
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 2.44 seconds realtime, 2.44 seconds runtime
; (335,544,928 bytes allocated).

(verify-guards 2^n-1)

(must-eval-to (value (time$ (2^n-1 20)))
              (expt 2 19)
              :with-output-off nil)
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 0.01 seconds realtime, 0.01 seconds runtime
; (16 bytes allocated).

(defthm 2^n-1-loop-lemma
  (implies (and (warrant 2^n-1)
                (integerp n)
                (<= 0 n))
           (equal (loop$ for i from 0 to n sum (2^n-1 i))
                  (expt 2 n))))

(defthm 2^n-1-is-expt-2-n-1
  (implies (and (warrant 2^n-1)
                (integerp n)
                (< 0 n))
           (equal (2^n-1 n)
                  (expt 2 (- n 1)))))

; -----------------------------------------------------------------
; Terms and Substitutions

(defun$ pstermp (x)

; TODO 1:
; This is the ACL2 built-in pseudo-termp, expressed with loop$, EXCEPT that I
; have swapped the indicated terms below so that the inductor is not tested.
; This is not crucial to the proof of the pstermp-pssubst theorem below, but
; testing the inductor is a very strange thing to do.

  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cdr (cdr x)))))
        ((not (true-listp x)) nil)
        ((loop$ for e in (cdr x) always (pstermp e))
         (or (symbolp (car x))
             (and (true-listp (car x))
                  (equal (length (car x)) 3)
                  (eq (car (car x)) 'lambda)
                  (symbol-listp (cadr (car x)))
                  (equal (length (cadr (car x))) ; <--- swapped with
                         (length (cdr x)))
                  (pstermp (caddr (car x))))))   ; <--- this
        (t nil)))

(definductor pstermp)

(defun$ pssubst (new old term)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count term)))
  (cond
   ((variablep term)
    (if (eq term old) new term))
   ((fquotep term)
    term)
   (t (cons (ffn-symb term)
            (loop$ for e in (fargs term)             ; had to use same iterative var everywhere!
                   collect (pssubst new old e))))))

(definductor pssubst)

; Now we embark on proving that pssubst produces a pstermp.  We try several
; different statements of the second conjunct to explore the issue of
; whether we should write
; [1]
; (loop$ for e in (loop$ for e in term collect (pssubst new old e))
;        always (pstermp e))
; or
; [2]
; (loop$ for e in term always (pstermp (pssubst new old e)))

; We don't want it stored as a rule so that successive proofs don't
; influence eachother.

(defthm pstermp-pssubst-[1]
  (implies (warrant pstermp pssubst)
           (and (implies (and (pstermp new)
                              (variablep old)
                              (pstermp term))
                         (pstermp (pssubst new old term)))
                (implies (and (pstermp new)
                              (variablep old)
                              (loop$ for e in term always (pstermp e)))
                         (loop$ for e in (loop$ for e in term collect (pssubst new old e))
                                always (pstermp e)))))
  :rule-classes nil)
; Time:  32.30 seconds (prove: 32.25, print: 0.05, other: 0.00)

(defthm pstermp-pssubst-[2]
  (implies (warrant pstermp pssubst)
           (and (implies (and (pstermp new)
                              (variablep old)
                              (pstermp term))
                         (pstermp (pssubst new old term)))
                (implies (and (pstermp new)
                              (variablep old)
                              (loop$ for e in term always (pstermp e)))
                         (loop$ for e in term
                                always (pstermp (pssubst new old e))))))
  :rule-classes nil)
; Time:  28.71 seconds (prove: 28.67, print: 0.05, other: 0.00)

(defthm pstermp-pssubst-[1]-without-compose-rules
  (implies (warrant pstermp pssubst)
           (and (implies (and (pstermp new)
                              (variablep old)
                              (pstermp term))
                         (pstermp (pssubst new old term)))
                (implies (and (pstermp new)
                              (variablep old)
                              (loop$ for e in term always (pstermp e)))
                         (loop$ for e in (loop$ for e in term collect (pssubst new old e))
                                always (pstermp e)))))
  :hints (("Goal" :in-theory (disable compose-always-collect)))
  :rule-classes nil)
; Time:  11.81 seconds (prove: 11.77, print: 0.04, other: 0.01)

; This next one fails after over an hour, with over 574 pushed subgoals.

; (defthm pstermp-pssubst-[2]-without-compose-rules
;   (implies (warrant pstermp pssubst)
;            (and (implies (and (pstermp new)
;                               (variablep old)
;                               (pstermp term))
;                          (pstermp (pssubst new old term)))
;                 (implies (and (pstermp new)
;                               (variablep old)
;                               (loop$ for e in term always (pstermp e)))
;                          (loop$ for e in term
;                                 always (pstermp (pssubst new old e))))))
;   :hints (("Goal" :in-theory (disable compose-always-collect)))
;   :rule-classes nil)

; So the take-home is this, I think: If the conclusion of the theorem you're
; proving is of the form (p (f x)), where f builds a data structure with a
; COLLECT loop$ and p checks it with an ALWAYS loop$, it is probably fastest to
; state the second conjunct in style [1], i.e., an ALWAYS loop$ over a COLLECT
; loop$ target, and to disable the compose-always-collect rule.

; If the functions or theorems are not clearly of that form, it is probably
; best to state the second conjunct in style [2], i.e., an ALWAYS loop$
; checking the property over whatever the appropriate target is and to enable
; the compose-always-collect rule.

(defun$ psoccur (term1 term2)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count term2)))
  (cond
   ((equal term1 term2) t)
   ((variablep term2) nil)
   ((fquotep term2) nil)
   (t (loop$ for e in (fargs term2) thereis (psoccur term1 e)))))

(defthm psoccur-pssubst
  (implies (warrant psoccur pssubst)
           (and (implies (and (variablep var)
                              (psoccur var (pssubst new var term)))
                         (psoccur var new))
                (implies (and (variablep var)
                              (loop$ for e in term thereis (psoccur var (pssubst new var e))))
                         (psoccur var new))))
  :rule-classes nil)
