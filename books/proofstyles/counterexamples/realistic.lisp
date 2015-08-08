(in-package "ACL2")

#|

 realistic.lisp
 ~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Sun Dec  9 00:27:02 2007

This book demonstrates why the Manolios/Moore 2003 notion might not be
an adequate notion of partial correctness.  Here we consider a machine
that operates as follows.  It executes the instructions in a program,
and when it is done it resets memory and program and halts.  With this
machine we show that any arbitrary program of length 10 satisfies
Manolios/Moore's partial correctness condition, where as postcondition
I chose that the machine computes factorial.

The machine is of course a toy and not realistic at all.  But the
machine can be extended to a realistic one by keeping the basic idea.
The basic idea is that the machine computes the program instructions,
but at the time of *finally* halting, it clears off everything before
halting.  It is not important that everything is cleared, actually:
the program-specific details need to be cleared before halting.  At
any exit state before halting, there are non-trivial partial (and
total) correctness theorems that one can imagine proving on such a
machine.  But if the only thing we want to do is say that an initial
state and a modified state (according to postcondition) reach the same
halting state (as is required by Manolios/Moore notion), then we can
prove *each* program partially correct with respect to that machine.

|#

(include-book "misc/records" :dir :system)
(include-book "misc/defpun" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Machine definition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro ctr (s) `(g :pc ,s))
(defmacro memory (s) `(g :mem ,s))
(defmacro program-of (s) `(g :program ,s))

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))

(defmacro >s (&rest upds) `(update s ,@upds))

;; I leave the execute-op function below undefined since its semantics
;; does not matter.

(defstub execute-op (* *) => *)

;; Here of course the only thing that the language allows is
;; incrementing the pc by 1, so the language is assumed to have no
;; conditional or loops or anything.  So every program terminates.

(defun next (s)
  (let ((pc (ctr s))
        (program (program-of s)))
    (if (consp program)
        (if (<= pc (len program))
            (>s :mem (execute-op (nth pc program) s)
                :pc (1+ pc))
          (>s :pc 0
              :mem nil
              :program nil))
      s)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Manolios/Moore's notion of partial correctness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun halted-statep (s) (equal (next s) s))

(defpun stepw (s)
  (if (halted-statep s) s
    (stepw (next s))))

(defun == (x y)
  (equal (stepw x) (stepw y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: A program and its specification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here we specify an arbitrary program of length 10.

(encapsulate
 (((arbitrary-program) => *))

 (local (defun arbitrary-program () (list 1 2 3 4 5 6 7 8 9 10)))

 (defthm |arbitrary program is non-empty|
   (equal (len (arbitrary-program)) 10)))

;; Now we specify the precondition and the modify condition as per
;; Manolios/Moore's notion.  The goal is to prove that for each state
;; s satisfying pre, s == (modify-factorial s).  Given the
;; precondition and the modify, this is the partial correctness of
;; factorial for the Manolios/Moore's notion.  But we prove this
;; notion for any arbitrary program of length 10.  (The choice of
;; length 10 is just so that I don't have to do an induction as
;; necessary for arbitrary length in this demonstration.)

(defun pre (s)
  (and (equal (ctr s) 0)
       (natp (nth 1 (memory s)))
       (equal (program-of s) (arbitrary-program))))

(defun ! (n)
  (if (zp n) 1
    (* n (! (1- n)))))

(defun modify-factorial (s)
  (>s :pc 10
      :mem (update-nth 3 (! (nth 1 (memory s))) (memory s))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Intermediate lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun run (s n)
   (if (zp n) s
     (run (next s) (1- n)))))

(local
 (defthm run-expansion
   (equal (run s n)
          (if (zp n) s
            (run (next s) (1- n))))))

(local
 (defthm arbitrary-program-is-consp
   (consp (arbitrary-program))
   :rule-classes :type-prescription
   :hints (("Goal"
            :in-theory (disable |arbitrary program is non-empty|)
            :use |arbitrary program is non-empty|))))

(local
 (defthm memory-cleared-after-some-time
   (implies (pre s)
            (equal (run s 12)
                   (>s :pc 0
                       :mem nil
                       :program nil)))))

(local
 (defthm memory-cleared-after-modify
   (implies (pre s)
            (equal (run (modify-factorial s) 3)
                   (>s :pc 0
                       :mem nil
                       :program nil)))))

(local
 (defthm clear-is-halted
   (halted-statep (>s :pc 0
                      :mem nil
                      :program nil))))

(local (in-theory (disable run-expansion)))

(local
 (defthm halted-to-stepw
   (implies (halted-statep s)
            (equal (stepw s) s))))

(local
 (defthmd run-s-stepw
   (implies (halted-statep (run s n))
            (equal (stepw (run s n))
                   (stepw s)))))

(local (in-theory (disable stepw-def)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: Intermediate lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here is the final theorem that shows that Manolios/Moore's notion
;; of partial correctness is satisfied by the program.

(defthm |arbitrary program is partially correct|
  (implies (pre s)
           (== s (modify-factorial s)))
  :hints (("Goal"
           :in-theory (disable pre run modify-factorial)
           :use ((:instance run-s-stepw
                            (n 12))
                 (:instance run-s-stepw
                            (n 3)
                            (s (modify-factorial s)))))))