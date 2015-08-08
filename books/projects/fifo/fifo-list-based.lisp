; A List-based FIFO queue
; Copyright (C) 2015, Oracle and/or its affiliates. All rights reserved.
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: David L. Rager <david.rager@oracle.com>

; THIS IS A WORK IN PROGRESS

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/top" :dir :system)

(defxdoc fifo-head-tail-simple-model
  :short "A fifo model that uses a list as its
          implementation"
  :long "THIS IS A WORK IN PROGRESS"
  :parents (projects))

(local (set-default-parents fifo-head-tail-simple-model))

(define unsigned4b-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 4 x))

(defun unsigned4b-p-fix (x)
  (if (unsigned4b-p x)
      x
    0))

(fty::deffixtype unsigned4b-p
  :pred unsigned4b-p
  :fix unsigned4b-p-fix
  :equiv equal)

(define unsigned8b-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 8 x))

(defun unsigned8b-p-fix (x)
  (if (unsigned8b-p x)
      x
    0))

(fty::deffixtype unsigned8b-p
  :pred unsigned8b-p
  :fix unsigned8b-p-fix
  :equiv equal)

(fty::defprod address-data
  ((data unsigned8b-p)
   (address unsigned4b-p)))

(defval *default-address-data*
  :short "Default values for invalid address and associated data"
  (address-data 0 0))

(std::deflist address-data-list-p (x)
 (address-data-p x)
 :true-listp t)

(defval *fifo-size-limit*
  :short "Size of the FIFO"
  4)

(define fifo-p (x)
  (and (address-data-list-p x)
       (<= (len x) *fifo-size-limit*)))

(define fifo-empty-p ((fifo fifo-p))
  (atom fifo))

(define fifo-full-p ((fifo fifo-p))
  (<= *fifo-size-limit* (len fifo))) ; could use equal instead

(fty::defprod inst ; instruction is already taken... I should really be in my
  ; own package
  ((write booleanp "Non-nil if the FIFO should be written")
   (write-val address-data-p "Value to write to the FIFO")
   (read booleanp "Non-nil if the FIFO should be read")))

(fty::deflist inst-list
  :elt-type inst)

(define fifo-step
  ((inst inst-p)
   (fifo fifo-p)) :guard-debug t
  :returns (mv (erp booleanp "Whether an error occurred")
               (val address-data-p "Valid output if a read occurs and there is
                                    no error"
                    :hyp :fguard
                    :hints (("Goal" :in-theory (enable fifo-p))))
               (fifo fifo-p "The new fifo" :hyp :fguard
                     :hints (("Goal" :in-theory (enable fifo-p)))))
  :short "Read and/or write to the FIFO."
  :long "The write and read operations occur simultaneously.  As a result, if
         one reads and writes an empty or full queue, no error will occur."
  (b* (((inst inst)))
    (cond ((and inst.read inst.write)
           (mv nil
               (car (append-without-guard fifo (list inst.write-val)))
               (cdr (append-without-guard fifo (list inst.write-val)))))
          ((and inst.read
                (atom fifo)) ; fifo-empty-p
           (mv t
               *default-address-data*
               fifo))
          (inst.read ; fifo isn't empty
           (mv nil
               (car fifo)
               (cdr fifo)))
          ((and inst.write
                (< (len fifo) *fifo-size-limit*))
           (mv nil
               *default-address-data*
               (append-without-guard fifo (list inst.write-val))))
          (inst.write
           (mv t
               *default-address-data*
               fifo))
          (t (mv nil *default-address-data* fifo)))))


;; (defrule cdr-append
;; We don't use this one, because it introduces a case-split.  However, note
;; that we must be able to relieve (consp x) in the version that we do use,
;; below.
;;   (equal (cdr (append x y))
;;          (cond ((atom x)
;;                 (cdr y))
;;                (t
;;                 (append (cdr x) y)))))

(defrule something-about-len
  (implies (consp x)
           (equal (equal n (len x))
                  (equal (1- n) (len (cdr x))))))

(defrule write-and-5-reads
  :long "If we write something, and read four times, one of those four
         outputs is equal to that input."
  (implies (and (address-data-p in)
                (fifo-p fifo)
                (<= (len fifo) *fifo-size-limit*) ; room for one write
                )
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (make-inst :write t
                                       :read t
                                       :write-val in)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (make-inst :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (make-inst :read t)
                            fifo3))
                ((mv ?erp4 out4 ?fifo5)
                 (fifo-step (make-inst :read t)
                            fifo4))
                ((mv ?erp5 out5 ?fifo6)
                 (fifo-step (make-inst :read t)
                            fifo5)))
             (or (equal out1 in)
                 (equal out2 in)
                 (equal out3 in)
                 (equal out4 in)
                 (equal out5 in))))
  :rule-classes nil
  :enable (fifo-step))

(defrule 5-writes-and-5-reads
  :long "If we write something, and read four times, one of those four outputs
         is equal to that input.  The following three writes might cause
         errors, but we don't lose the first input."
  (implies (and (address-data-p in)
                (fifo-p fifo)
                (< (len fifo) *fifo-size-limit*)) ; room for one write
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (make-inst :write t :write-val in :read t)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (make-inst :write-val anything
                                       :write t
                                       :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (make-inst :write-val anything2
                                       :write t
                                       :read t)
                            fifo3))
                ((mv ?erp4 out4 ?fifo5)
                 (fifo-step (make-inst :write-val anything3
                                       :write t
                                       :read t)
                            fifo4))
                                ((mv ?erp5 out5 ?fifo6)
                 (fifo-step (make-inst :read t
                                       :write-val anything4
                                       :write t)
                            fifo5)))
             (or (equal out1 in)
                 (equal out2 in)
                 (equal out3 in)
                 (equal out4 in)
                 (equal out5 in))))
  :rule-classes nil
  :enable (fifo-step))

(defrule something-about-len
  (implies (consp x)
           (equal (equal n (len x))
                  (equal (1- n) (len (cdr x))))))

(defrule other-thing-about-len
  (equal (equal 0 (len x))
         (atom x)))

;; (defrule something-about-len-<
;;   (implies (posp n)
;;            (equal (< (len x) n)
;;                   (and (consp x)
;;                        (< (len (cdr x)) (1- n)))))
;;   :enable len)

;; (defrule other-thing-about-len-<
;;   (equal (< (len x) 0)
;;          nil))

(defrule 4-writes-and-7-reads-are-ordered
  :long "If we write four things, and read seven times, the outputs come out in
         the order that they were input."
  (implies (and (address-data-p in)
                (address-data-p in2)
                (address-data-p in3)
                (address-data-p in4)
                (fifo-p fifo)
                (< (len fifo) *fifo-size-limit*) ; room for one write
                )
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (make-inst :write-val in
                                       :write t
                                       :read t)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (make-inst :write-val in2
                                       :write t
                                       :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (make-inst :write-val in3
                                       :write t
                                       :read t)
                            fifo3))
                ((mv ?erp4 out4 fifo5)
                 (fifo-step (make-inst :write-val in4
                                       :write t
                                       :read t)
                            fifo4))
                ((mv ?erp5 out5 fifo6)
                 (fifo-step (make-inst :write-val anything5
                            :read t)
                            fifo5))
                ((mv ?erp6 out6 fifo7)
                 (fifo-step (make-inst :write-val anything6
                                       :read t)
                            fifo6))
                ((mv ?erp7 out7 ?fifo8)
                 (fifo-step (make-inst :write-val anything7
                                       :read t)
                            fifo7)))
             (cond (;(atom fifo)
                    (equal (len fifo) 0)
                    (and (equal out1 in)
                         (equal out2 in2)
                         (equal out3 in3)
                         (equal out4 in4)))
                   (;(atom (cdr fifo))
                    (equal (len fifo) 1)
                    (and (equal out2 in)
                         (equal out3 in2)
                         (equal out4 in3)
                         (equal out5 in4)))
                   (;(atom (cddr fifo))
                    (equal (len fifo) 2)
                    (and (equal out3 in)
                         (equal out4 in2)
                         (equal out5 in3)
                         (equal out6 in4)))
                   (t ; (atom (cdddr fifo))
                    (and (equal out4 in)
                         (equal out5 in2)
                         (equal out6 in3)
                         (equal out7 in4))))))
  :rule-classes nil
  :enable (fifo-step))


(defrule 4-writes-and-7-reads-are-ordered-with-or
  :long "If we write four things, and read seven times, the outputs come out in
         the order that they were input."
  (implies (and (address-data-p in)
                (address-data-p in2)
                (address-data-p in3)
                (address-data-p in4)
                (fifo-p fifo)
                (< (len fifo) *fifo-size-limit*) ; room for one write
                )
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (make-inst :write-val in
                                       :write t
                                       :read t)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (make-inst :write-val in2
                                       :write t
                                       :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (make-inst :write-val in3
                                       :write t
                                       :read t)
                            fifo3))
                ((mv ?erp4 out4 fifo5)
                 (fifo-step (make-inst :write-val in4
                                       :write t
                                       :read t)
                            fifo4))
                ((mv ?erp5 out5 fifo6)
                 (fifo-step (make-inst :write-val anything5
                            :read t)
                            fifo5))
                ((mv ?erp6 out6 fifo7)
                 (fifo-step (make-inst :write-val anything6
                                       :read t)
                            fifo6))
                ((mv ?erp7 out7 ?fifo8)
                 (fifo-step (make-inst :write-val anything7
                                       :read t)
                            fifo7)))
             (or (and (equal out1 in)
                      (equal out2 in2)
                      (equal out3 in3)
                      (equal out4 in4))
                 (and (equal out2 in)
                      (equal out3 in2)
                      (equal out4 in3)
                      (equal out5 in4))
                 (and (equal out3 in)
                      (equal out4 in2)
                      (equal out5 in3)
                      (equal out6 in4))
                 (and (equal out4 in)
                      (equal out5 in2)
                      (equal out6 in3)
                      (equal out7 in4)))))
  :use 4-writes-and-7-reads-are-ordered
  :in-theory (theory 'minimal-theory)
  :rule-classes nil)


; Prove that you don't get an error if the sequence of instructions is
; well-formed wrt the current queue length (note that the length is
; parameterized [thus, general]).  The "is it well-formed" test is defined
; easily recursively.

; Inductive lemma for reasoning about the step function is: run(i+j,s) is
; run(i,run(j,s))

;; (defval *read-only* 0)
;; (defval *write-only* 1)
;; (defval *write-and-read* 2)

;; (encapsulate (((generate-step-instruction) => *))

;;   (local (defun generate-step-instruction ()
;;     0))

;;   (local (in-theory (disable
;; ; Otherwise the linear rule fails
;;                      (:e generate-step-instruction))))

;;   (defthm generate-step-instruction-type
;;     (natp (generate-step-instruction))
;;     :rule-classes :type-prescription)

;;   (defthm generate-step-instruction-limit
;;     (<= (generate-step-instruction) 2)
;;     :rule-classes :linear)

;;   (defthm generate-step-instruction-bottom
;;     (>= (generate-step-instruction) 0)
;;     :rule-classes :linear))

; It'd be easier to reason about a sequence of reads/writes, rather than the
; absraction of fifo-step.  Consider proving that using fifo-step is equivalent
; to the "exploded" version of the interpreter.

; (1) Write a version of fifo-step that takes an instruction as input

; (2) Write a function that takes a sequence of instructions and calls
; fifo-step on each of them.  Figure out whether to have a "defensive"
; interpreter, which would immediately signal an error.  Or, something more
; liberal, which would just skip instructions that cause an error.

; (3) Create a verilog module that also contains an "error flag" as one of its
; signals.  Show that this list-based fifo is equivalent to that module.

(define room-for-instruction
  ((instruction inst-p "Instruction to test")
   (count-in-queue natp "Number of address-data pairs in the queue"))
  (b* (((inst instruction))
       ((when (and instruction.write instruction.read))
        t)
       ((when (and instruction.write
                   (>= count-in-queue *fifo-size-limit*)))
        nil)
       ((when (and instruction.read
                   (<= count-in-queue 0)))
        nil))
    t))

(define next-count-in-queue
  ((instruction inst-p "Current instruction")
   (count-in-queue natp "Number of address-data pairs in the queue"))
  :returns (retval natp "Next count in the queue, assuming the given
                         instruction executes."
                   :hyp :fguard)
  (b* (((inst instruction)))
    (cond ((and instruction.write instruction.read)
           count-in-queue)
          (instruction.write
           (1+ count-in-queue))
          (instruction.read
           (nfix (1- count-in-queue)))
          (t count-in-queue))))

(define instructions-valid-p
  ((instructions t "Instructions to march forward")
   (count-in-queue natp))
  :returns (valid-p booleanp "Whether the instructions are valid.")
  :long "We test a list of instructions for validity.  For example, it doesn't
         make sense to read when we haven't written something to the buffer."
  (cond ((atom instructions)
         t)
        (t
         (and (inst-p (car instructions))
              (room-for-instruction (car instructions)
                                    count-in-queue)
              (instructions-valid-p (cdr instructions)
                                    (next-count-in-queue (car instructions)
                                                         count-in-queue))))))

(assert!
 (instructions-valid-p
  (list (make-inst :write t :write-val *default-address-data* :read t)
        (make-inst :write t :write-val *default-address-data*)
        (make-inst :read t :write-val *default-address-data*))
  0))

(assert!
 (not (instructions-valid-p
       (list (make-inst :write t :write-val *default-address-data* :read t)
             (make-inst :read t :write-val *default-address-data*)
             (make-inst :write t :write-val *default-address-data*))
       0)))

(assert!
 (not (instructions-valid-p
       (list (make-inst :write t :write-val *default-address-data* :read t)
             (make-inst :write t :write-val *default-address-data*)
             (make-inst :read t :write-val *default-address-data*))
       4)))

(define fifo-run
  ((instructions (instructions-valid-p instructions (len fifo)))
   (fifo fifo-p)
   (read-acc address-data-list-p))
   :returns (mv erp fifo read-values)
  ;;             fifo t) ;fifo-p :hyp :fguard
  ;;                    ;:hints (("goal" :in-theory (enable fifo-step fifo-p))))
  ;;              (fifo t)
  ;;              (read-values t));  address-data-list-p))
  :verify-guards nil
  (cond ((atom instructions)
         (mv nil fifo (rev read-acc)))
        (t
         (b* (((mv erp read-val new-fifo)
               (fifo-step (car instructions)
                          fifo))
              ((when erp)
               (mv erp new-fifo (rev read-acc)))
              (read-acc (cons read-val read-acc)))
           (fifo-run (cdr instructions) new-fifo read-acc)))))
;;   ///

;; (defrulel return-lemma-fifo-p-1
;;   (IMPLIES
;;    (AND (INSTRUCTIONS-VALID-P INSTRUCTIONS (LEN FIFO))
;;         (ADDRESS-DATA-LIST-P FIFO)
;;         (<= (LEN FIFO) 4)
;;         (ADDRESS-DATA-LIST-P READ-ACC))
;;    (ADDRESS-DATA-LIST-P (MV-NTH 1
;;                                 (FIFO-RUN INSTRUCTIONS FIFO READ-ACC)))))
;;   :enable (address-data-list-p instructions-valid-p room-for-instruction))

;;   (more-returns
;;    (erp booleanp)
;;    (fifo fifo-p :hyp :fguard
;;          :hints (("goal" :in-theory (enable fifo-step fifo-p))))
;;    (read-values address-data-list-p)))

#|| Commented out by Matt K. (not an embedded event form).
(fifo-run
 (list (make-inst :write t :write-val *default-address-data* :read t)
       (make-inst :write t :write-val *default-address-data*)
       (make-inst :read t :write-val *default-address-data*))
 nil
 nil)
||#

(defrule valid-instructions-implies-no-error-base-case-lemma
  (implies (and (INST-P INST)
                (ROOM-FOR-INSTRUCTION INST
                                      (LEN FIFO)))
           (not (MV-NTH 0 (FIFO-STEP INST FIFO))))
  :enable (fifo-step room-for-instruction))

#|
Learning note:

We saw checkpoint Subgoal *1/4'':

; Since we don't see a call of fifo-run on the cdr in the hyps, we suspect that
; it's probably true for another reason (i.e., because of a contradiction in
; the hyps).  And indeed, after we performed our investigation, we found that
; fifo and read-val were being bound in each others' slots in the body of
; fifo-run.

(IMPLIES
  (AND (CONSP INSTRUCTIONS)
       (NOT (FIFO-P (MV-NTH 1 (FIFO-STEP (CAR INSTRUCTIONS) FIFO))))
       (INST-P (CAR INSTRUCTIONS))
       (ROOM-FOR-INSTRUCTION (CAR INSTRUCTIONS)
                             (LEN FIFO))
       (INSTRUCTIONS-VALID-P (CDR INSTRUCTIONS)
                             (NEXT-COUNT-IN-QUEUE (CAR INSTRUCTIONS)
                                                  (LEN FIFO)))
       (FIFO-P FIFO))
  (NOT (MV-NTH 0
               (FIFO-RUN (CDR INSTRUCTIONS)
                         (MV-NTH 1 (FIFO-STEP (CAR INSTRUCTIONS) FIFO))
                         (CONS (MV-NTH 2 (FIFO-STEP (CAR INSTRUCTIONS) FIFO))
                               (MV-NTH 1
                                       (FIFO-STEP (CAR INSTRUCTIONS)
                                                  FIFO)))))))

; We can see that under the induction, we get the following statement from
; ACL2:

(AND (IMPLIES (AND (NOT (ATOM INSTRUCTIONS))
                   (NOT (MV-NTH 0 (FIFO-STEP (CAR INSTRUCTIONS) FIFO)))
                   (:P (MV-NTH 2 (FIFO-STEP (CAR INSTRUCTIONS) FIFO))
                       (CDR INSTRUCTIONS)))
              (:P FIFO INSTRUCTIONS))
     (IMPLIES (AND (NOT (ATOM INSTRUCTIONS))
                   (MV-NTH 0 (FIFO-STEP (CAR INSTRUCTIONS) FIFO)))
              (:P FIFO INSTRUCTIONS))
     (IMPLIES (ATOM INSTRUCTIONS)
              (:P FIFO INSTRUCTIONS)))

We call the first of the three conjuncts an induction step, because there is a
reference to :P in the hypotheses, where as the second and third conjuncts do
not have a reference to :P in their hypotheses.  This means the second and
third conjuncts are base cases.

We can tell from looking at the induction step, that we forgot to generalize
our accumulator (we were passing in nil, but we needed a variable).  So we
generalize the accumlator, and we guess that we won't need any additional
hypotheses about the generalized accumulator, because the accumulator can't
cause errors.


After we generalize, we get the following two checkpoints.  *1/3' has a
contradiction of sorts in hypotheses 3 and 6.  *1/2' is exactly what we would
expect to see, given ACL2 now has an appropriate induction and that fifo-step
is disabled.

Subgoal *1/3'
(IMPLIES
 (AND
  (CONSP INSTRUCTIONS)
  (NOT (MV-NTH 0 (FIFO-STEP (CAR INSTRUCTIONS) FIFO)))
  (NOT ; third and sixth hyps form a lemma about fifo-step
   (INSTRUCTIONS-VALID-P (CDR INSTRUCTIONS)
                         (LEN (MV-NTH 2
                                      (FIFO-STEP (CAR INSTRUCTIONS) FIFO)))))
  (INST-P (CAR INSTRUCTIONS))
  (ROOM-FOR-INSTRUCTION (CAR INSTRUCTIONS)
                        (LEN FIFO))
  (INSTRUCTIONS-VALID-P (CDR INSTRUCTIONS)
                        (NEXT-COUNT-IN-QUEUE (CAR INSTRUCTIONS)
                                             (LEN FIFO)))
  (FIFO-P FIFO))
 (NOT (MV-NTH 0
              (FIFO-RUN (CDR INSTRUCTIONS)
                        (MV-NTH 2 (FIFO-STEP (CAR INSTRUCTIONS) FIFO))
                        (CONS (MV-NTH 1 (FIFO-STEP (CAR INSTRUCTIONS) FIFO))
                              ACC)))))

Subgoal *1/2'
(IMPLIES (AND (CONSP INSTRUCTIONS)
              (MV-NTH 0 (FIFO-STEP (CAR INSTRUCTIONS) FIFO)) ; make a lemma for this with fifo-step
              (INST-P (CAR INSTRUCTIONS))
              (ROOM-FOR-INSTRUCTION (CAR INSTRUCTIONS)
                                    (LEN FIFO))
              (INSTRUCTIONS-VALID-P (CDR INSTRUCTIONS)
                                    (NEXT-COUNT-IN-QUEUE (CAR INSTRUCTIONS)
                                                         (LEN FIFO))))
         (NOT (FIFO-P FIFO)))


|#

(defrulel valid-instructions-implies-no-error-base-case-lemma-2
; restatement of *1/3' above
  (implies
   (and (room-for-instruction (car instructions)
                              (len fifo))
        (instructions-valid-p (cdr instructions)
                              (next-count-in-queue (car instructions)
                                                   (len fifo))))
   (instructions-valid-p (cdr instructions)
                         (len (mv-nth 2
                                      (fifo-step (car instructions) fifo)))))
  :enable (fifo-step instructions-valid-p room-for-instruction next-count-in-queue))

(defrulel valid-instructions-implies-no-error-induction-step
; restatement of *1/2' above
  (implies (and (fifo-p fifo)
                (inst-p inst)
                (room-for-instruction inst (len fifo)))
         (not (mv-nth 0 (fifo-step inst fifo))))
  :enable (fifo-step room-for-instruction))

(defrule valid-instructions-implies-no-error
  (implies (and (instructions-valid-p instructions (len fifo))
                (fifo-p fifo))
           (b* (((mv erp ?fifo ?vals)
                 (fifo-run instructions fifo acc)))
             (not erp)))
  :enable (fifo-run instructions-valid-p)
; We leave fifo-step and fifo-p disabled so that our checkpoint looks like
; something that we actually want a lemma for (we kind of suspect that we need
; a lemma about fifo-step anyway).
  :do-not '(preprocess)
  :rule-classes nil)

#|
(encapsulate (((generate-instruction) => *))

  (local (defun generate-instruction ()
           (make-inst :read t :write-val *default-address-data* :write t)))

  (defthm inst-p-of-generate-instruction
    (inst-p (generate-instruction))))

(encapsulate (((generate-instruction * *) => *))

  (local
   (defun generate-instruction (something-free fifo)
     (declare (ignore something-free fifo))
     (make-inst :read t :write-val *default-address-data* :write t)))

  (defthm inst-p-of-generate-instruction
    (inst-p (generate-instruction something-free fifo)))

  (defrule room-for-generated-instruction
    :long "@('Generate-instruction') only generates instructions where there's
           room in the queue.

           We decided to go ahead and pass in the fifo to
           @('generate-instruction'), but it's probably unnecssary, since we're
           already passing in @('something-free'), which already provides
           maximum non-determinism (provided each call of
           @('generate-instruction') is given a different binding."

; Outdated documentation options:

; For the sake of intuition, we could say that
; @('something-free') helps us ensure that the function does that
; (e.g., @('something-free') could include the @('count-in-queue')).
; However, technically, this is unnecessary -- as this
; theorem/constraint ensures that generate-instruction only generates
; instructions where there's room for their execution in the queue.

; This is a rather odd way of making this constraint, but it should work.  If
; we were writing a version of generate-instruction that we were going to
; actually write, we'd need to pass in @('count-in-queue').

; There is some question as to whether room-for-instruction should take
; count-in-queue, state, or some other object so that (generate-instruction)
; doesn't necessarily equal (generate-instruction).  Indeed, it probably
; should.

    (room-for-instruction (generate-instruction something-free fifo)
                          (len fifo))
    :enable room-for-instruction))
|#

; Kaufmann agrees that the above is a reasonable approach.  However, he
; suggests that encapsulate is unnecessary at this point.  Instead, we can
; introduce non-determinism by just having free variable values for :read,
; :write, and :write-val.

(define generate-instruction (fifo
                              &key
                              (read booleanp)
                              (write booleanp)
                              (write-val address-data-p))
  :long "Introduce non-determinism by just having free variable values
         for :read, :write, and :write-val."
  (b* ((inst (make-inst :read read :write write :write-val write-val)))
    (cond ((room-for-instruction inst (len fifo))
           inst)
          (t (make-inst :write-val *default-address-data*))))
  ///
  (defrule room-for-generated-instruction
    (room-for-instruction (generate-instruction fifo
                                                :read free1
                                                :write free2
                                                :write-val free3)
                          (len fifo))
    :enable (room-for-instruction)))


(defrule 1-deterministic-4-non-deterministic
  (implies (and (address-data-p in)
                (fifo-p fifo)
                (<= (len fifo) *fifo-size-limit*))
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (generate-instruction fifo
                                                  :write t
                                                  :write-val in
                                                  :read t)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (generate-instruction fifo2
                                                  :write free2a
                                                  :write-val free2b
                                                  :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (generate-instruction fifo3
                                                  :write free3a
                                                  :write-val free3b
                                                  :read t)
                            fifo3))
                ((mv ?erp4 out4 ?fifo5)
                 (fifo-step (generate-instruction fifo4
                                                  :write free4a
                                                  :write-val free4b
                                                  :read t)
                            fifo4))
                ((mv ?erp5 out5 ?fifo6)
                 (fifo-step (generate-instruction fifo5
                                                  :write free5a
                                                  :write-val free5b
                                                  :read t)
                            fifo5)))
             (or (equal out1 in)
                 (equal out2 in)
                 (equal out3 in)
                 (equal out4 in)
                 (equal out5 in))))
  :rule-classes nil
  :enable (fifo-step generate-instruction room-for-instruction fifo-p))


(defrule 4-deterministic-7-non-deterministic
  :long "If we write four things, and read seven times, the outputs come out in
         the order that they were input."
  (implies (and (address-data-p in)
                (address-data-p in2)
                (address-data-p in3)
                (address-data-p in4)
                (fifo-p fifo)
                (<= (len fifo) *fifo-size-limit*)
                )
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (generate-instruction fifo
                                                  :write t
                                                  :write-val in
                                                  :read t)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (generate-instruction fifo2
                                                  :write t
                                                  :write-val in2
                                                  :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (generate-instruction fifo3
                                                  :write t
                                                  :write-val in3
                                                  :read t)
                            fifo3))
                ((mv ?erp4 out4 ?fifo5)
                 (fifo-step (generate-instruction fifo4
                                                  :write t
                                                  :write-val in4
                                                  :read t)
                            fifo4))
                ((mv ?erp5 out5 ?fifo6)
                 (fifo-step (generate-instruction fifo5
                                                  :write free5a
                                                  :write-val free5b
                                                  :read t)
                            fifo5))
                ((mv ?erp6 out6 fifo7)
                 (fifo-step (generate-instruction fifo6
                                                  :write free6a
                                                  :write-val free6b
                                                  :read t)
                            fifo6))
                ((mv ?erp7 out7 ?fifo8)
                 (fifo-step (generate-instruction fifo7
                                                  :write free7a
                                                  :write-val free7b
                                                  :read t)
                            fifo7))
                ((mv ?erp8 out8 ?fifo9)
                 (fifo-step (generate-instruction fifo8
                                                  :write free8a
                                                  :write-val free8b
                                                  :read t)
                            fifo8)))
             (cond (;(atom fifo)
                    (equal (len fifo) 0)
                    (and (equal out1 in)
                         (equal out2 in2)
                         (equal out3 in3)
                         (equal out4 in4)))
                   (;(atom (cdr fifo))
                    (equal (len fifo) 1)
                    (and (equal out2 in)
                         (equal out3 in2)
                         (equal out4 in3)
                         (equal out5 in4)))
                   (;(atom (cddr fifo))
                    (equal (len fifo) 2)
                    (and (equal out3 in)
                         (equal out4 in2)
                         (equal out5 in3)
                         (equal out6 in4)))
                   (;(atom (cdddr fifo))
                    (equal (len fifo) 3)
                    (and (equal out4 in)
                         (equal out5 in2)
                         (equal out6 in3)
                         (equal out7 in4)))
                   (t ; (atom (cddddr fifo))
                    (and (equal out5 in)
                         (equal out6 in2)
                         (equal out7 in3)
                         (equal out8 in4))))))
  :rule-classes nil
  :enable (fifo-step generate-instruction room-for-instruction fifo-p))


(defrule 4-deterministic-7-non-deterministic-are-ordered
  :long "If we write four things, and read seven times, the outputs come out in
         the order that they were input."
  (implies (and (address-data-p in)
                (address-data-p in2)
                (address-data-p in3)
                (address-data-p in4)
                (fifo-p fifo)
                (<= (len fifo) *fifo-size-limit*))
           (b* (((mv ?erp1 out1 fifo2)
                 (fifo-step (generate-instruction fifo
                                                  :write t
                                                  :write-val in
                                                  :read t)
                            fifo))
                ((mv ?erp2 out2 fifo3)
                 (fifo-step (generate-instruction fifo2
                                                  :write t
                                                  :write-val in2
                                                  :read t)
                            fifo2))
                ((mv ?erp3 out3 fifo4)
                 (fifo-step (generate-instruction fifo3
                                                  :write t
                                                  :write-val in3
                                                  :read t)
                            fifo3))
                ((mv ?erp4 out4 ?fifo5)
                 (fifo-step (generate-instruction fifo4
                                                  :write t
                                                  :write-val in4
                                                  :read t)
                            fifo4))
                ((mv ?erp5 out5 ?fifo6)
                 (fifo-step (generate-instruction fifo5
                                                  :write free5a
                                                  :write-val free5b
                                                  :read t)
                            fifo5))
                ((mv ?erp6 out6 fifo7)
                 (fifo-step (generate-instruction fifo6
                                                  :write free6a
                                                  :write-val free6b
                                                  :read t)
                            fifo6))
                ((mv ?erp7 out7 ?fifo8)
                 (fifo-step (generate-instruction fifo7
                                                  :write free7a
                                                  :write-val free7b
                                                  :read t)
                            fifo7))
                ((mv ?erp8 out8 ?fifo9)
                 (fifo-step (generate-instruction fifo8
                                                  :write free8a
                                                  :write-val free8b
                                                  :read t)
                            fifo8)))
             (or (and (equal out1 in)
                      (equal out2 in2)
                      (equal out3 in3)
                      (equal out4 in4))
                 (and (equal out2 in)
                      (equal out3 in2)
                      (equal out4 in3)
                      (equal out5 in4))
                 (and (equal out3 in)
                      (equal out4 in2)
                      (equal out5 in3)
                      (equal out6 in4))
                 (and (equal out4 in)
                      (equal out5 in2)
                      (equal out6 in3)
                      (equal out7 in4))
                 (and (equal out5 in)
                      (equal out6 in2)
                      (equal out7 in3)
                      (equal out8 in4)))))
  :use 4-deterministic-7-non-deterministic
  :in-theory (theory 'minimal-theory)
  :rule-classes nil)
