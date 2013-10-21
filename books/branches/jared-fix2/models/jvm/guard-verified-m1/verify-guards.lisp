#||

See the README file on this directory for an overview of this work.

In this file I verify the guards on the M1 model.  The guards are exhibited in
the function definitions presented in m1.lisp and the functions used to express
the guards are defined in good-statep.lisp.  All of the functions in
good-statep.lisp are already guard verified.

To play:

; (include-book "m1")
; (ld "verify-guards.lisp" :ld-pre-eval-print t)

To recertify:

; (include-book "m1")
; (certify-book "verify-guards" 1)

||#

(in-package "M1")

; These functions are left disabled by "m1.lisp" so that that book alone can be
; used to verify code.  But to verify the guards of these functions we need to
; have them enabled.  We re-disable them at the end of this book.

(in-theory (enable make-state pc locals stack program step m1))

; -----------------------------------------------------------------
; Stack Manipulation

; A stack is a true-list of rationals.  Here we show the consequences of this.

(defthm stackp-implies-true-listp
  (implies (stackp x)
           (true-listp x)))

(defthm stackp-push
  (implies (and (rationalp x) (stackp y))
           (stackp (push x y)))
  :hints (("Goal" :in-theory (enable push))))

(defthm integerp-top
  (implies (and (stackp x) (not (equal x nil)))
           (rationalp (top x)))
  :hints (("Goal" :in-theory (enable top))))

; ---  horrible lemmas for a user to have to state ---

(defthm integerp-+
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (+ x y))))

(defthm rationalp--
  (implies (rationalp x)
           (rationalp (- x))))

; --- end of horrible lemmas ---

(defthm stackp-pop
  (implies (stackp x) (stackp (pop x)))
  :hints (("Goal" :in-theory (enable pop))))

; -----------------------------------------------------------------
; The Locals of a State

; The locals must be a list of integers.  This is equivalent to stackp but
; we'll define it separately for sanity.

(defthm localsp-implies-true-listp
  (implies (localsp x)
           (true-listp x)))

(defthm localsp-nth
  (implies (and (localsp lst)
                (natp i)
                (< i (len lst)))
           (rationalp (nth i lst))))

(defthm localsp-update-nth
  (implies (and (natp i)
                (rationalp v)
                (localsp x)
                (< i (len x)))
           (localsp (update-nth i v x))))

(defthm len-update-nth-new
  (implies (and (natp i)
                (< i (len x)))
           (equal (len (update-nth i v x)) (len x))))

; -----------------------------------------------------------------
; Instruction Well-Formedness

(in-theory (disable make-state
                    (:executable-counterpart make-state)
                    pc locals stack program))

; -----------------------------------------------------------------
; Computing a Stack Map

; We need a couple of key lemmas about csm: ``Property 1'' is that if pc is
; legal and (csm program stack-map) is true and (nth pc program) is
; an IADD [say], then 2 <= (cdr (assoc pc stack-map)).  Of course, we need the
; analogous theorem for IADD, ISUB, IMUL, ISTORE, and IFEQ.

; ``Property 2'' is that if (nth pc program) is an IADD [say] then the stack
; map at (+ 1 pc) is one greater than at pc.

; Our approach is first to prove inductive versions of properties 1 and 2 for
; csm1, making the resulting general theorem :rule-classes nil.  Then, we
; instantiate each of the general properties for specific opcodes.  We start with
; property 1 and then do property 2.

(defthm csm1-property-1
  (implies (and (natp i)
                (natp pc)
                (<= i pc)
                (< pc (len program))
                (csm1 i program stack-map))
           (<= (case (op-code (nth pc program))
                 ((ISTORE IFEQ) 1)
                 ((IADD ISUB IMUL) 2)
                 (otherwise 0))
               (cdr (assoc-equal pc stack-map))))
  :rule-classes nil)

(defthm csm-IADD-ISUB-IMUL-property-1
  (implies (and (csm (program s) stack-map)
                (pcp (pc s) (len (program s)))
                (member (op-code (nth (pc s) (program s))) '(IADD ISUB IMUL)))
           (<= 2 (cdr (assoc (pc s) stack-map))))
  :hints (("Goal" :in-theory (enable csm)
           :use (:instance csm1-property-1
                           (i 0)
                           (pc (pc s))
                           (program (program s))
                           (stack-map stack-map))))
  :rule-classes :linear)

(defthm csm-ISTORE-IFEQ-property-1
  (implies (and (csm (program s) stack-map)
                (pcp (pc s) (len (program s)))
                (member (op-code (nth (pc s) (program s))) '(ISTORE IFEQ)))
           (<= 1 (cdr (assoc (pc s) stack-map))))
  :hints (("Goal" :in-theory (enable csm)
                  :use (:instance csm1-property-1
                                  (i 0)
                                  (pc (pc s))
                                  (program (program s))
                                  (stack-map stack-map))))
  :rule-classes :linear)

(defthm csm1-property-2
  (implies (and (natp i)
                (natp pc)
                (<= i pc)
                (< pc (len program))
                (csm1 i program stack-map))
           (and (implies (equal (op-code (nth pc program)) 'GOTO)
                         (and (assoc (+ pc (arg1 (nth pc program))) stack-map)
                              (equal (cdr (assoc pc stack-map))
                                     (cdr (assoc (+ pc (arg1 (nth pc program))) stack-map)))))
                (implies (equal (op-code (nth pc program)) 'IFEQ)
                         (and (assoc (+ pc (arg1 (nth pc program))) stack-map)
                              (assoc (+ 1 pc) stack-map)
                              (equal (+ -1 (cdr (assoc pc stack-map)))
                                     (cdr (assoc (+ pc (arg1 (nth pc program))) stack-map)))
                              (equal (+ -1 (cdr (assoc pc stack-map)))
                                     (cdr (assoc (+ 1 pc) stack-map)))))
                (implies (member (op-code (nth pc program))
                                      '(ILOAD ICONST))
                         (and (assoc (+ 1 pc) stack-map)
                              (equal (+ 1 (cdr (assoc pc stack-map)))
                                     (cdr (assoc (+ 1 pc) stack-map)))))
                (implies (member (op-code (nth pc program))
                                      '(IADD ISUB IMUL ISTORE))
                         (and (assoc (+ 1 pc) stack-map)
                              (equal (+ -1 (cdr (assoc pc stack-map)))
                                     (cdr (assoc (+ 1 pc) stack-map)))))))
  :rule-classes nil)

(defthm csm-GOTO-property-2
  (implies (and (csm (program s) stack-map)
                (pcp (pc s) (len (program s)))
                (equal (op-code (nth (pc s) (program s))) 'GOTO))
           (and (assoc (+ (pc s) (arg1 (nth (pc s) (program s)))) stack-map)
                (equal (cdr (assoc (+ (pc s) (arg1 (nth (pc s) (program s)))) stack-map))
                       (cdr (assoc (pc s) stack-map)))))
  :hints (("Goal" :in-theory (e/d (csm) (csm1))
                  :use (:instance csm1-property-2
                                  (i 0)
                                  (pc (pc s))
                                  (program (program s))
                                  (stack-map stack-map)))))

(defthm csm-IFEQ-property-2
  (implies (and (csm (program s) stack-map)
                (pcp (pc s) (len (program s)))
                (equal (op-code (nth (pc s) (program s))) 'IFEQ))
           (and (assoc (+ (pc s) (arg1 (nth (pc s) (program s)))) stack-map)
                (assoc (+ 1 (pc s)) stack-map)
                (equal (cdr (assoc (+ (pc s) (arg1 (nth (pc s) (program s)))) stack-map))
                       (+ -1 (cdr (assoc (pc s) stack-map))))
                (equal (cdr (assoc (+ 1 (pc s)) stack-map))
                       (+ -1 (cdr (assoc (pc s) stack-map))))))
  :hints (("Goal" :in-theory (e/d (csm) (csm1))
           :use (:instance csm1-property-2
                           (i 0)
                           (pc (pc s))
                           (program (program s))
                           (stack-map stack-map)))))

(defthm csm-ILOAD-ICONST-property-2
  (implies (and (csm (program s) stack-map)
                (pcp (pc s) (len (program s)))
                (member (op-code (nth (pc s) (program s))) '(ILOAD ICONST)))
           (and (assoc (+ 1 (pc s)) stack-map)
                (equal (cdr (assoc (+ 1 (pc s)) stack-map))
                       (+ 1 (cdr (assoc (pc s) stack-map))))))
  :hints (("Goal" :in-theory (e/d (csm) (csm1))
           :use (:instance csm1-property-2
                           (i 0)
                           (pc (pc s))
                           (program (program s))
                           (stack-map stack-map)))))

(defthm csm-IADD-ISUB-IMUL-ISTORE-property-2
  (implies (and (csm (program s) stack-map)
                (pcp (pc s) (len (program s)))
                (member (op-code (nth (pc s) (program s))) '(IADD ISUB IMUL ISTORE)))
           (and (assoc (+ 1 (pc s)) stack-map)
                (equal (cdr (assoc (+ 1 (pc s)) stack-map))
                       (+ -1 (cdr (assoc (pc s) stack-map))))))
  :hints (("Goal" :in-theory (e/d (csm) (csm1))
           :use (:instance csm1-property-2
                           (i 0)
                           (pc (pc s))
                           (program (program s))
                           (stack-map stack-map)))))


; -----------------------------------------------------------------
; Well-Formed States

; Note on strategy:

; After admitting and proving the guards of an instruction's semantic function,
; I will prove that the instruction preserves good-statep.  I do this for each
; semantic function.  When that is done, I'll temporarily disable all the
; semantic functions (so lemmas about them are available) and prove the theorem
; that do-inst satisfies its guard and preserves good-statep.  Then I do repeat
; that for step and the M1 interpreter.

; In a model as small as M1 it is just as practical to NOT prove the
; preservation property for each instruction, and just do it all at once when
; we prove it for step.  One advantage of doing it the structured way, as done
; here, is that it enables the discovery of the necessary lemmas (e.g.,
; len-push above) in a manageable way.  We would get a lot of failures on the
; proof of good-statep-step if we hadn't already proved the necessary lemmas
; for each instruction.  So we are modularizing the proof discovery process
; too.

; The functions below marked redundant were actually guard verified in
; good-statep.lisp.  They're listed here just to remind the user that we must
; verify the guards of every function used in the model.

(verify-guards push)
(verify-guards top)
(verify-guards pop)
(verify-guards nth)         ; redundant
(verify-guards update-nth)
(verify-guards op-code)     ; redundant
(verify-guards arg1)        ; redundant
(verify-guards arg2)
(verify-guards arg3)
(verify-guards make-state)
(verify-guards pc)          ; redundant
(verify-guards locals)      ; redundant
(verify-guards stack)       ; redundant
(verify-guards program)     ; redundant
(verify-guards next-inst)

; To verify the guards on the individual instructions we need the same basic
; ``use-when'' machinery set up in good-statep.

(acl2::use-when instructionp-nth         ; lemma name
                nil                      ; initial substitution
                :hyp (programp lst)      ; patterns to look for as
                :subterm (nth pc lst))

(acl2::use-when next-pc-okp-nth
                ((pc . '0))
                :hyp (all-pcs-okp program pc)
                :subterm (nth i program))

(verify-guards ok-to-step)

(verify-guards execute-ILOAD)
(defthm good-statep-ILOAD
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'ILOAD))
           (good-statep (execute-ILOAD (nth (pc s) (program s)) s))))

(verify-guards execute-ICONST)
(defthm good-statep-ICONST
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'ICONST))
           (good-statep (execute-ICONST (nth (pc s) (program s)) s))))

(defthm top-guards-1
  (implies (and (stackp stk)
                (< 0 (len stk)))
           (and (rationalp (top stk))
                (stackp (pop stk))))
  :hints (("Goal" :in-theory (enable stackp top pop))))

(defthm top-guards-2
  (implies (and (stackp stk)
                (< 1 (len stk)))
           (and (rationalp (top stk))
                (consp (pop stk))
                (rationalp (top (pop stk)))
                (stackp (pop (pop stk)))))
  :hints (("Goal" :in-theory (enable stackp top pop))))

(verify-guards execute-IADD)

(defthm len-pop
  (equal (len x)
         (if (endp x)
             0
             (+ 1 (len (pop x)))))
  :hints (("Goal" :in-theory (enable pop)))
  :rule-classes (:definition))

(defthm good-statep-IADD
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'IADD))
           (good-statep (execute-IADD (nth (pc s) (program s)) s))))

(verify-guards execute-ISUB)
(defthm good-statep-ISUB
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'ISUB))
           (good-statep (execute-ISUB (nth (pc s) (program s)) s))))

(verify-guards execute-IMUL)
(defthm good-statep-IMUL
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'IMUL))
           (good-statep (execute-IMUL (nth (pc s) (program s)) s))))

(verify-guards execute-ISTORE)
(defthm good-statep-ISTORE
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'ISTORE))
           (good-statep (execute-ISTORE (nth (pc s) (program s)) s))))

(verify-guards execute-GOTO)
(defthm good-statep-GOTO
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'GOTO))
           (good-statep (execute-GOTO (nth (pc s) (program s)) s))))

(verify-guards execute-IFEQ)
(defthm good-statep-IFEQ
  (implies (and (good-statep s)
                (equal (op-code (nth (pc s) (program s))) 'IFEQ))
           (good-statep (execute-IFEQ (nth (pc s) (program s)) s))))

(verify-guards do-inst)

; We don't bother to prove that do-inst, when applied to the next-inst,
; preserves good-statep.  Instead we will do it ``in place'' when we verify the
; corresponding theorem for step.

(verify-guards step)

; The in-theory hint is not necessary below but is good hygine, since we have
; already proved the preservation property for each opcode.

(in-theory (disable good-statep))

(defthm good-statep-step
  (implies (good-statep s)
           (good-statep (step s)))
  :hints
  (("Goal" :in-theory (disable execute-ILOAD
                               execute-ICONST
                               execute-IADD
                               execute-ISUB
                               execute-IMUL
                               execute-ISTORE
                               execute-GOTO
                               execute-IFEQ))))

(in-theory (disable step))

(verify-guards m1)
(defthm good-statep-m1
  (implies (good-statep s)
           (good-statep (m1 s n))))

(in-theory (enable good-statep))

(verify-guards haltedp)

