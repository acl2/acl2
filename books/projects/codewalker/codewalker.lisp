; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Codewalker (Version 15)
; J Moore
; with help from Warren Hunt and Matt Kaufmann
; June, 2014

; =============================================================================
; Introduction

; ``Codewalker'' is a utility for exploring code in any programming language
; specified by an ACL2 model to discover certain properties of the code.

; Two main facilities are provided by Codewalker: the abstraction of a piece of
; code into an ACL2 ``semantic function'' that returns the same machine state,
; and the ``projection'' of such a function into another function that computes
; the final value of a given state component using only the values of the
; relevant initial state components.

; Codewalker is independent of any particular machine model, as long as a
; step-based operational semantics for the machine is defined in ACL2.  To
; facilitate this language-independent analysis, the user must declare a
; ``model API'' that allows Codewalker to access functionality of the model
; (e.g., setting the pc in a symbolic state).  Generally speaking, Codewalker
; accesses the model by forming symbolic ACL2 expressions that answer certain
; questions, then applying the ACL2 simplifier with full access to user-proved
; lemmas, and then inspecting the resulting term to recover the answer.

; This book starts with an extensive comment -- over 3000 lines (~50 pages).
; This comment is structured like a paper and its intended audience includes
; both users of Codewalker and any future developers of Codewalker.  The major
; sections of the comment are listed below.  Each section starts with a line of
; equal (=) signs.

; Codewalker has many limitations:

; * You must have a suitable ACL2 lemma data base configured for code proofs
;   about your model.

; * It must be possible to express the API in the terms required by
;   def-model-api.  You must be able to identify a ``machine state,'' a
;   single-step state transition function, here called ``step,'' and a ``pc''
;   that points to the next instruction to be stepped.

; * Every reachable pc (in the region of code to be explored) must be constant,
;   starting with the initial pc, i.e., you have to know, in concrete terms,
;   where the instructions are stored.

; * Given the instruction at a reachable pc it must be possible to determine,
;   by rewriting the step function, what the possible next values of the pc
;   will be.  This means Codewalker cannot handle instructions that set the pc
;   to data dependent values.

; * The program should not exercise aliasing, i.e., writing in a way that
;   changes the values of parts of the state not explicitly mentioned.

; * The region of code to be explored must terminate.

; * The region of code to be explored should not modify itself during execution.

; These limitations and a couple of ways to mitigate some of them are discussed
; in a section below.

; Here are the major sections of this file.  We recommend they be read in this
; order, by the audiences identified:

; [For All Potential Users and Developers:]

; A Friendly Introduction to Codewalker
;    a worked example of def-model-api, def-semantics, and def-projection for
;    a very simple machine, M1, including examples of output produced by
;    Codewalker

; Reference Guide to Def-Model-API, Def-Semantics, and Def-Projection
;    a full explanation of the options available

; Appendix A: More on Four Similiar Data Structures: :updater-drivers,
;   :constructor-drivers, :state-comps-and-types, and :var-names.
;    an elaboration of several features; you may or may not be interested in
;    this material, depending on whether the explanations in earlier sections
;    suffice for your use

; Limitations and Mitigations
;    what Codewalker cannot handle and a few suggestions that might permit
;    Codewalker to help you, some, anyway

; [For Developers Only:]

; Following Some Examples through the Implementation
;    the same examples as in the Friendly Introduction, but seen from the
;    ``inside;'' examples of internal functions and data structures are
;    shown to give a sense of how Codewalker works

; Guide to the Implementation of Codewalker descriptions of the books upon
;    which Codewalker is built, the basic data structures driving Codewalker,
;    and high level sketches of the individual steps used by def-semantics and
;    def-projection to derive their results; following these high level
;    descriptions are more detailed descriptions of each step, including
;    reference to the relevant function names in the Code

; The Code for Codewalker
;    the definitions of all the functions and data structures in Codewalker,
;    interspersed with comments explaining many low-level details not covered
;    in the material above; these comments freely use the terminology
;    introduced above and may be hard to understand if you haven't read the
;    foregoing material

; How to Certify Codewalker
;    instructions for how to rebuild all the books and replay the the simple
;    examples discussed in the Friendly Introduction

; Search for the section headers above to find the beginning of each section
; below.

; =============================================================================
; A Friendly Introduction to Codewalker

; The events mentioned in the text below are taken from basic-demo.lsp.

; We have an operational semantics for the simple JVM-like machine M1.  It is
; contained in the file m1-version-3.lisp, which also contains all the necessary
; lemma development for M1 code proofs.

; The M1 machine has a stobj state with 4 fields

; field   accessor               updater

; pc      (rd :pc s)             (wr :pc v s)
; locals  (nth i (rd :locals s)) (wr :locals (update-nth i v (rd :locals s)) s)
; stack   (rd :stack s)          (wr :stack v s)
; program (rd :program s)        (wr :program v s)

; Note that the locals field is really an array accessed by nth and update-nth.
; So while the stobj has 4 fields we actually think of the state as having n+3
; ``components'': the pc, n independently readable/writable locals, the stack,
; and the program.  Except for initializing the state, we never write to the
; program field.  The locals are indexed, from 0, and we actually refer to them
; colloquially as ``registers'' and use the informal notation reg[i] below.

; The M1 machine has 9 simple instructions
; (ILOAD i)    push reg[i] on stack
; (ISTORE i)   pop stack into reg[i]
; (ICONST i)   push i on stack
; (IADD)       pop 2 items, add, and push answer
; (ISUB)       pop 2 items, subtract, and push answer
; (IMUL)       pop 2 items, multiply, and push answer
; (GOTO d)     increment pc by d (d may be negative)
; (IFEQ d)     pop stack and if item is 0, increment pc by d
; (HALT)       stop

; We use M1 because it is arithmetically simple: unbounded integers, no
; limits on the number of registers or the size of the stack, and only a few
; instructions.  We use the stobj version of M1 because stobjs are the most
; common paradigm for machine models.

; So consider the following program constant:

; (defconst *program1*
;   '((ICONST 1)  ; 0
;     (ISTORE 1)  ; 1  reg[1] := 1;
;     (ICONST 0)  ; 2
;     (ISTORE 2)  ; 3  reg[2] := 0;
;     (ICONST 1)  ; 4
;     (ISTORE 3)  ; 5  reg[3] := 1;
;     (ILOAD 0)   ; 6                         ; <--- loop
;     (IFEQ 14)   ; 7  if R0=0, goto 14+7;
;     (ILOAD 1)   ; 8
;     (ILOAD 0)   ; 9
;     (IMUL)      ;10
;     (ISTORE 1)  ;11  reg[1] := reg[0] * reg[1];
;     (ILOAD 2)   ;12
;     (ILOAD 0)   ;13
;     (IADD)      ;14
;     (ISTORE 2)  ;15  reg[2] := reg[0] + reg[2];
;     (ILOAD 0)   ;16
;     (ILOAD 3)   ;17
;     (ISUB)      ;18
;     (ISTORE 0)  ;19  reg[0] := reg[0] - reg[3];
;     (GOTO -14)  ;20  goto 20-14;            ; goto loop
;     (ILOAD 1)   ;21
;     (HALT)))    ;22  halt with reg[1] on top of stack;

; What does this program do?  What does it leave in reg[1]?  Reg[2]? On the
; stack?  These kinds of questions are answered by Codewalker.

; As a puzzle for the reader consider this: Why does it terminate?

; The ``what does it do?'' question is answered by def-semantics which
; invents an ACL2 function that returns the same final state as the program.
; This exposes the first big restriction on Codewalker: it only works for
; programs that terminate.  However, you can always run Codewalker on just a
; region of code (e.g., a straightline segment or a loop body) to
; ``understand'' what that part does.

; The ``what does it leave in some state component?'' question is answered by
; the def-projection command, which invents an ACL2 function that returns the
; final value of the given state component.  The projection facility operates
; on the output of def-semantics.  So you should always first run def-semantics
; on the code of interest and then ``project out'' the final values of selected
; components if def-semantics's answer is still too hard to understand.

; Def-semantics discovers the loops in the program and writes a function for
; each loop.  There is a loop starting at pc = 6 in our program above and
; def-semantics' function for that loop is named sem-6.

; The definition of sem-6, created by def-semantics, is shown below.  When
; def-semantics was run it was told it could assume that the state statisfies
; (hyps s) which is the ``good state'' invariant for M1.  We've deleted
; DECLAREs and other noise but included the entire logical part of the
; definition.

; (DEFUN SEM-6 (S)
;   (IF (AND (HYPS S)
;            (EQUAL (NTH 3 (RD :LOCALS S)) 1))
;       (IF (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;           (WR :PC 22
;               (WR :STACK (PUSH (NTH 1 (RD :LOCALS S))
;                                (RD :STACK S))
;                          S))
;           (SEM-6
;            (WR
;             :PC 6
;             (WR
;              :LOCALS
;              (UPDATE-NTH 0 (+ (NTH 0 (RD :LOCALS S))
;                               (- (NTH 3 (RD :LOCALS S))))
;                (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                                 (NTH 1 (RD :LOCALS S)))
;                  (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                   (NTH 2 (RD :LOCALS S)))
;                              (RD :LOCALS S))))
;              S))))
;       S))

; Notice that the function does not mention code, just basic operations on the
; state components manipulated by the code.  Notice also that we can just read
; from the ``base case'' that the final state has PC 22 and the final value of
; reg[1] is pushed on the stack.  However, it may be harder to understand what
; the final value of reg[1] is since reg[1] is modified as the function recurs.
; On the other hand, def-semantics invents a measure (not shown) that explains
; why the function -- and the code loop -- terminates.

; Another thing that def-semantics does is prove that its invented functions are
; correct.  In particular, it proves this:

; (defthm sem-6-correct
;   (implies (and (hyps s) (equal (rd :pc s) 6))
;            (equal (m1 s (clk-6 s))
;                   (sem-6 s))))

; This reveals another fact about def-semantics: it invents a second
; function, CLK-6, that counts how many M1 instructions are executed from the
; time the loop is entered to the HALT.  The theorem establishes that if the
; state satisfies the invariant and the initial pc is 6, then running the state
; for the number of steps specified by CLK-6 produces the very same state as
; SEM-6.  That is, SEM-6 really does what was promised.

; To explore what SEM-6 does to the registers, we can use def-projection.  If we
; project out the reg[1] component of the state produced by SEM-6 we get the
; following function.  Again, certain DECLAREs and other non-logical noise has
; been eliminated.

; (defun fn1-loop (r0 r1 r3)
;   (cond ((or (not (integerp r3))
;              (< r3 0)
;              (not (integerp r0))
;              (< r0 0)
;              (not (integerp r1))
;              (< r1 0))
;          0)
;         ((or (not (equal r3 1)) (equal r0 0))
;          r1)
;         (t (fn1-loop (+ -1 r0) (* r0 r1) 1))))

; Here are some immediate observations we can make about this function -- and
; thus about the code.

; (1) The new function does not take state s as an argument!  It just takes
; three values, r0, r1, and r3 -- which happen to be the initial values of
; reg[0], reg[1], and reg[3] respectively.  It assumes they are natural numbers
; -- it short-circuits to 0 if they're not.

; (2) We can immediately see that the final value of reg[1] does not depend on
; reg[2], since reg[2] (``r2'') is not mentioned above.

; (3) We see that if the hypotheses on r0, r1, and r3 are satisfied then the
; final value of r1 is just the product of the naturals from r0 down to 0.

; (4) R3 seems a bit irrelevant.  Its only role is to short-circuit the
; computation if it is not 1 upon entry.  Thereafter it is always 1.  But note
; that if R3 is not 1, this function doesn't correspond to the code!  The code
; loops by replacing R0 by R0 - R3.  But the function recurs by replacing R0 by
; R0 - 1.

; The def-projection command also proves this theorem:

; (defthm fn1-loop-correct
;   (implies (hyps s)
;            (equal (nth 1 (rd :locals (sem-6 s)))
;                   (fn1-loop (nth 0 (rd :locals s))
;                             (nth 1 (rd :locals s))
;                             (nth 3 (rd :locals s))))))

; which we can count as a fifth observation and which leads to another:

; (5) The final value of reg[1] after running sem-6 is what fn1-loop computes,
; given only the initial values of reg[0], reg[1], and reg[3].

; (6) Since we already know (from the theorem sem-6-correct, above) that sem-6
; produces the same state as running the code starting at pc = 6, we can put
; the two theorems together to conclude that fn1-loop computes the final value
; of reg[1] after running the code starting at pc = 6.

; Next we discuss what you must do to make def-semantics and def-projection produce
; such answers.  There are really four steps.

; Step 1: Decide what the independently readable/writeable state components in
; your model are, decide what you want the canonical expressions to be for
; those components, develop a collection of lemmas about your model for
; reducing finite-length runs of program segments to those terms, and develop
; the ``opener'' and ``seqential execution'' lemmas you'd need if you were
; doing code proofs about your model.  To see the lemmas actually proved about
; the M1 model here, see the tail end of the file m1-version-3.lisp which
; contains the most basic code proof lemmas, plus the lemmas in the encapsulate
; after (hyps s) is defined in the basic-demo.lsp script.

; Step 2: Tell the Codewalker utilities how to access the model.

; (def-model-api
;   :run M1                  ; the run function of the model
;   :svar S                  ; name of state variable
;   :stobjp T                ;  and whether it's a stobj
;   :hyps ((HYPS S))         ; invariant to assume about state
;   :step STEP               ; name of step function
;   :get-pc (LAMBDA (S) (RD :PC S))      ; how to fetch the pc
;   :put-pc (LAMBDA (V S) (WR :PC V S))  ; how to set the pc
;
;                            ; the ``drivers'' below specify how to
;                            ;  dive through updaters (and constructors)
;                            ; and their accessors
;   :updater-drivers (((UPDATE-NTH I :VALUE :BASE)
;                      (NTH I :BASE))
;                     ((WR LOC :VALUE :BASE)
;                      (RD LOC :BASE)))
;   :constructor-drivers nil
;                            ; list patterns that match each state component
;                            ;  and its inherent type under the :hyps.  See below.
;   :state-comps-and-types  (((NTH I (RD :LOCALS S)) (NATP (NTH I (RD :LOCALS S))))
;                            ((RD :STACK S)          (NATP-LISTP (RD :STACK S)))
;                            ((RD :PC S)             (NATP (RD :PC S))))
;
;   :callp  nil              ; recognizer fn for states with pc on call instruction
;   :ret-pc nil              ; how to fetch the return pc after a call
;   :returnp nil             ; recognizer for states with pc on return instruction
;
;   :clk+ binary-clk+        ; how to add two clocks
;   :name-print-base nil     ; base to use for pcs appearing in names
;                            ;  (2, 8, 10, or 16)
;
;                            ; how to generate variable names from state comps
;   :var-names (((RD :PC S) "PC")
;               ((NTH I (RD :LOCALS S)) "R~x0" I)
;               ((RD :STACK S) "STK"))
;   )

; The constructor drivers are generally unnecessary for stobj-based models.
; When might you need it?  Suppose your chosen canonical form for register
; updates is

; (wr :locals (cons new-r0 (cons new-r1 (cons ... (cd...dr (rd :locals s))))) s)

; instead of

; (wr :locals (update-nth 0 new-r0 (update-nth 1 new-r1 ... (rd :locals s))) s)

; Then you would need to tell def-semantics how to dive through conses and would
; add the element:

; ((cons a b) (car :base) (cdr :base))

; to :constructor-drivers in your API.  If your new states were constructed by
; (make-state pc locals stack program) expressions, instead of wr expressions,
; you'd need to add a tuple like

; ((make-state pc locals stack program)
;  (rd :pc :base) (rd :locals :base) (rd :stack :base) (rd :program :base))

; in addition to the cons tuple above.  Note the convention that :base denotes
; the location of the state argument in the accessor expressions.

; :Var-names is used in the generation of variable symbols to use in place of
; state components.  For example, Codewalker may need to generalize the state
; component (NTH 7 (REGS S)) and you may prefer for it to generate the variable
; name R7.  Technically, :var-names is always a function which maps a term to a
; string and that string is used as the root name of a new variable symbol.

; But as illustrated above, def-model-api supports the idea that :var-names may
; be a list of tuples, of the form (pattern fmt-string term_0 term_1 ...).  These
; are called ``var name rules.''  When such a list is provided, def-model-api
; actually generates a suitable lambda expression and sets :var-names to that
; function.

; The meaning of a var name rule is:

;   if a state component matching pattern [see caveat below] must be
;   generalized, then obtain the root string for the new variable by formatting
;   fmt-string under an alist binding #\0 to the value of term_0, #\1 to the
;   value of term_1, etc.  There may be no more than 10 term_i.  The evaluation
;   of the term_i is done with respect to an environment determined by the
;   substitution produced by matching the pattern with the state component.

;   Caveat: The substition produced by the match must satisfy two rules: (a)
;   The svar of the API can only be bound to itself -- thus if S is the svar,
;   then the pattern (NTH I (REGS S)) matches component (NTH '7 (REGS S)) but
;   does not match the term (NTH '7 (REGS ST)).  (b) Every other variable in
;   the pattern must be bound to a quoted constant.  Since the only variable
;   that may appear in a state component produced by Codewalker is svar,
;   neither of these restrictions matter much.  However, (b) insures that if
;   the term_i involve only the (non-svar) variables of the pattern, then it is
;   possible to evaluate the term_i under the substitution.

; Step 3: Issue the command to explore your code.  To do this you have to
; decide at what pc exploration is to begin and, perhaps, the ``focus region''
; to be explored, a root-name to use in the generation of the clock and
; semantic function names, additional invariant :hyps to extend those in the
; API, and some annotations to modify the otherwise automatically generated
; events.

; The focus region is specified by a predicate that takes the pc and returns t
; or nil depending on whether the pc is in the region you care about.  That's
; the :focus-regionp argument mentioned below.  It might be used if you want to
; simulate through a fixed region or stop when you encounter certain
; instructions that def-semantics doesn't ``understand.''  (Codewalker must be
; able to follow the flow of control and if an instruction sets the pc to some
; function of the data, def-semantics will signal an error.)

; In this example, we defined the state invariant to be:

; (defun hyps (s)
;   (declare (xargs :stobjs (s)))
;   (and (sp s)
;        (natp (rd :pc s))
;        (< (rd :pc s) (len (rd :program s)))
;        (< 16 (len (rd :locals s)))
;        (natp-listp (rd :locals s))
;        (natp-listp (rd :stack s))))

; Note that it makes no requirement on the program component of s, so the code
; in this state s could be anything.  We'll show below how this invariant is
; strengthened so that we have a particular program in the state.

; In basic-demo.lsp you will see that in order to constrain the state
; to contain our *program1* above, we defined:

; (defun program1p (s)
;   (declare (xargs :stobjs (s)))
;   (equal (rd :program s) *program1*))

; and then strengthened the :hyps of the API when we issued the
; following command to explore the code:

; (def-semantics
;  :init-pc 0
;  :focus-regionp nil        ; optional - to limit the region explored
;  :root-name nil            ; optional - to change the fn names chosen
;  :hyps+ ((program1p s))    ; optional - to strengthen the :hyps of API
;  :annotations nil          ; optional - to modify output generated
;  )

; We could have used:

;  :hyps+ ((equal (rd :program s) *program1*))

; in the def-semantics command but as you'll see from looking at
; basic-demo.lsp we introduced program1p, proved some lemmas about it, and
; disabled it.  Otherwise, where you see (program1p s) in the derived functions
; below you would see *program1*.  When the program in question is very large,
; you might prefer the approach used here.

; Def-semantics explores the state satisfying the extended invariant starting
; at the :init-pc 0.  It discovers the loop at pc = 6 and ultimately defines
; four functions, clk-6, clk-0, sem-6, and sem-0, and two defthms, one stating
; the correctness of sem-6 (wrt the clock function clk-6) and one the
; correctness of sem-0 (wrt clk-0).  If we wanted to make the function names
; reflect the fact that they were generated from *program1* we could have
; used:

;  :root-name "PROGRAM-1-PC"  ; or just the symbol program-1-pc

; in the def-semantics above and then the names would be clk-program-1-pc-0,
; sem-program-1-pc-0, etc.

; Def-semantics actually prints a lot of stuff as it goes.  It also often
; fails!  Some of its error messages make supposedly helpful suggestions as to
; what's ``wrong.''  Often your response will be to prove more lemmas because
; things aren't being reduced to the canonical forms.  Another response might
; be to restrict the focus region or strengthen the invariant so as to avoid
; certain cases.  Another common failure is the inability to guess why a
; function (loop) terminates, in which case the right response might be to add
; an :annotation to tell it the :measure for the troublesome function or,
; instead of addining an :annotation, to teach the Terminatricks package a new
; measure pattern.  Sometimes you can figure out what you need to do by reading
; the checkpoints of failed proofs.  If you're still lost, you might try
; (assign acl2::make-event-debug t) and look at that output!

; Sometimes, if def-semantics generates definitions and theorems but cannot
; admit them, the best response is to take the ``bad'' definitions and theorems
; it was trying to admit and use them as starting points for your own
; definitions and theorems.  In that case, you'd just comment out the original
; def-semantics event in your evolving script and substitute the ``bad''
; definitions and theorems -- and then hand-edit them so they are correct and
; admissible.

; But when def-semantics succeeds, here is how you can get a sketch of what it
; did:

; (pcb :x)
;    d       8:x(DEF-SEMANTICS :INIT-PC 0 ...)
;                (TABLE ACL2::ACL2-DEFAULTS-TABLE     ; update tables used
;                       :VERIFY-GUARDS-EAGERNESS ...) ; by Terminatricks
;                (TABLE ACL2::MEASURE-PATTERNS :LIST ...)
;  L d           (DEFUN CLK-6 (S) ...)                ; clock fn for pc=6
;                (TABLE ACL2::MEASURE-PATTERNS :LIST ...)
;  L d           (DEFUN CLK-0 (S) ...)                ; clock fn for pc=0
;  L             (DEFUN SEM-6 (S) ...)                ; semantic fn for pc=6
;  L             (DEFUN SEM-0 (S) ...)                ; semantic fn for pc=0
;                (DEFTHM SEM-6-CORRECT ...)           ; correctness for pc=6
;                (IN-THEORY (DISABLE CLK-6))
;                (DEFTHM SEM-0-CORRECT ...)           ; correctness for pc=0
;                (IN-THEORY (DISABLE CLK-0))

; Note: The output above was correct as of May, 2014.  It may change.  In
; addition, for simplicity we sometimes ``prettyify'' the output shown in these
; comments, when in fact the events generated are in fully translated form.
; The output shown here is highly suggestive of what is actually produced!
; Re-play basic-demo.lsp and inspect the output to see EXACTLY what is
; produced.

; Then you can print out the definitions and theorems if you so choose, e.g.,
; with:

; (pe 'clk-0)
; (DEFUN CLK-0 (S)
;   (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
;   (DECLARE (XARGS :STOBJS (S)))
;   (PROG2$ (ACL2::THROW-NONEXEC-ERROR 'CLK-0 (LIST S))
;           (IF (AND (HYPS S) (PROGRAM1P S))
;               (CLK+ 6
;                     (CLK-6
;                      (WR :PC 6
;                       (WR :LOCALS (UPDATE-NTH 1 1
;                                    (UPDATE-NTH 2 0
;                                     (UPDATE-NTH 3 1
;                                                 (RD :LOCALS S))))
;                        S))))
;               0)))

; (pe 'sem-0-correct)
; (DEFTHM SEM-0-CORRECT
;   (IMPLIES (AND (HYPS S)
;                 (PROGRAM1P S)
;                 (EQUAL (RD :PC S) 0))
;            (EQUAL (M1 S (CLK-0 S))
;                   (SEM-0 S))))

; Recall that after def-semantics we can project out selected components.  Here
; is how we project out the final value of reg[1] from the loop semantics,
; sem-6.

; (def-projection
;   :new-fn FN1-LOOP
;   :projector (nth 1 (rd :locals s))
;   :old-fn SEM-6
;   :hyps+ ((program1p s))
;   )

; The function name ``FN1-LOOP'' was chosen by the user to be memorable.  It is
; meant to suggest ``the function that computes the final value of reg[1]
; starting from the loop.''  The function fn1-loop returns the (nth 1 (rd
; :locals s)) of the state s obtained by running sem-6.  That function could be
; defined trivially as:

; (defun fn1-loop (s) (nth 1 (rd :locals (sem-6 s))))

; but that is not what def-projection does!  Instead, it does a ``cone of
; influence'' analysis to identify which state components contribute to the
; final value of the one of interest and tracks how those components change as
; sem-6 recurs.

; To see what a successful def-projection did, use:

; (pcb :x)
;            9:x(DEF-PROJECTION FN1-LOOP (NTH 1 #) ...)
;  L             (DEFUN FN1-LOOP (R0 R1 R3) ...)
;                (DEFTHM FN1-LOOP-CORRECT ...)

; You may inspect the details with:

; (pe 'fn1-loop)
; (DEFUN FN1-LOOP (R0 R1 R3)
;   (DECLARE
;    (XARGS :MEASURE (ACL2::DEFUNM-MARKER (ACL2-COUNT R0))
;           :WELL-FOUNDED-RELATION O<))
;   (COND ((OR (NOT (INTEGERP R3))
;              (< R3 0)
;              (NOT (INTEGERP R0))
;              (< R0 0)
;              (NOT (INTEGERP R1))
;              (< R1 0))
;          0)
;         ((OR (NOT (EQUAL R3 1)) (EQUAL R0 0))
;          R1)
;         (T (FN1-LOOP (+ -1 R0) (* R0 R1) 1))))

; and

; (pe 'fn1-loop-correct)
; (DEFTHM FN1-LOOP-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '1 (RD ':LOCALS (SEM-6 S)))
;                   (FN1-LOOP (NTH '0 (RD ':LOCALS S))
;                             (NTH '1 (RD ':LOCALS S))
;                             (NTH '3 (RD ':LOCALS S))))))

; We claim that the definition of FN1-LOOP as derived by def-projection makes
; it easy to understand what the code is doing to compute the final value of
; reg[1].

; In answering the puzzle mentioned earlier: it is also easy to see why the
; loop terminates.  It counts R0 down to 0 by subtracting 1 from it.  But the
; code in *program1* (pc = 19) actually subtracts reg[3] from it.  However,
; def-semantics detects that the assignment at pc = 5 sets reg[3] to 1 and that
; it is unchanged throughout the loop, so it suffices to model the program as
; subtracting 1.

; We can go on and project the value of reg[1] starting from pc = 0, with:

; (def-projection
;   :new-fn FN1
;   :projector (nth 1 (rd :locals s))
;   :old-fn SEM-0
;   :hyps+ ((program1p s))
;   )

; We see:

; (pe 'fn1)
; (DEFUN FN1 (R0)
;   (IF (OR (NOT (INTEGERP R0)) (< R0 0))
;       0
;       (FN1-LOOP R0 1 1)))

; and

; (pe 'fn1-correct)
; (DEFTHM FN1-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '1 (RD ':LOCALS (SEM-0 S)))
;                   (FN1 (NTH '0 (RD ':LOCALS S))))))

; We might wish to establish that fn1 is actually factorial.  We can do that
; conventionally:

; (defun ! (n)
;   (if (zp n)
;       1
;       (* n (! (- n 1)))))

; (defthm fn1-loop-is-!-gen
;   (implies (and (natp r0) (natp r1))
;            (equal (fn1-loop r0 r1 1)
;                   (* r1 (! r0)))))

; (defthm fn1-is-!
;   (implies (natp r0)
;            (equal (fn1 r0)
;                   (! r0))))

; And because of all we know, we can immediately relate it to the
; result of running the code:

; (defthm reg[1]-of-code-is-!
;   (implies (and (hyps s)
;                 (program1p s)
;                 (equal (rd :pc s) 0))
;            (equal (nth 1 (rd :locals (m1 s (clk-0 s))))
;                   (! (nth 0 (rd :locals s))))))

; We can, also or instead, project reg[2]:

; (def-projection
;   :new-fn FN2-LOOP
;   :projector (NTH 2 (RD :LOCALS S))
;   :old-fn SEM-6
;   :hyps+ ((program1p s))
;   )

; (def-projection
;   :new-fn FN2
;   :projector (NTH 2 (RD :LOCALS S))
;   :old-fn SEM-0
;   :hyps+ ((program1p s))
;   )

; and thus learn that from the perspective of its effect on reg[2], the loop
; computes the sum of the numbers below reg[0]:

; (pe 'fn2-loop)
; (DEFUN FN2-LOOP (R0 R2 R3)
;   (DECLARE
;    (XARGS :MEASURE (ACL2::DEFUNM-MARKER (ACL2-COUNT R0))
;           :WELL-FOUNDED-RELATION O<))
;   (COND ((OR (NOT (INTEGERP R3))
;              (< R3 0)
;              (NOT (INTEGERP R0))
;              (< R0 0)
;              (NOT (INTEGERP R2))
;              (< R2 0))
;          0)
;         ((OR (NOT (EQUAL R3 1)) (EQUAL R0 0))
;          R2)
;         (T (FN2-LOOP (+ -1 R0) (+ R0 R2) 1))))

; (pe 'fn2)
; (DEFUN FN2 (R0)
;   (IF (OR (NOT (INTEGERP R0)) (< R0 0))
;       0
;       (FN2-LOOP R0 0 1)))

; (pe 'fn2-correct)
; (DEFTHM FN2-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '2 (RD ':LOCALS (SEM-0 S)))
;                   (FN2 (NTH '0 (RD ':LOCALS S))))))

; We could prove reg[2] is the sum of the naturals from reg[0] down, in the
; conventional manner and immediately relate it to the code:

; (defthm fn2-loop-is-sum-gen
;   (implies (and (natp r0) (natp r2))
;            (equal (fn2-loop r0 r2 1)
;                   (+ r2 (/ (* r0 (+ r0 1)) 2)))))

; (defthm fn2-is-sum
;   (implies (natp r0)
;            (equal (fn2 r0)
;                   (/ (* r0 (+ r0 1)) 2))))

; (defthm reg[2]-of-code-is-sum
;   (implies (and (hyps s)
;                 (program1p s)
;                 (equal (rd :pc s) 0))
;            (equal (nth 2 (rd :locals (m1 s (clk-0 s))))
;                   (/ (* (nth 0 (rd :locals s))
;                         (+ (nth 0 (rd :locals s)) 1))
;                      2))))

; If we wanted to explore a different M1 program would could define, say,
; program2p in a way analogous to program1p above, keep the M1 API as is, and
; issue def-semantics and def-projection commands about program2p.

; To replay this demo you will need to have certified the Codewalker books.
; See the section How to Certify Codewalker.  But once they are certified, you
; can replay this demo by starting ACL2 and doing:

; (ld "basic-demo.lsp" :ld-pre-eval-print t)

; You can then inspect the output or query the ACL2 data base.  By the way, the
; ld above leaves you in the "ACL2" package, but all the definitions mentioned
; above are in the "M1" package and to poke around after the ld you should do
; (in-package "M1").

; If you intend to use Codewalker, we recommend that you first try your hand at
; a few examples.  We strongly recommend you use the M1 model.  You can find
; many examples of simple M1 programs in the ACL2 Community Books directory
; models/jvm/m1.  See the README file there for a list of files containing
; simple programs.

; =============================================================================
; Reference Guide to Def-Model-API, Def-Semantics, and Def-Projection

; After presenting the reference guide for def-model-api, we discuss the
; requirements on the ACL2 data base usually necessary for the other two
; commands to succeed.  Then we provide the reference guides for def-semantics
; and def-projection.  The subsections of this section are:

; Example/General Form of Def-Model-API
; About the ACL2 Data Base
; Example/General Form of Def-Semantics
; Example/General Form of Def-Projection

; All of the arguments to all three of the commands are presented in keyword
; form.  Some arguments are optional, as noted.  We present example settings
; for each keyword and then describe the general form and interpretation.

; The commands themselves generally pre-check the appropriateness of their
; arguments before attempting to generate tables, semantic functions, and
; projections.  However, the commands do not necessarily pre-check all of the
; appopriateness conditions mentioned here.  If the conditions described below
; are violated by your settings you will likely get a pre-check error message
; but sometimes the command will fail in less obvious ways.  If it turns out
; that these failures are difficult to debug, we might be able to strengthen
; the pre-checks or clarify the error messages.

; -----------------------------------------------------------------------------
; Example/General Form of Def-Model-API

; (def-model-api

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :run RUN               ; the general form:

;  function symbol or lambda expression from a machine state and natural number
;  to a state.  If, for example, your actual ``run'' function takes its
;  arguments in the other order you could write: (lambda (s n) (run n s)).
;  This is a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :svar S

;   variable symbol denoting the machine state.  This is a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :stobjp nil

;   flag indicating whether svar is a stobj.  This is a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :hyps ((HYPS s))

;   invariant on state, expressed as a list of terms, in svar, implicitly
;   conjoined.  Thus, the empty list denotes the vacuous hypothesis T.  The conjunction
;   of hyps should be an invariant preserved by the run function (at least on
;   the states and region of code of interest).  This is an optional field in
;   the sense that it has a sensible default value: nil, the conjunction over
;   which results in the invariant T.

;   However, it is overwhelmingly likely that you will need to provide :hyps to
;   characterize the expected ``shape'' of state and perhaps the contents of
;   the ``program'' part of the state to be analyzed.  The def-semantics and
;   def-projection commands provide a similar argument named :hyps+ that allows
;   you to add conjuncts to the :hyps in the API.  This feature allows you to
;   specify an API that is independent of any particular program and then
;   further constrain the state to contain the programs of interest each time
;   you create a semantic function or projection.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :step STEP

;   function symbol or lambda from state to state.  This is a required field.

;   Your :run and :step functions must satisfy

;   Constraint:
;   (run s n) = (if (zp n) s (run (step s) (- n 1))),

;   where run and step are the values of the :run and :step fields.  It is
;   possible your model does not adhere to this constraint and you will have to
;   re-define it.  Codewalker does not try to prove this constraint -- it just
;   may fail to work if it is violated.  If Codewalker reports that it worked,
;   i.e., that the defuns it created were admitted and the theorems it created
;   were proved, then it did work insofar as its ``claims'' are formally
;   understood.

;   Your model may satisfy Constraint even though your run may not be defined
;   exactly in this syntactic form or you have not explicitly defined a step
;   function in your own development of the model.

;   For example, if your run function is defined like this:

;   (defun run (s n)
;    (if (zp n)
;        s
;        (if (error-statusp s)
;            s
;            (run (do-inst (next-inst s) s)
;                 (- n 1)))))

;   your setting for the :step function should be

;   (lambda (s)
;     (if (error-statusp s)
;         s
;         (do-inst (next-inst s) s))).

;   which makes the constraint between the :run and :step functions provable,
;   assuming that (error-statusp s) implies that (do-inst (next-inst s) s) = s.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :get-pc PC

;   function symbol or lambda expression from state to program counter of
;   state.  This is a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :put-pc !PC

;   function symbol or lambda expression from new pc, v, and state, s, to a
;   state with :get-pc v and otherwise like s.  This is a required field.

;   If, for example, the pc of your model were (nth 3 s) and your convention
;   was to update it with update-nth, then the appropriate settings for :get-pc
;   and :put-pc would be:

;     :get-pc (lambda (s) (nth 3 s))
;     :put-pc (lambda (x s) (update-nth 3 x s))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :updater-drivers
;   (((UPDATE-NTH I :VALUE :BASE) (NTH I :BASE))
;    ((!PC :VALUE :BASE)          (PC :BASE))
;    ((!REGS :VALUE :BASE)        (REGS :BASE))
;    ((!MEM :VALUE I BASE)        (MEM I :BASE)))

;   list of tuples (updater-term accessor-term) listing every updater and the
;   corresponding accessor used in the simplified canonical state expressions
;   produced from the model.  The keyword :VALUE marks the slot in the updater
;   holding the new value, the keyword :BASE marks the slot holding a nest of
;   other updaters, constructors (see :constructor-drivers, below), or the
;   state.  Some nest of these expressions (possibly mixed with nests of
;   constructors) around the model's :svar should match the canonical form of
;   states produced by ACL2's simplifier on the model.  All those accessor
;   nests should be orthogonal in the sense that updating the value of one
;   accessor nest should not change the value of a different nest.

;   This is a required field, unless the simplified canonical state expressions
;   from the model are expressed entirely as constructors (see next field).
;   See also Appendix A.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :constructor-drivers
;   (((CONS A B)           (CAR :BASE) (CDR :BASE))
;    ((MAKE-STATE A B C D) (PC :BASE) (REGS :BASE) (MEM :BASE) (PROGRAM :BASE)))

;   list of tuples of the form (constructor accessor-term_1 ...
;   accessor-term_k) listing every constructor and the corresponding accessor
;   terms used in the simplified canonical state expressions produced from the
;   model.  The constructor expressions must list distinct variables in their
;   slots and the accessors are listed in the order of their corresponding
;   slots of the constructor.  The keyword :BASE marks the slot in the
;   accessors where nests of constructors, updaters, or the state variable may
;   appear.  Some nest of these expressions (possibly mixed with nests of
;   updaters) around the model's :svar should match the canonical form of
;   states produced by ACL2's simplifier on the model.  All those accessor
;   nests should be orthogonal in the sense that updating the value of one
;   accessor nest should not change the value of a different nest.

;   This is a required field, unless the simplified canonical state expressions
;   from the model are expressed entirely in the updater paradigm.

;   The example setting above is unlikely in light of the :updater-drivers
;   above: the canonical state is most likely produced either by an updater or
;   a constructor, not both.  Updaters and constructors on other data
;   structures (e.g., update-nth and cons) used within state expressions is not
;   unusual.  See also Appendix A.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :state-comps-and-types
;   (((NTH I (REGS S))   (NATP (NTH I (REGS S))))
;    ((STACK S)          (LIST-OF-NATSP (STACK S)))
;    ((PC S)             (NATP (PC S))))

;   list of tuples of the form (comp type), where both comp and type are terms.
;   The state variable, svar (the contents of the :svar field of the API), must
;   occur in comp and is treated specially.  Furthermore, unless type is T, comp
;   must occur in type, the only use of the :svar in type must be its
;   occurrence in the comp subterm of type, and every other variable in type
;   must occur in comp. This is a required field if def-projection is to be
;   used.

;   This list is used to determine the ``state components'' that def-projection
;   can generalize to produce functions independent of state.  A subexpression,
;   x, of a canonical state expression is a ``state component'' precisely if
;   there is a comp listed here such that comp matches x under the restriction
;   that the svar in comp is bound to itself (i.e., to the contents of the
;   :svar field) and every other variable in comp is bound to a constant.  For
;   example, given the comps above, the term (NTH 7 (LOCALS S)) is a state
;   component, but (NTH (+ U V) (LOCALS S)) and (NTH 7 (LOCALS (FN S))) are
;   not.

;   The type of each state component is as specified by the corresponding
;   instance of the type expression listed.  For example, the type of state
;   component (STACK S), as specified above, is (LIST-OF-NATSP (STACK S)).
;   Thus, if def-projection generalizes (STACK S) to some new variable STK,
;   then it will add the hypothesis that (LIST-OF-NATSP STK).  Type information
;   about the new variables is often crucial to insuring that projected
;   functions terminate.  If you want no type information added when a state
;   component is generalized, use the type term T.  Otherwise, the type term
;   should (a) contain an occurrence of the comp term, (b) should not use svar
;   any place but in the comp term, and (c) should use no variables other than
;   those in the comp term.

;   See also Appendix A.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :callp                          ; (*** this feature not yet implemented ***)
;   (LAMBDA (S) (MEMBER-EQ (OPCODE (NEXT-INSTR S)) '(JSR CALL)))

;   function symbol or lambda expression recognizing when the pc in state
;   points to a call instruction.  This is a required field if subroutine calls
;   are to be explored.


; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :ret-pc                         ; (*** this feature not yet implemented ***)
;   (TOP (STACK S))

;   term in svar indicating where the return pc is stored after a call.  This
;   is a required field if subroutine calls are to be explored.


; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :returnp                        ; (*** this feature not yet implemented ***)
;   (LAMBDA (S) (EQ (OPCODE (NEXT-INSTR S)) 'RET))

;   function symbol or lambda expression recognizing when the pc in state
;   points to a return.  This is a required field if subroutine calls are to be
;   explored.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :clk+ BINARY-CLK+

;   function symbol or lambda expression for adding together two ``clocks''
;   (natural numbers).  This is a required field.

;   Logically this function is just BINARY-+ (or a version of it that coerces
;   arguments to naturals), but most code proof lemma configurations use a
;   special symbol so that clock expressions are not subjected to the same
;   canonicalization rules as arithmetic expressions.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :name-print-base 16

;   the print base used for the pc when the pc is part of the name of an
;   automatically generated function.  The :name-print-base must be 2, 8, 10, or
;   16.  This is an optional field which defaults to 10.

;   For example, the name generated for the semantic function derived starting
;   at pc 123 is one of the following, depending on the :name-print-base:

;    2   SEM-B1111011
;    8   SEM-O173      [``O'' as in ``Octal'']
;   10   SEM-123
;   16   SEM-X7B

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :var-names
;   (((PC S)             "PC")    ; general form: a function name, a lambda-
;    ((NTH I (REGS S)) "R~x0" I)  ; expression, or as shown here, a list of
;    ((STACK S)          "STK")   ; tuples of the form
;    (:OTHERWISE         "X"))    ; (pattern fmt-string term_0 term_1...)

;   a function name, lambda expression or list of tuples used to produce the
;   variable name for a given state component (see :state-comps-and-types
;   above).  Roughly speaking, whatever legal value is provided, the :var-names
;   field allows us to map a state component term into a msg (as handed by fmt
;   and related ACL2 printing functions) and hence into a string to use as the
;   root name for the variable used to generalize that state component.

;   This is an optional field, but if left unspecified all generated variable
;   names are based on the "NO-VAR-NAME-STRING", so that the formals of any
;   projection will be NO-VAR-NAME-STRING, NO-VAR-NAME-STRING-1,
;   NO-VAR-NAME-STRING-2, etc.  If you have provided :var-names in your API
;   your will presumably be surprised to see such ugly names!  By looking at
;   the correctness theorem for the projection (the correctness theorem for a
;   projection function named fn has the name fn-CORRECT) you will be able to
;   see the state components for which your :var-names setting suggested no
;   sensible string.

;   As noted above, the :var-names field may be a function symbol, lambda
;   expression, or a list of tuples.  The third form, a list of tuples, is
;   illustrated above and discussed below because it is probably the most
;   common form.  See Appendix A for a discussion of the function/lambda case
;   and fancier uses of the list of tuples form.  In all cases, given a state
;   component x, :var-names determines a string which is used to generate a
;   unique variable symbol in the same symbol package as the :package-witness
;   of the API.

;   The general handling of (pattern fmt-string term_0 ...)  is as follows:
;   Pattern must be a term, fmt-string is a string suitable for printing with
;   fmt, the term_i must be terms involving only the non-:svar variables in
;   pattern, and there may be no more than 10 term_i.  To use such a list of
;   tuples to generate a msg (and hence a string): Each tuple is considered in
;   turn and the first one to succeed produces the string to be used.  Match
;   the pattern in the current tuple against a state component term to be
;   generalized.  (If the patttern is :OTHERWISE, consider it matched with the
;   empty substitution alist.)  If the match is successful, this tuple
;   succeeds; else it fails.  The match for a successful tuple binds all the
;   variables in the pattern (except the :svar) to constants; it binds the
;   :svar to itself.  Create the msg pair as with (msg fmt-string term_0 ...),
;   except evaluate the term_i under the alist created by the match (see note
;   immediately following).  Then print the resulting msg to a string to obtain
;   the root name of the variable symbol to be used in place of the matched
;   state component term.  [Note: technically, the alist produced by the match
;   binds the (non-svar) variables to quoted constants but the evaluation of
;   the term_i is done under an alist binding those variables to the unquoted
;   constants.]

;   For example, recall the list of tuples presented above:

;   (((PC S)             "PC")
;    ((NTH I (REGS S)) "R~x0" I)
;    ((STACK S)          "STK")
;    (:OTHERWISE         "X"))

;   where the :svar is S.  The root string generated for the state component
;   (PC S) is "PC".  The root string generated for (NTH '3 (REGS S)) is "R3"
;   and the root string for (NTH '12 (REGS S)) is "R12".  The root string for
;   (STACK S) is "STK".  The root string for any state component not matching
;   one of the four patterns in the list is "X".  In all cases, the variable
;   name is made unique, if necessary, by appending a hyphen and a numeric
;   suffix.  So if there are three state components to be generalized and none
;   match any of the given patterns, the variable symbols X, X-1, and X-2 are
;   used.

;   Suppose terms like (NTH '123 (MEM S)) were state components in our API
;   and that we added this tuple to the list above (and made sure to place it
;   before the :OTHERWISE tuple):

;   ((NTH I (MEM S))  "WORD-~x0-BYTE-~x1" (floor I 8) (mod I 8))

;   then the string generated for (NTH '123 (MEM S)) would be "WORD-15-BYTE-3"
;   because 123 = 15*8 + 3.

;   See also Appendix A.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :package-witness nil

;   a symbol used to determine the package of every function, variable, and
;   event name created by Codewalker.  This is an optional field.  If not
;   provided, the :svar symbol is used.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; (end of keyword arguments for def-model-api)
;  )

; Def-model-api translates all the alleged terms involved in the arguments and
; pre-checks most of the syntactic conditions.  Conditions not checked but
; violated, such as failure to supply a well-formed fmt string or to supply
; bindings for all of the tilde-variables in some fmt string in :var-names,
; will signal errors either when def-semantics or def-projection is invoked.
; If def-model-api detects no errors, it stores the results in three tables:

; (table acl2::model-api)                   ; used by Codewalker
; (table acl2::generalized-updater-drivers) ; used by Terminatricks
; (table acl2::constructor-drivers)         ; used by Terminatricks

; -----------------------------------------------------------------------------
; About the ACL2 Data Base

; Before any def-semantics or def-projection commands can succeed, you must
; be sure that the ACL2 lemma data base is configured for code proofs about the
; functions used in your model API.  Def-model-api does not check the
; configuration of the ACL2 data base!  Attempting to use def-semantics or
; def-projection in the absence of a suitable data base will likely fail.  Some
; failures may be resource exhaustion, if for example, the model is being
; expanded too readily by rewriting.  Other failures will print terms or
; Codewalker data structures containing terms that will ``suggest'' the missing
; lemmas in the way that the informed ACL2 user uses ``The Method'' to find
; lemmas.

; If we let run, step, hyps, and clk+ be the contents of the corresponding
; fields of the API, then the lemmas to which we refer include:

; * lemmas to canonicalize terms produced by simplifying step.  These include
;   lemmas often referred to as ``read-over-write'' and ``write-over-write'' --
;   lemmas that allow the rewriter to recover the symbolic value of a state
;   component from a symbolic state to which some modifications have been made,
;   and lemmas that allow the rewriter to ignore redundant or overwritten
;   writes.  Typically these lemmas also canonicalize arithmetic expressions
;   and other theories arising from the step function.  All of your state
;   components (as identified by the various fields in the API) should be in
;   the chosen canonical form.

; * lemmas, sometimes called ``step opener'' lemmas, that prevent step from
;   expanding until and unless the next instruction can be adequately decoded.
;   Typically, the step function is a big case split on the opcode of the next
;   instruction and if, for example, the opcode of the next instruction cannot
;   be determined by rewriting, then expanding the step function on successive
;   instructions produces a combinatoric explosion.  This is normally solved by
;   having one or more lemmas that force step to expand when syntactic
;   conditions are right and then disabling step.

; * the ``sequential execution'' lemma that states that
;   (run s (clk+ i j)) is (run (run s i) j).  Typically, clk+ is disabled in
;   the data base so that arithmetic canonicalization does not apply to it.

; * lemmas that establish the invariance of hyps under step and run.

; All subsequent def-semantics and def-projection commands are done relative to
; the most recent settings of these tables.  Thus, you may invoke def-model-api
; repeatedly in the same session to change or debug your settings.  However,
; functions derived under one API are unlikely to be compatible with those
; derived under another API.  For example, do not expect automatic success if
; you produce a semantic function under one API and then compose it with a
; function derived under another, or if you try to project it under a different
; API.

; -----------------------------------------------------------------------------
; Example/General Form of Def-Semantics

; Def-semantics, described below, explores all reachable code from a given pc
; and within a specified focus region.  It detects and explores loops.  Its
; non-erroneous output is a sequence of defun-like events defining clock and
; semantic functions followed by a sequence of defthms proving those functions
; correct with respect to the code and semantics.  The ``defun-like'' events
; are typically DEFUNM-NX events -- that is, Terminatricks is responsible for
; guessing a measure (hence the ``M'' in ``DEFUNM...'') and they are declared
; non-executable (``-NX'') because their bodies do not necessarily follow the
; syntactic rules on single-threaded objects (since their bodies are derived by
; simplification).

; (def-semantics

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :init-pc 0

;  the pc at which exploration is to start; the value is not translated.  When
;  def-semantics uses this value as a term it embeds it in a QUOTE.  This
;  technicality is unimportant for models with numeric pcs since quoted numbers
;  evaluate to themselves.  But if the model uses a structured pc, e.g., (FOO
;  . 5), perhaps meaning instruction 5 of subroutine FOO, and one wants the
;  analysis to start at that location, then write:

;     :init-pc (FOO . 5)

;  and DO NOT WRITE

;     :init-pc '(FOO . 5)

;  This is a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :focus-regionp nil

;  a function or lambda expression that maps a pc to a Boolean value.
;  Def-semantics explores all reachable code from :init-pc within the region
;  allowed by :focus-regionp.  When this predicate evaluates to nil on a pc
;  while def-semantics is exploring a piece of code, exploration of that branch
;  stops -- so the resulting semantic function will produce a state for that
;  branch that is ready to execute the first instruction outside the focus
;  region.  The :focus-regionp predicate can be used to limit def-semantics to
;  a particular region of code, as in the setting:

;  (lambda (pc) (and (<= 0 pc) (<= pc 100)))

;  and/or to prevent def-semantics from causing an error because control from
;  an instruction at a certain pc cannot be determined.  For example, if the
;  instruction at pc 53 sets the next pc to some computed value, then
;  def-semantics would signal an error if that instruction is reached.  To
;  prevent that instruction from being reached one could exclude it from the
;  :focus-regionp, as with the setting:

;  (lambda (pc) (and (<= 0 pc) (<= pc 100)
;                    (not (equal pc 53))))

;  If a function symbol is used for :focus-regionp, it may be a :program mode
;  function.  This field is optional.  If not supplied, the default value is
;  (lambda (pc) t).

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :root-name PROG-A

;  A symbol or string used as part of the names of the functions created by
;  def-semantics.  The names all have the form CLK-<root>-<pc> and
;  SEM-<root>-<pc>, where <root> is derived from :root-name and <pc> is the pc
;  at which exploration for this function started.  For example, with the
;  settings used here, the names of two of the functions defined would be
;  CLK-PROG-A-0 and SEM-PROG-A-0.  (Additional names would be defined if the
;  reachable region involves loops.)  If root-name is nil, the empty string is
;  used, so the generated names would be CLK-0 and SEM-0.  If root-name is any
;  other symbol, the symbol-name string of the root-name is used, with a hyphen
;  tacked on to the end if one is not already there.  Otherwise, root-name must
;  be a string and it is likewise extended with a hyphen if need be.  All
;  generated names are in the package of the :package-witness of the API.

;  This is an optional field.  If :root-name is not supplied, the empty string
;  is used.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :hyps+ nil

;  A list of terms to be conjoined to the :hyps of the API while doing this
;  def-semantics.  The :hyps of the API are not permanently extended, so
;  def-projections of functions derived by this def-semantics are likely to
;  require the same :hyps+ extension.

;  Note that you cannot ``override'' the :hyps of the API, only conjoin new
;  ones!  If for example, the :hyps of the API say that the machine has 8
;  registers and you used :hyps+ to ``extend'' it to say that there are 16
;  registers, you would in fact have contradictory hypotheses in the extended
;  API and anything could be derived and proved correct!

;  Perhaps the most common use of :hyps+ is to constrain the contents of the
;  state dealing with the program being explored.  Otherwise, it would be
;  impossible to determine the ``next instruction'' with enough specificity to
;  interpret it.  The exact form of this characterization depends on the
;  model of course.  The M1 model has a particular component, (program s),
;  containing the instructions to be executed, the JVM model has (class-table
;  s) containing a structure specifying classes and methods and their bytecode
;  instructions, and the X86 model has a read/write/execute memory but
;  typically devotes a region of memory to execute-only programs.  In all
;  cases, the most common way to characterize the program space is to include a
;  conjuct asserting that the program area is equal to some constant list of
;  instructions or bytes to be interpreted as instructions.  The question is
;  whether this assertion is included in the :hyps of the API or is part of the
;  :hyps+ of def-semantics.  The answer is up to you and depends on whether you
;  intend to use the API to explore only one particular program or to explore
;  various programs that could be loaded into the machine.  If the former,
;  making the constraint part of the API's :hyps makes sense because then that
;  API contains everything you need to use def-semantics.  If the latter, it is
;  better to put the constraint in the :hyps+ of each def-semantics so that the
;  API is program-independent and can be re-used over and over as you explore
;  different programs on that machine.

;  The :hyps+ extension of the API's :hyps is used by def-semantics as the
;  top-level test on the incoming state to the derived semantic function; if
;  those extended :hyps are violated, the derived function is defined to be a
;  no-op returning the same state.  These tests can affect the admissibility of
;  the derived function, the cases tested along the different paths through the
;  code, the canonical forms of any states produced from the derived function,
;  and the governing hypotheses of the ``theorem'' alleging that the derived
;  function is correct.  However, for the correctness theorems to be provable
;  it is generally necessary that the extended :hyps be invariant on every call
;  of ANY derived function produced by this def-semantics.

;  This is an optional field that defaults to nil (i.e., no additional
;  hypotheses are added).

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :annotations nil

;  An alist allowing you to modify the automatically generated output of
;  def-semantics.  Thus, if def-semantics ``almost'' succeeds in deriving good
;  semantic functions and their correctness theorems but the events need a
;  little minor tweaking to be admissible, you can add that tweaking here and
;  leave the def-semantics command in your script.  If, on the other hand,
;  def-semantics fails badly, you might just take part of its output and use it
;  as a starting point for your own definitions and theorems.

;  Each element of the :annotations alist must be in one of two forms and the
;  form dictates how the output is modified:

;  * (name (DECLARE ...)) -- means that name is the name of a function that
;    will be generated by this def-semantics and the automatically generated
;    declarations are to be replaced in their entirety by the given DECLARE
;    form.  Furthermore, the DEFUNM-NX that would have been generated becomes a
;    standard ACL2 DEFUN-NX!  Thus, if you provide a DECLARE :annotation you
;    are using def-semantics to generate the body but you are completely taking
;    over the admission of the function.

;  * (name :keyword . rest) -- means different things depending on what sort of
;    generated event has the given name.

;    + If name is defun-like (i.e., DEFUNM-NX), :keyword and everything
;      following it is added to the front of the automatically generated XARGS,
;      so that (DECLARE (XARGS . auto-xargs)) becomes (DECLARE (XARGS :keyword
;      ,@rest . auto-xargs)) Thus, adding an :in-theory (for example)
;      :annotation means that you are just telling def-semantics to go ahead
;      with its guesses but to use your hints.

;    + If name is a DEFTHM, :keyword must be :hints and it and everything
;      following it are added to the generated defthm in the :hints position.

;  Note that we don't actually check what sort of event name there is until we're
;  asked to add the appropriate annotation.  So our pre-processing error
;  checking on annotations is limited.  However, when we attempt to use an
;  annotation we check for certain conditions and signal a hard or soft error
;  if violations are detected.  Of course, ultimately the final events are
;  processed and must be admissible or the def-semantics will fail.

; Other annotations could be implemented if they seem useful.  We regard the
; current :annotations as a starting point.

; This is an optional field with default nil.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; (end of keyword arguments for def-semantics)
;  )

; Def-semantics makes certain pre-checks on the arguments and then attempts to
; walk the code in question, resulting either in a supposedly self-explanatory
; error message or the admission of clock and semantic functions corresponding
; to :init-pc and the proof of their correctness theorem.

; If run, svar, and get-pc are the contents of the :run, :svar, and :get-pc
; fields of the API, init-pc is the :init-pc of the def-semantics and hyps' is
; the :hyps+ extension of the :hyps field of the API, and clk and sem are the
; names generated by def-semantics for the clock and semantic functions
; corresponding to :init-pc, then the correctness theorem is:

; (DEFTHM sem-CORRECT
;    (IMPLIES (and hyps'
;                  (equal (get-pc svar) 'init-pc))
;             (EQUAL (run svar (clk svar))
;                    (sem svar)))
;    ...)

; Def-semantics disables clk after this correctness proof.  Def-semantics will
; define other functions and prove them correct as required by the loop
; structure of the code walked.

; During the exploration of the paths through a region of code, def-semantics
; prints out two kinds of reports.  The first kind look like this:

; pc 6 ==> (7) [unkn: NIL]
; pc 7 ==> (8) [unkn: NIL]
; ...
; pc 337 ==> (338 350) [unkn: NIL]
; ...

; and the second kind are ``SNORKEL REPORT''s as explained below.

; The first kind of reports record a superficial exploration of the code to
; compute the topology, i.e., loops, branches, and terminal pcs.  The line

; pc 337 ==> (338 350) [unkn: NIL]

; means that from the state with pc 337 has two immediate successor states, one
; with pc 338 and the other with pc 350.  There are no successors with
; indeterminate pcs.  We see from this line that some kind of branch occurs at
; pc 337.  But this exploration superficial because it does not take into
; account the tests made along the path to 337.  It could be that those tests
; force the test at 337 to always be T so that, in fact, pc 350 is never an
; immediate successor.

; The more expensive, context-sensitive exploration is done after collecting
; the ``cutpoints'' from the code.  (Cutpoints are discussed further below.)

; Let s_0 be some machine state poised at the top of some path in the code,
; e.g., state with pc 6.  To explore that path, Codewalker calls the rewriter
; on a term that STEPs the state until it loops, terminates or reaches some
; other ``cutpoint.''  Let s_i be the state reached from s_0 after i steps.
; As Codewalker steps the state it composes the changes of successive
; instructions, introducing IFs to explain branches in the path.

; But each step involves a call of the ACL2 rewriter, which pushes more
; information onto the Common Lisp stack.  Long paths can cause the Common Lisp
; stack to overflow.  To avoid stack overflow, Codewalker takes at most 300
; steps and then stops and returns a term representing the incomplete answer,
; i.e., an IF-expression with some ``tip'' states in it (states that reached
; cutpoints) and also some states, e.g., s_300, not yet at cutpoints.  By
; stopping the rewriting and returning the (incomplete) answer, Codewalker
; clears the Common Lisp stack.  It then applies the rewriter to the incomplete
; answer, which has the effect of extending the path 300 steps further from the
; states that have not yet reached cutpoints.  This is called ``snorkeling''
; because it is as though the rewriter has to come up periodically for air.

; Every 300 steps, Codewalker prints a snorkel report such as:

; SNORKEL REPORT: pc: 6; steps 600
; number of continuations: = 1
; nesting depth: 1
; splitter pcs: (337)
; partial-path-tree =
; (IF (EQUAL (NTH '0 (RD ':LOCALS S)) '0) :TIP (:CONTINUATION-FROM-PC 410))

; In a snorkel report, pc is the program counter at which the current path
; begins, steps is the number of steps taken so far along that path and will
; generally be a multiple of 300.  The number of continuations is the number of
; states in the incomplete answer that have not yet reached cutpints, splitter
; pcs lists the pcs at which IFs were introduced, and the partial path tree is
; a term-like expression that sketches the current incomplete state.  In the
; example above, the path beginning at 6, after 600 steps, contains on IF
; (introduced by the instruction at 337) testing the term (EQUAL (NTH '0 (RD
; ':LOCALS S)) '0).  On the branch of the path where that term is true, some
; cutpoint was reached.  But on the branch where that term is false, we reached
; s_300 which is a state with pc 410.  After the report has been printed,
; Codewalker resumes rewriting, eventually reaching a cutpoint on every branch
; of the path.

; These reports are intended to give you a sense of the progress made so far
; while exploring long branches.  If you witness behavior different from that
; described above, please report it.

; The frequency of snorkel reports (and, more importantly, of ``coming up for
; air'') is determined by the defconst *snorkel-depth*.  Its value is set to
; 300.

; -----------------------------------------------------------------------------
; Example/General Form of Def-Projection

; Def-projection attempts to derive a function that returns the final value of
; a given state component of the state produced by a given semantic function --
; as a function only of the values of the relevant input state components.  The
; motivation of doing this is usually so you can better understand ``what the
; code does,'' by understanding its effects on any part of the state, phrased
; in terms of just those operations and inputs that affect the part of
; interest.  We call this ``projecting'' a component out of a semantic
; function.  The result is a function, called the ``projection'' of the
; component.  Def-projection attempts to derive a given projection of a given
; semantic function and to prove that the projection is correct.

; (def-projection
; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :new-fn FN

;  a new function symbol, to be used as the name of the projection.  This is
;  a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :projector (NTH 3 (REGS S))

;  a state component expression, i.e., an instance of one of the comp terms in
;  the :state-comps-and-types field of the API, ((comp type) ...), such that
;  the :svar of the API is bound to itself and all other variables are bound to
;  constants.  In the example def-model-api shown above the :svar is S and one
;  of the comps in the :state-comps-and-types is (NTH I (REGS S)).  This comp
;  matches the :projector shown above, with S bound to S and I bound the
;  constant 3.

;  This is a required field.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :old-fn SEM-PROG-A-0

;  the function symbol of a semantic function written by def-semantics; the
;  value returned by this function is a state and the value of the function,
;  :new-fn, to be defined, is supposed to be the :projector component of that
;  state.  However, def-projection attempts to derive a function definition
;  that does not take the entire state as an argument and instead is
;  sensitive only to the values of the relevant state components in the state
;  to which :old-fn is applied.  The correctness theorem proved by
;  def-projection is shown below and makes clear what we mean.

;  This is a required field.
; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;  :hyps+ nil

;  A list of terms to be conjoined to the :hyps of the API while doing this
;  def-projection.  The :hyps of the API are not permanently extended.  To
;  succeed, the extension used for this def-projection should probably be
;  identical to that used by the def-semantics that produced :old-fn.  See the
;  discussion of :hyps+ in def-semantics above.  This is an optional field with
;  default nil.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; (end of keyword arguments for def-projection)
;  )

; Def-projection makes certain pre-checks on the arguments and then attempts to
; derive a suitable definition of :new-fn.  It also generates a correctness
; theorem for the :new-fn.  If svar is the :svar of the API and hyps' is the
; :hyps+-extended :hyps in the API and (proj0 s), (proj1 s), ..., (projk s) are
; all state component terms of the API, and new-fn is the name of the newly
; defined function :new-fn, :projector is (proj0 s), and sem is the :old-fn
; being projected, then the correctness theorem is:

; (DEFTHM new-fn-CORRECT
;   (IMPLIES hyps'
;            (EQUAL (proj0 (sem s))
;                   (new-fn (proj1 s) ... (projk s))))
;   ...)

; Note that this theorem can be composed with sem-CORRECT to show that running
; the code and projecting out the final value of proj0 is the same as computed
; by new-fn on the values of components progj1, ..., projk in initial state s.
; If def-projection fails to define :new-fn or to prove the correctness
; theorem, a supposedly self-explanatory error message is printed.

; A common error message concerns what are called ``subprojections.''  Suppose
; the semantic function, say sem, calls some other semantic function, say
; sub-sem.  This would happen if the code explored for sem encountered a simple
; loop; sub-sem would be the semantic function generated for the loop.  Before
; projecting some component of sem you must first project the relevant
; components of sub-sem.  For example, suppose you want to project out the
; final value of register 1 from sem.  Then you will need to first project out
; the final value of register 1 from sub-sem.  We call that a
; ``sub-projection.''  If you attempt to project out from sem before the
; necessary sub-projections have been created, def-projection will print an
; error message.  Usually the error message will exhibit the sub-projections
; you need to do.

; You might ask why def-projection doesn't just do the required sub-projections
; if it knows what they are?

; The answer is that def-projection is designed so that you choose the names of
; every relevant projection (i.e., :new-fn).  If sub-projections were done
; automatically, the names would be arbitrarily generated symbols.  We have
; found this makes it harder to understand what the ultimate projection is
; doing because it talks about concepts not named by the user.  That defeats
; the main purpose of def-projection.  So do not be surprised if you're asked
; to do a particular sub-projection!  And when you are asked, think of a
; meaningful name for the concept you're introducing!

; Also note that def-projection must discover which are the ``relevant''
; components affecting the final value of the one of interest.  This is done
; iteratively in the sense that def-projection may note that the final value of
; interest depends on certain other state components and may ask you to do
; sub-projections of them.  In any case, you are not responsible for
; identifying the ``cone of influence.''  Def-projection is responsible for
; that.  But do not be surprised if you are asked to name sub-projections that
; are on different components than the one in which you're interested!

; This completes the reference guide.

; =============================================================================
; Appendix A: More on Four Similiar Data Structures: :updater-drivers,
;   :constructor-drivers, :state-comps-and-types, and :var-names.

; This Appendix discusses all four of the model API fields named in the title.
; We present a few more examples to explain their individual uses and how
; they're interpreted, and we discuss their relationships.

; The Appendix is divided into four sections:

; The :UPDATER-DRIVERS and :CONSTRUCTOR-DRIVERS Fields
; The :STATE-COMPS-AND-TYPES Field
; The :VAR-NAMES Field
; Discussion of All Four Fields

; The reason we conflate the discussions of these four fields is that all four
; concern the identification of the state components being changed as a
; semantic function recurs, the same state components that might be generalized
; to variables in projections, the ``inherent'' types of those newly introduced
; variables, and the names of those variables.  There are reasons that we have
; four fields instead of one, but the reasons are not necessarily good ones!
; This discussion also attempts to document those reasons to inform (and
; perhaps encourage) future attempts to unify the fields.

; The :UPDATER-DRIVERS and :CONSTRUCTOR-DRIVERS Fields

; The :updater-drivers and :constructor-drivers fields are used to explore the
; canonical state expressions produced by simplifying the state expressions
; derived by executing sequences of instructions in the model.  Both
; def-semantics and def-projection use these fields in guessing measures to
; explain derived functions.  In addition, def-projection uses them to identify
; state components that can be generalized.

; Suppose for example that some sequence of instructions produces a state expression
; that canonicalizes to:

; (!pc 22
;      (!regs (update-nth 0 (- (nth 0 (regs s)) 1)
;               (update-nth 2 (+ (nth 0 (regs s)) (nth 7 (regs s)))
;                   (update-nth 3 (nth 7 (regs s))
;                                 (regs s))))
;             (!stack (nth 7 (regs s))
;                     s)))

; Then the state components that are modified in this expression are derived
; entirely from information in the :updater-drivers setting:

; ``modified'' components
; (pc s)
; (nth 0 (regs s))
; (nth 2 (regs s))
; (nth 3 (regs s))
; (stack s)

; (Technically, perhaps we should say ``targets of the writes'' since we do not
; mean to imply that the new value is necessarily different from the old
; value.)

; These terms are called ``virtual formals'' of any semantic function that
; transforms state s to the new canonicalized state expression above.  The idea
; behind the name is that the values of the virtual formals are being changed
; independently in recursion and we might find a decreasing measure of these
; virtual formals to admit the semantic function.

; Determining the virtual formals (i.e., modified state components) involves
; recursively diving through the canonicalized state expression confirming that
; just the right nest of updaters occurs, with just the right :value and :base
; expressions.

; Consider our determination that (nth 2 (regs s)) is modified.  Naively one might
; expect from this determination that the new state is (!regs (update-nth 2
; ... (regs s)) s).  No such expression even occurs in the new state above.
; Instead we see that (!pc ... (!regs ... (update-nth 2 ... (update-nth 3
; ... (regs s))) (!stack ... s))) occurs.  Starting at the top, we see that
; (!pc ... ...) not only modifies the pc of whatever state is in its :base, but
; that it also modifies whatever that :base modifies.  That :base is (!regs
; ... ...).

; Reasoning recursively, we see that its :value modifies positions 0, 2, and 3
; of its ultimate base, which (regs s) -- here repeating the exact recursive
; reasoning through the :values and :bases of the update-nth expressions.

; Furthermore, it is not sufficient to notice that position 2 of (regs s) is
; modified unless we also note that the result of all those update-nths is
; ultimately written back to (regs s) via the (!regs ... ...).

; Once we identify the modified slots of the canonicalized state expression, we
; can look for one that is decreasing and see that (nth 0 (regs s)) is
; (probably) decreasing -- if we can be sure it is a non-0 natural.

; The reasoning above involves only the :updater-drivers because only updaters
; are used to build the new state.  If the canonicalized state expressions
; involve constructors then we would have to also mix in exploration through
; :constructor-drivers.

; For example, an equivalent new state expression could be obtained if we
; adopted a different canonical form, one in which update-nth and nth
; expressions are expanded into cons/car/cdr nests.  (The expression below is
; equivalent to that above if (regs s) has at least 8 elements so all the
; update-nth and nth expressions expand appropriately.  We use extended
; cad..dr/cdd..dr nests for succinctness below.)

; (!pc 22
;      (!regs (cons (- (car (regs s)) 1)
;                   (cons (cadr (regs s))
;                         (cons (+ (car (regs s)) (cadddddddr (regs s)))
;                               (cons (cadddddddr (regs s))
;                                     (cddddr (regs s))))))
;                                 (regs s))))
;             (!stack (cadddddddr (regs s))
;                     s)))

; which would result in the modified state components

; (pc s)
; (car (regs s))
; (car (cdr (cdr (regs s))))
; (car (cdr (cdr (cdr (regs s)))))
; (stack s)

; The identification that (car (regs s)) is probably decreasing requires
; exactly the same analysis as shown above, even though the canonical form is
; different.

; This also makes it clear why we impose the orthogonality requirement.  If
; both (cadr (regs s)) and (nth 1 (regs s)) were allowed in the canonical form
; -- and thus in :updater-drivers and :constructor-drivers -- then the
; ``canonical'' form wouldn't be canonical.  This can confuse the termination
; analysis, which is designed to suggest a decreasing measure for recursively
; defined functions.  For example, one standard iterative/recursive paradigm is
; to count some value up to a fixed upper bound.  The termination analysis
; therefore might look for a state component that is used as an upper bound in
; a test and that is not being changed in the new state expressions.  In
; non-canonical forms, the termination analysis might settle on the component
; (cadr (regs s)) as fixed even though it might detect that (nth 1 (regs s)) is
; changing.

; The use of :updater-drivers and :constructor-drivers to identify virtual
; formals is actually done by code in the Terminatricks book, where the two
; fields are actually tables, named generalized-updater-drivers and
; constructor-drivers.  Def-model-api stores :updater-drivers and
; :constructor-drivers in those tables, in addition to making them available
; in the API.  See the section of Terminatricks entitled Virtual Formals and
; Proto Distilled Machines for more detailed comments on the use of these
; tables.

; The use of the keywords :value and :base in the driver patterns could be a
; problem if those keywords play important roles in the model.  Let us know and
; we'll adopt another convention.  (This faulty convention stems from an early
; implementation in which these terms had to be in translated form and
; thus the user actually wrote (rd ':pc :base), where the UNQUOTED :base
; denoted the special slot.  But when we added the automatic translation of
; these patterns, allowing (rd :pc :base), suddenly the role of :base is
; ambiguous: is it a built-in constant or a special token marking the slot?)

; The :STATE-COMPS-AND-TYPES Field

; Now we turn to the :state-comps-and-types field.  This field determines which
; parts of a state def-projection can generalize to new variables.

;  Recall that the shape of each element is (comp type), as in

;   (  comp            type                  )
;   ((NTH I (REGS S)) (NATP (NTH I (REGS S))))

; where both comp and type are terms, comp mentions the :svar variable of the
; API, and, except when type is T, comp occurs in type so that when an instance
; of comp is generalized, the same generalization of that instance of type
; produces a constraint on the new variable.  For example, if (NTH 7 (REGS S))
; is generalized to R7, then (NATP R7) is the constraint imposed by the above
; (comp type).

; When def-projection identifies a state component, (sc s), to be generalized
; and become a formal parameter, v, of the projection it also identifies
; constraints, (p v), on the new variable.  These come from three sources: (a)
; tests on the state component made by the semantic function being projected,
; (b) tests on the state component derived from the invariant :hyps assumed in
; the API, and (c) the type test associated with the state component in the
; :state-comps-and-types.

; One might think that (c) is unnnecessary in light of (b), e.g., one might
; reason, incorrectly, that ``if the user wants to add (p v) when (sc s) is
; generalized to v, it is sufficient for the user to add the conjunct (p (sc
; s)) to :hyps in the API.''  This fails because it (p (sc s)) might be always
; T due to ``inherent'' properites of sc rather than to properties conferred
; by the particular state.

; For example, one might define the register accessor (RD-REG I S).  In fact,
; one might define RD-REG so that it is known to return a natural number less
; than 2^32 by construction.  If (RD-REG 7 S) is a state component to be
; generalized, one might hope to recover (< (RD-REG 7 S) (EXPT 2 32)) by
; inspecting the :hyps of the API.  But that fact, even if it had been included
; explicitly as a conjunct, would have been simplified to T by properties of
; RD-REG.

; We could get constraints (c) via ACL2's :GENERALIZE lemmas.  But experiment
; has found that those lemmas might introduce additional constraints that
; complicate the projections.  So (c) -- and thus the type terms in
; :state-comps-and-types -- really serve two purposes: to get necessary
; intrinsic properties of the formal parameters and to avoid picking up junk
; the user doesn't want, i.e., to allow the user to specify exactly what is
; wanted.

; The :VAR-NAMES Field

; The :var-names setting used in the Reference Guide example was:

;   (((PC S)             "PC")
;    ((NTH I (REGS S)) "R~x0" I)
;    ((STACK S)          "STK")
;    (:OTHERWISE         "X"))

; and its interpretation is explained in the Reference Guide for def-model-api.
; This form of :var-names was called the ``list of tuples'' format.

; But it is also legal to set the :var-names to a function name (or equivalent
; lambda expression).  The function may be in either :logic or :program mode.
; It is sometimes easier to code a :program mode function than to arrange a
; suitable list of tuples.  Here we explain how to achieve the same effect by
; setting :var-names to a function.

; Before executing the def-model-api, define my-var-names as:

; (defun my-var-names (term)  ; term is a state component; we return
; ;                           ; a string or fmt msg that prints the string we
; ;                           ; choose.  Remember that term is in translated
; ;                           ; form, so constants are all QUOTEd!

;   (declare (xargs :mode :program))
;   (case-match term
;     (('PC 'S)                      "PC")
;     (('NTH ('QUOTE I) '(REGS S))   (msg "R~x0" I))
;     (('STACK 'S)                          ; or equivalently '(STACK S)
;                                    "STK")
;     (&                             "X")))

; Note that (my-var-names '(NTH '7 (REGS S))) generates the root name "R7".
; When '7, aka (QUOTE 7), is matched by case-match against ('QUOTE I), the I is
; let-bound to 7.  When (msg "R~x0" I) is then evaluated (as part of applying
; my-var-names) (msg "R~x0" I) produces the msg pair ("R~x0" . ((#\0 . 7))) as
; the result of my-var-names.  That pair is then printed with fmt to produce
; "R7".  Note also that the :svar of the machine model is built into the
; definition above, as 'S.

; Suppose we wanted to map (NTH 123 (MEM S)) to the string "WORD-15-BYTE-3",
; since 123 = 15*8 + 3.  We could do that with either the list of tuples form
; or the function/lambda expression form.  The list of tuples would be:

; :var-names:
;   (((PC S)             "PC")      ; general form:
;    ((NTH I (REGS S)) "R~x0" I)  ; (pattern fmt-string term_0 term_1...)
;    ((NTH I (MEM S))  "WORD-~x0-BYTE-~x1" (floor I 8) (mod i 8))
;    ((STACK S)          "STK")
;    (:OTHERWISE         "X"))

; Alternatively, we could define:

; (defun my-var-names (term)
;   (declare (xargs :mode :program))
;   (case-match term
;     (('PC 'S)                      "PC")
;     (('NTH ('QUOTE I) '(REGS S))   (msg "R~x0" I))
;     (('NTH ('QUOTE I) '(MEM S))    (msg "WORD-~x0-BYTE-~x1"
;                                          (floor I 8) (mod i 8)))
;     (('STACK 'S)                   "STK")
;     (&                             "X")))

; It is sometimes easier to define a :var-names function than to use the
; list-of-tuples approach, especially if you want to use sophisticated tests to
; steer the function function to the right string or msg.  For more, and more
; elaborate, examples, See the Essay on :var-names -- Two Ways for the User to
; Control the Generation of Variable Names in the Code section of this file.

; Discussion of All Four Fields

; Clearly, all four of these fields are involved in the user's specification of
; of what a ``state component'' is.  The urge to unify the fields, perhaps into
; a single field, is strong.  That single field might describe the shape of a
; state component and its type, a la :state-comps-and-types, and additionally
; encode how to generate the appropriate variable names from instances of the
; pattern.  This would obviate :updater-drivers and :constructor-drivers.

; However, Terminatricks needs those two lists, which are stored there as
; tables.  Recall that Terminatricks is charged with looking at a proposed
; function definition and guessing a decreasing measure.  Terminatricks
; ``learns'' from previously admitted definitions with user-supplied measures
; as well as patterns in certain user-controlled tables.  A key idea introduced
; in Terminatricks is that of ``virtual formal,'' a part of an argument being
; changed in recursion.

; For example, the following is an easy-to-admit function for Terminatricks
; which is not admitted without an explicit measure by ACL2.

; (defun foo (x)
;   (if (atom x)
;       x
;       (if (atom (car x))
;           (car x)
;           (foo (cons (caar x)
;                      (cons (cdar x) (cdr x)))))))

; Terminatricks guesses that the measure (acl2-count (car x)) decreases,
; because it identifies (car x) as a ``virtual formal'' of this function based
; on the :constructor-driver ((cons a b) (car :base) (cdr :base)).

; Terminatricks has nothing to do with Codewalker, semantic functions, machine
; models, machine states, etc.

; Thus, if Codewalker were to have a single unified field to answer the
; questions that def-semantics and def-projection have about state components
; and Codewalker expects to use Terminatricks, then the developer of
; Codewalker must implement some transformation of the unified field into
; appropriate settings for Terminatricks' driver tables.  While this is
; probably practical, we decided it was better to get on with developing
; Codewalker's functionality.

; =============================================================================
; Limitations and Mitigations

; When we say that ``Codewalker fails'' we mean that its attempt to admit
; definitions or prove theorems fails in one of the standard ways ACL2 events
; may fail: resource exhaustion, running ``forever,'' or error messages.  If
; Codewalker succeeds, i.e., terminates without such failures, then the derived
; definitions are admissible and the alleged correctness ``theorems'' are
; indeed theorems, notwithstanding any statements below about the assumptions
; Codewalker makes.

; Limitation 0: You must have a suitable ACL2 lemma data base configured for
; code proofs about your model.  We discuss this in more detail in the
; reference guide for def-model-api.  The ``friendly introduction'' section
; below cites a worked example of Codewalker functionality whose source files
; exhibit the necessary setup.

; Limitation 1: It must be possible to express the API in the terms required by
; def-model-api below, e.g., the model is an ACL2 operational semantics based
; on some notion of ``state,'' a single step transition function, a function
; that ``runs'' a state some number of steps, and a ``pc'' that points to the
; next instruction to be stepped.

; Limitation 2: Codewalker requires that every reachable pc traversed must be
; constant, starting with the initial pc.  For example, a typical def-semantics
; command says ``start exploration at :init-pc 0'' or ``:init-pc 12345'' but
; should not say ``:init-pc (+ x 23).''

; Limitation 3: Given the instruction at a reachable pc it must be possible to
; determine, by rewriting the step function, what the possible next values of
; the pc will be.  All of those next pc values must be constants.  To be more
; precise, rewriting the application of the step function on a state with a
; constant pc should canonicalize to an IF-expression whose tips are state
; expressions and the pcs in all those states should be constant.  This means,
; for example, that an ISA that includes instructions that may set the pc to
; data-dependent values may cause trouble if encountered.  An example of such
; an instruction would be a jump to the value of a computed arithmetic
; expression.  A more common example is a call instruction to a subroutine
; whose starting pc cannot be resolved to a constant.

; Limitation 4: Codewalker assumes that the canonical expressions for state
; components arising from expanding the step function on the program of
; interest are all independent or ``orthogonal.''  Thus, if a program exploits
; aliasing or accesses and modifies data via different canonical idioms, it is
; likely to cause Codewalker to fail.  For example, suppose the idiom for
; accessing memory is (rd-mem addr sz s), where addr is the memory address, sz
; is the number of bytes to read, and s is the state variable.  Then the two
; ``canonical'' expressions (rd-mem 100 8 s) and (rd-mem 103 2 s) are not
; orthogonal.  Memory writes that change one of those values may change the
; other whereas Codewalker assumes otherwise and may produce incorrect semantic
; functions on code that uses both idioms.

; Limitation 5: Codewalker will not work if the code to be explored does not
; terminate under the hypotheses of the API.  This is a fundamental limitation
; of the current design: the semantic functions derived by Codewalker must be
; admissible in the ACL2 logic.

; Limitation 6: Codewalker will probably not work on self-modifying code.  The
; control flow graph of the program is determined by static analysis of the
; code.  We suspect that if the control flow graph of the original code is the
; same as the graph of the running, self-modifying code, Codewalker might
; actually succeed in producing the correct semantics.  But the truth is that
; we haven't thought about such exploring self-modifying programs (yet) because
; we need to walk before we can run!

; It is possible to mitigate some of these limitations some of the time.
; Imagine that the code of interest contains instructions that would cause
; Codewalker to fail.  Def-semantics can still be used to explore that portion
; of the code that Codewalker can handle.  Two obvious ways to do this are:

; * use the :focus-regionp argument of def-semantics to limit the exploration
;   to regions of code containing instructions Codewalker can handle

; * use the :hyps argument of def-model-api or the :hyps+ argument of
;   def-semantics to restrict Codewalker's attention to paths that it can
;   handle.

; The second idea, of changing the hypotheses under which the code is analyzed,
; sometimes admits a way to partially handle some limitations.  For example, if
; the code doesn't in general terminate but can be shown to terminate under
; some hypothesis, then adding that hypotheses to :hyps or :hyps+ might be
; helpful.

; Similarly, if the program contains the instruction ``jump to the unknown
; value of register 2'' you might add the hypothesis that register 2 contains
; 123.  Because the meaning of any instruction is actually computed by the ACL2
; rewriter, that assumption -- if it interacts properly with your rewrite rules
; -- could make the jump instruction's new pc resolve to a constant as
; required.

; Changing the assumptions may well violate assumed invariants causing proofs
; to fail.  The :hyps (as extended by :hyps+) are supposed to be invariant
; under the step function.  But even if the correctness proofs fail, Codewalker
; will produce and print semantic functions derived under these (bogus)
; hypotheses and you may well find those definitions helpful in understanding
; the code or building a provably correct semantic function.

; The mitigation techniques outlined here will not allow the complete analysis
; of code that Codewalker inherently cannot ``understand.''  But the larger
; point is that Codewalker should be viewed as an assistant that may help you
; understand the code.  You may find that Codewalker fails every time you use
; it and yet prints things that are helpful!  Remember, if worse comes to
; worst, you can use Codewalker to take a stab at the semantics, grab its
; ill-formed, half-baked, incorrect ideas out of the session log, and use them
; in a hand-built model of the code.  In the end, Codewalker may not play a
; role in your certified book, but could still play an important role in the
; creation of that book.

; =============================================================================
; Following Some Examples through the Implementation

; Before we start with the details of the implementation it may be helpful to
; go through one of the examples above ``from the inside,'' i.e., with our
; attention on how the results are produced rather than just the user input and
; the results.

; In this section we'll talk about some of those.  For convenience we reproduce
; the *program* being walked and the derived definitions of CLK-6 and SEM-6.

; (defconst *program1*
;   '((ICONST 1)  ; 0
;     (ISTORE 1)  ; 1  reg[1] := 1;
;     (ICONST 0)  ; 2
;     (ISTORE 2)  ; 3  reg[2] := 0;
;     (ICONST 1)  ; 4
;     (ISTORE 3)  ; 5  reg[3] := 1;
;     (ILOAD 0)   ; 6                         ; <--- loop
;     (IFEQ 14)   ; 7  if R0=0, goto 14+5;
;     (ILOAD 1)   ; 8
;     (ILOAD 0)   ; 9
;     (IMUL)      ;10
;     (ISTORE 1)  ;11  reg[1] := reg[0] * reg[1];
;     (ILOAD 2)   ;12
;     (ILOAD 0)   ;13
;     (IADD)      ;14
;     (ISTORE 2)  ;15  reg[2] := reg[0] + reg[2];
;     (ILOAD 0)   ;16
;     (ILOAD 3)   ;17
;     (ISUB)      ;18
;     (ISTORE 0)  ;19  reg[0] := reg[0] - reg[3];
;     (GOTO -14)  ;20  goto 20-14;            ; goto loop
;     (ILOAD 1)   ;21
;     (HALT)))    ;22  halt with a on top of stack;

; (def-semantics
;  :init-pc 0                           ; initial pc where exploration starts
;  )                                    ; optional args default

; The first steps in def-semantics are to analyze the control flow and
; identify pc = 6 as a loop and pc = 22 as the exit.  These, along with the
; entry, 0, are called the ``cutpoints'' of the program.  Roughly speaking
; we do this by building context-free flow graph like the one shown below:

;                                               21 --> 22 [halt]
;                                             /
; 0 --> 1 --> 2 --> 3 --> 4 --> 5 --> 6 --> 7
;                                     ^      \
;                                    |       8 --> ... --> 20
;                                    |_____________________|

; We do this by taking a state s sastisfying the :hyps+-extended :hyps of the
; API, setting the pc to 0, and stepping it once with the simplifier to get an
; IF-expression with new symbolic states at the tips.  We collect all the pcs
; of those tips and know that the instruction at pc 0 transitions to (at most)
; one of those pcs.  We repeat this until we've explored the whole focus
; region.

; Note that each step is ``context free:'' we don't compose transitions from
; state to state at this stage.

; Having identified (0 6) as non-terminal cutpoints and (22) as the only halt
; we simulate forward from each non-terminal cutpoint to whatever cutpoint(s)
; are encountered next.  (By construction, we know some cutpoint will be
; encountered before we loop back on ourselves, no matter where we start.)  So,
; for example, the first (and only) cutpoint reached from pc 0 is pc 6.

; This simulation is done with the simplifier and compounds successive states,
; so it is context sensitive (relative to the state invariant and previously
; tested tests). This simulation may produce a big IF-expression with state
; expressions at the tips -- except we use a rewriting trick to keep track of
; how many steps we take to reach each final cutpoint pc (``fpc'') and the
; particular path through the pcs we followed to get there.  For example, the
; expression produced by simulating forward from pc = 0 is shown below.  This
; is called a ``path-tree.''  (We have untranslated the expressions below by
; hand for readability.)

; (ACL2::CODEWALKER-TIP
;  6                                  ; step count
;  '(0 1 2 3 4 5 6)                   ; path from 0 to 6 (``fpc'' = 6)
;  NIL                                ; splitters (pcs introducing IFs)
;  (WR :PC 6                          ; final state (``s[6]'' =)
;      (WR :LOCALS
;          (UPDATE-NTH 1 1
;           (UPDATE-NTH 2 0
;            (UPDATE-NTH 3 1
;                        (RD :LOCALS S))))
;          S)))

; The CODEWALKER-TIP function just records the number of steps taken from pc 0,
; the path followed (concluding with the fpc = 6), the pcs introducing IFs, and
; the final state (here s[6]).

; Such path-trees are the basis of the definitions of both the clock and the
; semantic functions.

; For example the clock function starting at pc 0 will basically be

; (clk+ 6                            ; step count of codewalker-tip for pc=0
;       (clk-6                       ; name of clock function for pc=6
;          s[6]))                    ; final state in codewalker-tip for pc=0

; These remarks ignore that fact that we assumed extended hyps.  If we add that
; as a hypothesis we get the final definition of CLK-0:

; (DEFUN CLK-0 (S)
;   (IF (AND (HYPS S) (PROGRAM1P S))
;       (CLK+ 6
;             (CLK-6
;              (WR :PC 6
;                  (WR :LOCALS (UPDATE-NTH 1 1
;                               (UPDATE-NTH 2 0
;                                (UPDATE-NTH 3 1
;                                            (RD :LOCALS S))))
;                      S))))
;       0))

; Similarly, we see that the semantic function SEM-0 is just a call to the
; semantic function for pc 6 applied to s[6].  So we get

; (DEFUN SEM-0 (S)
;   (IF (AND (HYPS S) (PROGRAM1P S))
;       (SEM-6
;        (WR :PC 6
;            (WR
;             :LOCALS (UPDATE-NTH 1 1
;                      (UPDATE-NTH 2 0
;                       (UPDATE-NTH 3 1
;                                   (RD :LOCALS S))))
;             S)))
;       S))

; We can derive these preliminary definitions for CLK-0 and SEM-0 even before
; we define CLK-6 and SEM-6 because we know what names we'll use for the clock
; and semantic functions for any given starting pc: CLK-pc and SEM-pc.

; Here is the path-tree produced by simulating forward from pc = 6 to the next
; cutpoint(s).

; (IF (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;     (ACL2::CODEWALKER-TIP
;      3                           ; step count
;      '(6 7 21 22)                ; path with t(erminal)pc = 22
;      '(7)                        ; splitters
;      (WR :PC 22                  ; final state
;          (WR :STACK (PUSH (NTH 1 (RD :LOCALS S))
;                           (RD :STACK S))
;              S)))
;     (ACL2::CODEWALKER-TIP
;      15                          ; step count
;      '(6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 6) ; path with tpc = 6
;      '(7)                        ; splitters
;      (WR :PC 6                   ; final state
;          (WR :LOCALS (UPDATE-NTH 0 (+ (NTH 0 (RD :LOCALS S))
;                                       (- (NTH 3 (RD :LOCALS S))))
;                       (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                                        (NTH 1 (RD :LOCALS S)))
;                        (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                         (NTH 2 (RD :LOCALS S)))
;                                    (RD :LOCALS S))))
;              S))))

; Given that pc = 22 is known to be a halt (or exit from the region of
; interest), we know there are no clock and semantic functions for it.

; So, given that the path-tree above starts in a state satisfying (hyps s) and
; (program1p s) with pc = 6, it is pretty obvious how to define CLK-6 and
; SEM-6:

;   * CLK-6: Visit the CODEWALKER-TIP expressions.  At each, let tpc be the
;     terminal cutpoint (e.g., 22 in the first tip above and 6 in the second).
;     If tpc is a halt pc (tpc = 22) replace that CODEWALKER-TIP by the step
;     count (e.g., 3) and otherwise (tpc = 6) replace that CODEWALKER-TIP by
;     the CLK-+ of the step count (15) and a call of CLK-tpc (CLK-6) on the
;     final state in the tip.

;   * SEM-6: Visit the CODEWALKER-TIP expressions.  At each, let tpc be the
;     terminal cutpoint (e.g., 22 in the first tip above and 6 in the second).
;     If tpc is a halt pc (tpc = 22) replace that CODEWALKER-TIP by the final
;     state in the tip, and otherwise (tpc = 6) replace that CODEWALKER-TIP by
;     a call of SEM-tpc (e.g., SEM-6) on the final state in tip.

; Implicit in the descriptions above is the addition of an additional IF
; testing (hyps s) and (program1p s) and laying down the body described above
; if those extended hypotheses are true.  In the case that they are false, we
; lay down either 0 or s, depending on whether we're defining a clock or a
; semantic function.

; Now the ``definitions'' described above are still not quite right because
; they do not record the fact that reg[3] is always +1 in CLK-6 and SEM-6.  If
; that fact is not discovered and recorded in the definition somewhere, then
; the definitions won't be admissible because the only thing even possibly
; decreasing is reg[0] and the CLK-6 and SEM-6 described above recur by
; replacing reg[0] by reg[0] - reg[3], for an unknown value of reg[3].  So the
; definitions derived above are considered ``preliminary.''

; We discover that reg[3] = +1 in SEM-6 (say) by noting that the preliminary
; definition of SEM-0 calls SEM-6 with reg[3] = +1 and that SEM-6 does not
; change reg[3] (and no other function calls SEM-6).  Having discovered this
; invariant, we conjoin it into the extended hyps test, and get the final
; definition of SEM-6.

; The resulting final definitions are shown below (with DECLAREs and
; non-logical noise deleted).  Compare these two to the path-tree for pc 6
; shown above.

; (DEFUN CLK-6 (S)
;   (IF (AND (HYPS S)
;            (PROGRAM1P S)
;            (EQUAL (NTH 3 (RD :LOCALS S)) 1))
;       (IF
;        (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;        3
;        (CLK+
;         15
;         (CLK-6
;          (WR :PC 6
;              (WR :LOCALS (UPDATE-NTH 0 (+ (NTH 0 (RD :LOCALS S))
;                                           (- (NTH 3 (RD :LOCALS S))))
;                           (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                                            (NTH 1 (RD :LOCALS S)))
;                            (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                             (NTH 2 (RD :LOCALS S)))
;                                        (RD :LOCALS S))))
;                  S)))))
;       0))

; (DEFUN SEM-6 (S)
;   (IF (AND (HYPS S)
;            (PROGRAM1P S)
;            (EQUAL (NTH 3 (RD :LOCALS S)) 1))
;       (IF (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;           (WR :PC 22
;               (WR :STACK (PUSH (NTH 1 (RD :LOCALS S))
;                                (RD :STACK S))
;                   S))
;           (SEM-6
;            (WR :PC 6
;                (WR :LOCALS (UPDATE-NTH 0 (+ (NTH 0 (RD :LOCALS S))
;                                             (- (NTH 3 (RD :LOCALS S))))
;                             (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                                              (NTH 1 (RD :LOCALS S)))
;                              (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                               (NTH 2 (RD :LOCALS S)))
;                                          (RD :LOCALS S))))
;              S))))
;       S))

; The correctness theorems for the functions are easy to generate.  Just
; consider what it is, say for pc = 6:

; (DEFTHM SEM-6-CORRECT
;   (IMPLIES (AND (HYPS S)
;                 (PROGRAM1P S)
;                 (EQUAL (RD :PC S) 6))
;            (EQUAL (M1 S (CLK-6 S))
;                   (SEM-6 S))))

; Of course, the functions for the loops must be defined before the top-level
; functions, CLK-0 and SEM-0, and the correctness theorem for SEM-6 must be
; proved before that for SEM-0.  So implicit in the actual submission of these
; events is determining the call ordering of the definitions.

; If you inspect basic-demo.lsp you will see a trace$ command, just before
; def-semantics.  The trace$ command has been commented out.  If you undo back
; through the def-semantics, execute the trace$ command, and re-run
; def-semantics you will see some of the internals of def-semantics in action.
; We recommend that you only inspect the top-level entry and exit of the traced
; functions (the entries labeled ``1>'' and ``<1'').

; This completes our sketch of how def-semantics works.  We have left
; out a lot!  We provide more details in the next section ... and complete
; details in the code.

; We now move on to the def-projection commands illustrated in A Friendly
; Introduction to Codewalker section above.

; For convenience, here is the user's definition of the state invariant, (hyps
; s):

; (defun hyps (s)
;   (declare (xargs :stobjs (s)))
;   (and (sp s)
;        (natp (rd :pc s))
;        (< (rd :pc s) (len (rd :program s)))
;        (< 16 (len (rd :locals s)))
;        (natp-listp (rd :locals s))
;        (natp-listp (rd :stack s))))

; Now we turn to the question of ``projecting'' the result of a given semantic
; function so we can more easily understand what that function's effect is on a
; given state component.  Let's start with SEM-6 and consider its effect on
; reg[1], i.e., (nth 1 (rd :locals s)).  It helps to see the definition of SEM-6:

; (DEFUN SEM-6 (S)
;   (IF (AND (HYPS S)
;            (PROGRAM1P S)
;            (EQUAL (NTH 3 (RD :LOCALS S)) 1))
;       (IF (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;           (WR :PC 22
;               (WR :STACK (PUSH (NTH 1 (RD :LOCALS S))
;                                (RD :STACK S))
;                   S))
;           (SEM-6
;            (WR :PC 6
;                (WR :LOCALS (UPDATE-NTH 0 (+ (NTH 0 (RD :LOCALS S))
;                                             (- (NTH 3 (RD :LOCALS S))))
;                             (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                                              (NTH 1 (RD :LOCALS S)))
;                              (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                               (NTH 2 (RD :LOCALS S)))
;                                          (RD :LOCALS S))))
;              S))))
;       S))

; Suppose we want to project (nth 1 (rd :locals s)) from SEM-6 and name the
; resulting function FN1-LOOP.  (Def-Projection requires the user to name each
; function being introduced because the point of def-projection is to allow the
; user to understand the effects of a piece of code.  It helps if names ``make
; sense'' to the user.  Our naming convention in this example is that ``FN1''
; refers to to the function that computes the final value of reg[1] and
; ``LOOP'' refers to the fact that it does so starting from the loop in the
; code at pc 6.)

; Of course, we could just

; (defun fn1-loop (s) (nth 1 (rd :locals (sem-6 s))))

; but that is not very illuminating.  Our goal is for fn1-loop to actually
; compute the final value of reg[1] using just what it needs from state s and no
; more.  In particular, it should not take state as an argument!  It should
; take just the values of whatever state components are necessary to compute
; the final reg[1] -- and no others.

; The first step is to create the expression (nth 1 (rd :locals (sem-6 s))),
; expand the call of sem-6, and simplify.  The result is:

; (if (equal (nth 3 (rd :locals s)) 1)
;     (if (equal (nth 0 (rd :locals s)) 0)
;         (nth 1 (rd :locals s))
;         (NTH 1 (RD :LOCALS
;                    (SEM-6
;                     (wr :pc 6
;                         (wr :locals (update-nth 0 (+ -1 (nth 0 (rd :locals s)))
;                                      (update-nth 1 (* (nth 0 (rd :locals s))
;                                                       (nth 1 (rd :locals s)))
;                                       (update-nth 2 (+ (nth 0 (rd :locals s))
;                                                        (nth 2 (rd :locals s)))
;                                                   (rd :locals s))))
;                             s))))))
;     (nth 1 (rd :locals s)))

; Note: A careful look at SEM-6 reveals that in its recursion, register 0 is
; replaced by (+ (NTH 0 (RD :LOCALS S)) (- (NTH 3 (RD :LOCALS S)))), not (+ -1
; (nth 0 (rd :locals s))) as shown above.  The reason for the difference is
; that there is a governing hypothesis that (NTH 3 (RD :LOCALS S)) is 1.  One
; might ask why that hypothesis wasn't used to further simplify the definition
; of SEM-6.  The reason is that we discovered the invariant that (NTH 3 (RD
; :LOCALS S)) is 1 in this function after producing the preliminary body and we
; don't bother to further simplify the body after adding that invariant.

; Recall our goal is to define a new function FN1-LOOP and the expression above
; is the beginning of a body for it.  There are two things to note about this
; expression.  First, the occurrence of the expression

; (NTH 1 (RD :LOCALS
;             (SEM-6
;               <new-s>)))

; suggests that that is the place where the new function, FN1-LOOP, will be
; called recursively, since this expression denotes the value of reg[1] in
; another call of SEM-6.  There may be multiple places in the evolving body
; where we call FN1-LOOP recursively.  So it is handy to just abstract away
; those places, enumerating them with unquoted numbers, and build a table
; associating the numbers with the corresponding <new-s>.  So we build the
; ``term'' shown below for the abstracted body (with the ``unquoted numbers''
; here preceded by ``#'' hash marks):

; (if (equal (nth 3 (rd :locals s)) 1)
;     (if (equal (nth 0 (rd :locals s)) 0)
;         (nth 1 (rd :locals s))
;         #0)
;     (nth 1 (rd :locals s)))

; where we know that #0 denotes a recursive call on

; <new-s> = (wr :pc 6
;               (wr :locals (update-nth 0 (+ -1 (nth 0 (rd :locals s)))
;                            (update-nth 1 (* (nth 0 (rd :locals s))
;                                             (nth 1 (rd :locals s)))
;                             (update-nth 2 (+ (nth 0 (rd :locals s))
;                                              (nth 2 (rd :locals s)))
;                                         (rd :locals s))))
;                   s))))))

; The second important thing to note about this evolving body is that outside
; of the ``recursive call(s)'' -- that is, in the abstracted body above -- we
; see three state components.  These three state components will become
; variables in the definition we're writing:

; state component outside #0            new variable name to be used

; (nth 0 (rd :locals s))                   R0
; (nth 1 (rd :locals s))                   R1
; (nth 3 (rd :locals s))                   R3

; These variable names are generated by the :var-names setting in the API.

; But those state components (or variables, as they'll become) refer to the
; final values after the recursion implicit at #0.  Furthermore, to compute the
; final values of those components/variables variables we have to track how
; they change in the recursive call.  The recursive call of the function we're
; writing will NOT be on <new-s> but on the new values of the relevant state
; components.

; So an important next step is to figure out the values of the relevant state
; components in the <new-s> at each enumerated recursive call site, by
; simplification of

; (NTH 0 (RD :LOCALS <new-s>)),
; (NTH 1 (RD :LOCALS <new-s>)), and
; (NTH 3 (RD :LOCALS <new-s>)).

; Using the notation ``comp <-- val'' to mean ``state component comp is replaced
; in recursion by expression val'' we learn:

; (NTH 0 (RD :LOCALS s)) <-- (+ -1 (NTH 0 (RD :LOCALS S)))
; (NTH 1 (RD :LOCALS s)) <-- (* (NTH 0 (RD :LOCALS S)) (NTH 1 (RD :LOCALS S)))
; (NTH 3 (RD :LOCALS s)) <-- (NTH 3 (RD :LOCALS s)).

; It could be that the new value of one of our ``relevant vars'' in recursion
; is determined by some state component heretofore not identified as relevant.
; So we must iterate the identification of relevant components and what their
; new values are, until we have closed the set.  In this example, the relevant
; component was initially just that named reg[1], it became reg[0], reg[1],
; reg[3], and that is closed.  So we don't track how reg[2] changes.

; So, after using :var-names to generate the new variable names for reg[0],
; reg[1], and reg[3], namely R0, R1, and R3, we get the actuals at this call
; site:

; R0 <-- (+ -1 R0)
; R1 <-- (* R0 R1)
; R3 <-- R3

; We then introduce the recursive calls of the function we're defining,
; FN1-LOOP, at the enumerated sites, on the new actuals.  So #0 is replaced by
; (FN1-LOOP (+ -1 R0) (* R0 R1) R3).

; We also endeavor to capture the restrictions on the relevant state
; components/variables imposed by the state invariant and the user's
; declarations of the types of certain components.  By ``capture the
; restrictions ... imposed by the state invariant'' we mean ``what does (and
; (hyps s) (program1p s)) tell us about R0, R1, and R3?''  Of course, it tells
; us nothing about those variables!  But it does tell us things about (nth 0
; (rd :locals s)), etc.  The question is how do we isolate from (and (hyps s)
; (program1p s)) just the parts about the relevant state components?  We
; explain later but it is an important step because the termination of SEM-6
; probably depends on some parts of the ``good state invariant'' and thus the
; termination of FN1-LOOP will probably depend on the parts of that invariant
; about these components.

; Moving on, for sanity we want the formal parameters of FN1-LOOP to be in
; alphabetical order.  But we initially don't know what all the parameters are.
; So we actually build expressions with the actuals of FN1-LOOP in the ``wrong
; order'' and then build a ``permutation map'' to tell us how we swap arguments
; to put them into order by formal name, and apply that map to all of our
; definitions when we're done.

; When we are done, the definition of FN1-LOOP is:

; (DEFUN FN1-LOOP (R0 R1 R3)
;   (COND ((OR (NOT (INTEGERP R3))
;              (< R3 0)
;              (NOT (INTEGERP R0))
;              (< R0 0)
;              (NOT (INTEGERP R1))
;              (< R1 0))
;          0)
;         ((OR (NOT (EQUAL R3 1)) (EQUAL R0 0))
;          R1)
;         (T (FN1-LOOP (+ -1 R0) (* R0 R1) 1))))

; Note that the definition does not track the changes to R2: it is not relevant
; to the final value of R1.

; The correctness theorem reveals and records the mapping from state components
; to formals:

; (DEFTHM FN1-LOOP-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '1 (RD ':LOCALS (SEM-6 S)))
;                   (FN1-LOOP (NTH '0 (RD ':LOCALS S))
;                             (NTH '1 (RD ':LOCALS S))
;                             (NTH '3 (RD ':LOCALS S))))))

; There is one more subtlety worth pointing out.  Suppose we've done the
; projection above and then apply this same technique to derive the value of R1
; starting from SEM-0, defining the new function FN1.  We form

; (NTH 1 (RD :LOCALS (SEM-0 S)))

; and then expand SEM-0 and simplify under (hyps s).  The result is:

; (NTH 1 (RD :LOCALS (SEM-6 <new-s>))).

; But what we want is for this expression to be replaced by:

; (FN1-LOOP (NTH 0 (RD :LOCALS <new-s>))
;           (NTH 1 (RD :LOCALS <new-s>))
;           (NTH 3 (RD :LOCALS <new-s>)))

; So that we can then replace the state components ``outside'' the recursive
; calls -- there aren't any recursive calls of (NTH 1 (RD :LOCALS (SEM-0
; ...)))) -- and derive the preliminary definition of (FN1 R0) to be (FN1-LOOP
; R0 1 1) which we then protect with the tests from (hyps s) to get:

; (DEFUN FN1 (R0)
;   (IF (OR (NOT (INTEGERP R0)) (< R0 0))
;       0
;       (FN1-LOOP R0 1 1)))

; But how does def-projection introduce FN1-LOOP?  How does def-projection know
; that the register 1 projection of SEM-6,

; (nth 1 (rd :locals (SEM-6 <new-s>))),

; is computed by an already projected function, namely:

; (FN1-LOOP (NTH 0 (RD :LOCALS <new-s>)) ...)?

; The answer is really simple: Since FN1-LOOP was proved correct with the
; FN1-LOOP-CORRECT theorem shown above, and since that theorem is now in the
; :rewrite rule database, it is applied as we simplify

; (NTH 1 (RD :LOCALS (SEM-0 S)))

; after SEM-0 is expanded.

; Finally, it is possible that we have not yet projected a given component from
; a given semantic function occurring in the body of the semantic function
; we're trying to project.  If this occurs, the ``final'' body described above
; will still contain other semantic functions.  (Imagine trying to project R1
; from sem-0 before we have projected R1 from sem-6.)  We detect this and
; advise the user to project that component from that other semantic function
; first.  We could, in principle, do it recursively, but we prefer the user to
; name each projection.

; This completes the walk through of a def-projection example.

; =============================================================================
; Guide to the Implementation of Codewalker

; -----------------------------------------------------------------------------
; Background on Supporting Books

; The Codewalker book depends on three supporting books:

; if-tracker.lisp
; simplify-under-hyps.lisp
; terminatricks.lisp

; The first two provide us with the ability to simplify a term under some
; hypotheses and recover an equivalent term.  This is a bit tricky since the
; ACL2 simplifier splits terms into clauses.  The challenge, overcome by
; if-tracker and simplify-under-hyps, is to take the resulting set of clauses
; and reassemble a term, minus the hypotheses that were assumed.

; The file terminatricks.lisp is the current incarnation of the Terminatricks
; book.  Terminatricks is documented with extensive comments but we sketch its
; basic functionality here.  Terminatricks provides the new macros DEFUNM and
; DEFUNM-NX which are like DEFUN and DEFUN-NX except do not require :measures.
; Instead, DEFUNM and DEFUNM-NX use heuristics to try to guess an appropriate
; measure for the definition.  These heuristics are derived from a table of
; ``measure patterns'' that look for certain subterms in the proposed
; definitions and conjecture the relevance of certain measures.  The measure
; patterns table may be augmented directly by the user but most often it is
; augmented by mining DEFUN events for which a user supplied an explicit
; :measure.

; Given a table of measure patterns and a proposed definition, Terminatricks
; first collects every measure that is suggested for each call and its
; governing tests.  Then it attempts to prove, on a call-by-call basis, that
; suggested measures decrease or do not increase.  Finally, it attempts to
; piece together lexicographic orderings of measures to explain all the calls.

; Codewalker uses the Terminatricks facilities often and freely.  In
; particular, Codewalker generates clock, semantic, and projection functions
; and -- unless user-supplied hints provide :measures -- DEFUNM/DEFUNM-NX is
; used to admit them.  So Codewalker critically depends on Terminatricks to
; figure out why these functions terminate.  Unfortunately, Terminatricks is
; not as powerful as it might be -- the problem is, after all, undecidable!  So
; sometimes we see def-semantics or def-projection fail, when in fact the
; failure ``belongs'' to Terminatricks.

; Terminatricks introduces two concepts that are used directly in Codewalker.
; The concepts are that of ``virtual formal'' (or ``vformal'') and the
; associated idea of a ``call on virtual formals'' more often referred to
; (misleadingly) as a ``virtual call''.  Suppose st is a list of numbers and
; you see a recursive function like:

; (defun foo (st)
;   (if (zp (nth 2 st))
;       st
;       (foo (update-nth 1 (+ (nth 1 st) (nth 2 st))
;             (update-nth 2 (+ (nth 2 st) -1)
;               st)))))

; Clearly, the decreasing measure is (acl2-count (nth 2 st)).  But ACL2's
; native DEFUN will not guess this, even though it would have no trouble with:

; (defun foo' (n1 n2)
;   (if (zp n2)
;       (list n1 n2)
;       (foo' (+ n1 n2) (+ n2 -1))))

; We call (nth 1 st) and (nth 2 st) of foo above ``virtual formals'' or
; ``vformals''.  Technically, a virtual formal is any structure component that
; is being tested or changed in a definition, where the notion of a
; ``component'' is as described by two Terminatricks tables
; generalized-updater-drivers and constructor-drivers, which we discuss further
; below.  (The former table contains the :updater-drivers setting from your
; API, the latter contains the :constructor-drivers.)

; See changed-virtual-formal-slots in terminatricks.lisp for the function that
; computes the vformals in a term.

; It is convenient to re-represent some function calls to make the
; virtual formals and their assignments more obvious.  Given a call like:

;       (foo (update-nth 1 (+ (nth 1 st) (nth 2 st))
;             (update-nth 2 (+ (nth 2 st) -1)
;               st)))

; we sometimes re-represent it as a ``call on virtual formals'' (or ``virtual
; call'') this way:

; (foo (:slot (nth 1 st) (+ (nth 1 st) (nth 2 st)))
;      (:slot (nth 2 st) (+ (nth 2 st) -1)))

; where, unlike normal calls, there may be different number of :slot
; expressions in each virtual call of foo.

; By explicitly identifying the state components being tested/manipulated in a
; recursive function we make it a little easier to identify measures that are
; decreasing.

; The idea of virtual formals rears its head in Codewalker at the
; user-interface level because Codewalker uses Terminatricks and Terminatricks
; uses the two tables, generalized-updater-drivers and constructor-drivers
; described below, to identify virtual formals.  It also arises in the
; description of the implementation of Codewalker because Codewalker detects
; certain trivial invariants by analyzing calls on virtual formals.

; -----------------------------------------------------------------------------
; Data Structures Driving Codewalker

; Three tables drive Codewalker.  These tables are set by the def-model-api
; command.  The model API is a record that tells Codewalker such things as:

; - the name of the run function
; - the name of the step function
; - the name of the state variable and whether it is a stobj
; - how to set the pc in a state
; - how to retrieve the pc from a state
; - how to add two clocks together

; This API allows Codewalker (both def-semantics and the def-projection
; command) to access the functionality of the machine model, without building
; in any particular model (e.g., X86, PCODE, M1, etc.).  The various fields of
; an API are supplied in untranslated form to def-model-api, which translates
; and error checks the fields and stores them into a record named model-api
; which, in turn, is stored in a table of the same name.

; See the defrec of model-api.

; There are two other global data structures, both represented by tables.  They
; are actually used by Terminatricks but since Codewalker uses DEFUNM/DEFUNM-NX
; they are also set by def-model-api from the fields of similar names.  The two
; tables are

; generalized-updater-drivers
; constructor-drivers

; These are described and exemplified in terminatricks.lisp.  But typical
; settings for the two tables might be:

; (table generalized-updater-drivers
;        :list
;        '(((update-nth i :value :base)       ; doublets consisting of
;           (nth i :base))                    ; an update expression and
;          ((wrm offset size :value :base)    ; corresponding access
;           (rdm offset size :base))          ; expression.  Such expressions
;          ((!i :value :base)                 ; are typically nested in
;           (i :base))                        ; the :base argument position
;          ((!s :value :base)
;           (s :base))))

; Obviously, in the model hinted at above, wrm writes a :value of size at
; address offset in the memory of :base, and rdm reads it.  Similarly,
; !i sets the instruction pointer and i fetches it, and !s sets the status
; flag and s fetches it.

; (table constructor-drivers
;        :list
;        '(((cons a b)                        ; lists consisting of a
;           (car :base) (cdr :base))))        ; constructor expression and
;                                             ; the corresponding n accessor
;                                             ; expressons.  Accessors may
;                                             ; appear nested in the :base
;                                             ; argument.

; From the perspective of Codewalker, the first table,
; generalized-updater-drivers, is relevant if the state object in the model is
; a stobj or, more generally, the model is in the ``state updater paradigm.''
; By that we mean that whenever the model needs to describe a new state it does
; so by ``updating'' the (an) old state, as by applying update-nth or, more
; generally, a stobj or record updater.

; The second table, constructor-drivers, is only relevant for machine models
; that use the ``state constructor paradigm'' -- where each instruction's
; semantics explicitly constructs a new state with CONS or some higher level
; function like M1's MAKE-STATE.

; Almost all practical ACL2 machine models are stobj-based and thus are in the
; updater paradigm.  But these tables are used by Terminatricks and
; Terminatricks can be used independently of Codewalker.  The second table is
; needed anytime Terminatricks is dealing with functions that recur by CONSing.

; An obvious flaw in the current implementation is that def-model-api transfers
; the contents of :updater-drivers and :constructor-drivers to Terminatricks'
; generalized-updater-drivers and constructor-drivers tables, without
; preserving any entries already in those tables.  A user who is using DEFUNM
; to define functions might have configured Terminatricks tables to identify
; the virtual formals in the kinds of functions being defined -- functions that
; need not be manipulating the state of any particular model.  If that user
; then starts using Codewalker, the def-model-api will smash the carefully
; constructed Terminatricks tables so they are suitable for the API in use but
; possibly no longer suitable for the other kinds of functions the user may end
; up defining with DEFUNM.  It would be better if Codewalker somehow merged the
; API's entries into the Terminatricks tables.

; -----------------------------------------------------------------------------
; Overviews of How the Def-Semantics and Def-Projection Commands Work

; Below we give overviews of the steps taken by both def-semantics and
; def-projection.  Each step is identified by a token, (A.1), (A.2), ...
; for def-semantics and (B.1), (B.2), ... for def-projection.  After these two
; high level sketches we detail each of the steps, repeating the tokens.
; Finally, the Code itself sometimes refers to these tokens.

; Overview of How Def-semantics Works

; def-semantics works in seven main steps:

; (A.1) compute a conservative (over-estimate of the) control flow graph of the
;       program

; (A.2) identify loops and halts, the so-called ``cutpoints''

; (A.3) simulate from cutpoint to cutpoint to get composed state transitions,
;       called path-tree expressions, along all paths

; (A.4) compute reflexive-transitive closure of cutpoint-to-cutpoint relations
;       to construct a call graph, inducing an order on the clock and semantic
;       functions

; (A.5) define clock and semantic functions from the path-tree expressions;
;       this would be straightforward except for two important additions:
;       (A.5.1) identifying certain trivial invariants that may be crucial to
;               termination, and
;       (A.5.2) removing mutual recursion.

; (A.6) generate the correctness theorem relating the clock and semantic
;       functions

; (A.7) apply the user-supplied :annotations argument to the generated events

; We deal with each step in turn below, repeating verbatim the enumerated header.

; ---
; Overview of How the Def-Projection Command Works

; The def-projection command works in eight main steps:

; (B.1) given a projector term (specifying the state component of interest) and a
;       semantic function, create the term (projector (semantic st)), expand
;       the semantic function call and simplify

; (B.2) find every state component referenced outside the projected recursive
;       calls and collect the state component and its type; these are the
;       initially relevant components

; (B.3) replace all projected recursive calls of the semantic function by
;       unquoted naturals and build an alist mapping those naturals to the new
;       states inside those calls

; (B.4) for each site, determine the new value of each of the relevant state
;       components in the new state at that site; close the set of relevant
;       components by iteration

; (B.5) introduce calls of the new function at each site, generalizing the
;       relevant state components and their occurrences in the actuals

; (B.6) determine the restrictions imposed by the invariant on the relevant state
;       components

; (B.7) rearrange all the definitions' formals and calls so that formals are
;       in alphabetical order

; (B.8) determine whether there are other projected state components that
;       still occur in the body and if so cause an error

; -----------------------------------------------------------------------------
; More Details on def-semantics

; As noted, def-semantics works in seven main steps.  Below we repeat
; verbatim the ``A'' headers describing each step and elaborate a little.

; ---
; (A.1) compute a conservative (over-estimate of the) control flow graph of the
;       program

; The first piece of functionality we develop is to build graphs that capture
; (over approximate) control flow.  The graph is represented by an adjacency
; alist with entries of the form (pc . (pc_1 ... pc_k)) meaning the graph has a
; directed edge from pc to each of the pc_i.  We actually build two graphs,
; one forward and one backwards.

; In the forward link ``flink'' graph, an edge from pc to pc_i means that when
; the instruction at pc is executed, the instruction at pc_i may be the next
; instruction, e.g., control may transfer in one step from pc to pc_i.  In the
; backward link ``blink'' graph an edge from pc to pc_i means that the
; instruction at pc may be the next instruction after the one at pc_i is
; executed, i.e., control may reach pc in one step from pc_i.

; In both cases, no context is kept.  For example, if the instruction at pc
; branches to either pc_1 or pc_2, then both are included in the flink graph
; entry from pc, even if it turns out that context tracking and theorem proving
; could show that the value of the test is known.

; The two graphs are constructed by the function link-graphs.  But the key
; idea in the construction is the function next-pcs, which takes a given pc
; value and simplifies the expression:

; (get-pc (step (set-pc pc st)))

; under the state invariant hypothesis (:hyps) provided to def-model-api.  (By
; the way, this idea of simplifying an expression under a hypothesis is used
; repeatedly in this work and is managed by the function simplify-under-hyps
; which is defined in the book of the same name.)

; The result of that simplification should be an IF expression with a lot of
; pcs at the tips.  After the simplification, next-pc scans the IF-expression
; and collects all the constant pcs, throwing away the tests since we carry
; no context information forward from one instruction to the next in
; constructing this conservative over-approximation flow graphs.

; Suppose the instruction at pc 1 sets reg0 to 0 and advances to pc 2, and
; suppose the instruction at pc 2 tests reg0 and branches to 3 or 30.  In this
; pass, we process the instruction at pc 1 independently of that at pc 2, i.e.,
; we don't take the simplified state from pc 1 and carry in forward into pc 2.
; So in this pass we say pc 1 transitions forward to pc 2 and that pc 2
; transitions forward to either 3 or 30.  If we simplified the instruction at
; pc 2 with respect to the state produced by pc 1 we could detect that reg0 is
; 0 and one branch would be pruned.  But that risks state-explosion and
; combinatoric problems before we even know where the loops are.  The
; overapproximation of the flow is set up in linear time since each instruction
; is processed once, independently of all others.

; ---
; (A.2) identify loops and halts, the so-called ``cutpoints''

; Next, we wish to identify the ``loops,'' the ``branches,'' and the ``halts''
; in the code.  Loops are those pcs, x, such that one of the jumps to x is from
; a pc greater than x, i.e., one of the jumps to x is a ``back jump.''  The
; branches are where the forward flow diverges, i.e., where a pc in the forward
; graph has multiple next pcs.  (Note: The concept of branches is actually
; irrelevant to our analysis.  We thought we might need it and so compute it but
; it turns out that as of codewalker.lisp, the concept is ignored.)  The ``halts''
; are places where the forward flow graph lists ONLY the pc itself as the next
; pc.  The ``cutpoints'' are the union of the loops and the halts plus the
; entry pc.

; Given that pcs need not always be numbers, e.g., (5 . 3) might be a pc in
; some model, how do we determine whether one pc occurs before another?  We use
; lexorder!  Thus, if one is coding up some ``strange'' notion of pc, code it
; in such a way that (lexorder pc1 pc2) means that pc1 occurs before pc2 in
; ``normal'' program flow.  If this built-in sense of order is too specific we
; could add some kind of ordering relation to the collection of functions
; identified in the machine description API.

; Instructions that may or may not change the pc are problematic.  Such
; behavior can mean different things.  For example, consider a DIV instruction
; which advances the pc if the denominator is non-0 but which does not change
; the pc if the denominator is 0.  DIV might even make other state changes,
; such as setting an error condition somewhere in the state.  So it is possible
; for a useful instruction to not change the pc even though it changes other
; state components.  And it is not clear from the analysis of the pc alone
; whether this is an error event or just an intermediate transition.

; For a clear example of the ``intermediate transition,'', consider an
; instruction which might be named POP-ACCUMULATE (or more likely, a block
; transfer like instruction).  Suppose POP-ACCUMULATE advances the pc if the
; stack is empty and otherwise pops the stack, adds the item to the contents of
; register a, but does NOT change the pc!  One could use such an instruction to
; sum the items on the stack.  Repeated steps would eventually empty the stack
; and advance the pc, but it would take as many clock cycles to complete as
; there are items on the stack.  It wouldn't actually be halting the machine
; despite the unchanged pc, and it wouldn't even be an error event: it's just a
; useful instruction that takes many cycles to complete.

; The question then is how does def-semantics handle such problematic
; instructions?  In particular, what clock does it generate?  Answer: when an
; instruction doesn't change the pc, the clock stops.  So this means def-semantics
; handles DIV, above, correctly but is not quite appropriate for
; POP-ACCUMULATE.  If we could detect (or be told) that an instruction just
; takes time to complete but doesn't REALLY halt the machine -- or if we could
; be told that there is some error flag in the state that distinguishes these
; two situations, we might improve the situation.  These possibilities suggest
; additions to the API but so far haven't been explored, as we haven't seen an
; instruction like POP-ACCUMULATE and DIV is handled correctly by this
; approach.

; The function for identifying loops, etc, is categorize-pcs.

; ---
; (A.3) simulate from cutpoint to cutpoint to get composed state transitions,
;       called path-tree expressions, along all paths

; Next, given a list of all the cutpoints (entry pc plus the union of the loops
; and the halts), we simulate forward from each cutpoint to the next cutpoint.
; This simulation is compositional.  That is, we start at a cutpoint and
; repeatedly step, passing the new symbolic state expression into the next
; instruction (risking state explosion) stopping only when we encounter another
; cutpoint.  We repeatedly rewrite and normalize -- as part of the normal ACL2
; simplifier -- and thus create a (possibly large) IF-expression as we go
; through multiple tests in the code.  We want to keep track of the number of
; steps taken and also the path pursued to reach each state at the tips of this
; tree.

; We do this with a fairly clever rewriting hack.  In particular, we introduce
; two functions, codewalker-wrapper and codewalker-tip, and three rewrite rules
; to manipulate such expressions.  Codewalker-tip expressions look like this:

; (CODEWALKER-TIP k (pc_0 pc_1 pc_2 ... pc_k) splitters s-final)

; and the function symbol itself is just defstub'd, i.e., left undefined.  In
; these codewalker-tip expressions k is the number of steps taken to get to the
; final state reached, s-final, and list of pc_i show the path from the
; cutpoint (pc_0) we started at to the pc, pc_k, of s-final.

; CODEWALKER-WRAPPER, on the other hand, is a defined function whose definition
; cannot be produced until we know the cutpoints -- so you won't find its
; definition in the tag table!  Instead, it is introduced internally to the
; make-event, after we've classified the pcs as above.  See wrapper-events
; for the function that creates its definition, but the scheme is shown below.

; CODEWALKER-WRAPPER expressions look like this:

; (CODEWALKER-WRAPPER cnt rpath known-cutpoints splitters depth s)

; which is defined to step s repeatedly until its pc is a member of
; known-cutpoints.  It counts the number of steps it takes and accumulates into
; rpath (reversed path) the list of pcs it visits.  It also accumulates into
; splitters the pcs causing branches and increments depth until it reaches the
; given *snorkel-depth*.  When it reaches a known cutpoint, it replaces itself
; with: a CODEWALKER-TIP expression.

; The definition of CODEWALKER-WRAPPER and the three rules about it are shown
; below, but it can't be expanded until we have the API for the machine
; (telling us the functions for manipulating these machine states) and the
; cutpoints.  But the ``meta-definitions'' should be clear.  We use the Common
; Lisp back-quote notation below and you should understand ``,s'' to mean the
; machine state name from the API and ``,get-pc'' to mean the term from the API
; for fetching the current pc from the machine state.

; (defun-nx codewalker-wrapper (cnt rpath known-cutpoints splitters depth ,s)
;   (declare (xargs :measure (nfix (- *snorkel-depth* (nfix depth)))))
;   (if (or (not (natp depth))
;           (>= depth *snorkel-depth*))
;       (codewalker-wrapper-snorkeler cnt rpath known-cutpoints
;                                     splitters depth s)
;       (if (or (member-equal ,get-pc rpath)
;               (and rpath
;                    (member-equal ,get-pc
;                                  known-cutpoints)))
;           (codewalker-tip cnt
;                           (revappend (cons ,get-pc rpath) nil)
;                           splitters
;                           ,s)
;           (codewalker-wrapper (+ 1 cnt)
;                               (cons ,get-pc rpath)
;                               known-cutpoints
;                               splitters
;                               (+ 1 depth)
;                               (,step ,s)))))
;
; (defthm codewalker-wrapper-rule-1
;   (implies
;    (and (natp depth)
;         (>= depth *snorkel-depth*))
;    (equal (codewalker-wrapper cnt rpath known-cutpoints
;                               splitters depth ,s)
;           (codewalker-wrapper-snorkeler cnt rpath known-cutpoints
;                                         splitters depth ,s))))
;
; (defthm codewalker-wrapper-rule-2
;   (implies
;    (and (natp depth)
;         (< depth *snorkel-depth*)
;         (equal pc ,get-pc)
;         (syntaxp (quotep pc))
;         (or (member-equal pc rpath)
;             (and rpath
;                  (member-equal pc known-cutpoints))))
;    (equal (codewalker-wrapper cnt rpath known-cutpoints
;                               splitters depth ,s)
;           (codewalker-tip cnt
;                           (revappend (cons pc rpath) nil)
;                           splitters
;                           ,s))))
;
; (defthm codewalker-wrapper-rule-3
;   (implies
;    (and (natp depth)
;         (< depth *snorkel-depth*)
;         (equal pc ,get-pc)
;         (syntaxp (quotep pc))
;         (not (or (member-equal pc rpath)
;                  (and rpath
;                       (member-equal pc known-cutpoints))))
;         (equal s1 (,step ,s))
;         (bind-free (update-codewalker-splitters
;                     ,s s1 pc splitters)
;                    (splitters1)))
;    (equal (codewalker-wrapper cnt rpath known-cutpoints
;                               splitters depth ,s)
;           (codewalker-wrapper (+ 1 cnt)
;                               (cons pc rpath)
;                               known-cutpoints
;                               splitters1
;                               (+ 1 depth)
;                               s1))))

; As noted, these rules keep forcing us to step the machine until we reach a
; cutpoint (or exhaust a natural number limit on the number of steps explored
; along a path, or reach a pc that is not a constant).  So by forming
; `(CODEWALKER-WRAPPER '0 'NIL ',known-cutpoints nil 0 ,(make-fn-application
; put-pc (list (kwote cutpoint) s))) and simpifying it under the hyps, we get a
; normalized IF-expression with CODEWALKER-TIP terms at all the non-tested
; exits.  That is called a ``path-tree.''

; The functions that build path-trees are path-tree-tuple-from-cutpoint and
; path-tree-tuples-from-cutpoint-lst.

; ---
; (A.4) compute reflexive-transitive closure of cutpoint-to-cutpoint relations
;       to construct a call graph, inducing an order on the clock and semantic
;       functions

; Each cutpoint gives rise to a (possibly) recursive function.  E.g., if pc=4
; is a cutpoint, there will be functions with names like CLK-4 and SEM-4.
; Given a list of several cutpoints, in which order should their functions be
; introduced?  (From our current perspective, it suffices to treat the pcs
; themselves as the function names.)

; Suppose we have five cutpoints and there are simulated paths from one to
; another as indicated by the graph:

; ((1 2) (2 3) (3 4 5) (4 2) (5)).

; This means that simulating forward from cutpoint 1 we reach cutpoint 2, from
; 2 we reach 3, from 3 we reach both 4 and 5, etc.  Each corresponds to a
; function.  In what order do we introduce those functions?

; To determine the order we first compute the reflexive, transitive closure of
; the cutpoint reachability relation, storing for each cutpoint the cutpoints
; (somehow) reachable from it:

;  ((1 . (1 2 3 4 5))  ; meaning 1 (somehow) calls (1 2 3 4 5)
;   (2 . (2 3 4 5))
;   (3 . (2 3 4 5))
;   (4 . (2 3 4 5))
;   (5 . (5)))

; Then if we order these by subset, so 5 is defined first, then
; 2, 3, and 4 which all have the same set of reachable cutpoints (and are thus
; mutually recursive) and finally 1.

; This is actually done in the Terminatricks book because Terminatricks uses
; the same ordering technique to assign weights to mutually recursive
; cutpoints.

; See the function call-graph-ordering.  In particular,
; (call-graph-ordering '((1 2) (2 3) (3 4 5) (4 2) (5)))
; =
; ((5) (2 3 4) (1)).

; ---
; (A.5) define clock and semantic functions from the path-tree expressions;
;       this would be straightforward except for two important additions:
;       (A.5.1) identifying certain trivial invariants that may be crucial to
;               termination, and
;       (A.5.2) removing mutual recursion.

; Next, we build clock and semantic function definitions for each cutpoint from
; the path-tree for that cutpoint.

; Every path-tree corresponds to a cutpoint.  Let the initial pc in the
; path-tree be pc.  Then we define a clock function, named something like
; CLK-pc, and a semantic function, SEM-pc, that takes a state and returns a
; state.  For the clock function body, we take the path-tree and eliminate all
; the codewalker-tips, leaving the tests in place and replacing the tips with
; the sum of the step count to the tip plus a call of the CLK-pc' function,
; where pc' is the pc at the tip.  We do an analogous thing to produce the body
; of the semantic functions except we replace the tips with the call of SEM-pc'.

; (Of course, if the tip is a terminal cutpoint -- e.g., we've reached a HALT
; or [eventually] a RETURN, or exited the region of code we're supposed to
; explore -- we don't generate the CLK-pc' or SEM-pc' recursive calls and just
; return the count or state as appropriate.

; The functions that do this are: generate-clock-function-body and
; generate-semantic-function-body.

; However, the results they return are not exactly the ones ultimately
; submitted by def-semantics!  The results of the two functions above are called
; the ``preliminary'' definitions of the clock and semantic functions.  We
; process them further:

;       (A.5.1) identifying certain trivial invariants that may be crucial to
;               termination, and
;       (A.5.2) removing mutual recursion.

; We sketch those two processes now.

; Regarding (A.5.1) the ``trivial invariants,'' consider our initial example,
; *program* above, in which the semantic function SEM-6 has a virtual call
; :slot like:

;  (:slot (nth 0 (rd :locals st))
;         (- (nth 0 (rd :locals st)) (nth 3 (rd :locals st)))).

; That is, in the colloquial, we are dealing with a recursion in which
; R0 <-- R0 - R3.

; Clearly, in the absence of additional information, this vformal is not
; decreasing.  But suppose that (nth 3 (rd :locals st)) is held constant in the
; recursion of SEM-6 and suppose that in every external virtual call of SEM-6,
; we have (:slot (nth 3 (rd :locals st)) 1).  Then SEM-6 is subtracting 1 from
; R0 as it recurs, it's just that the 1 is found as a constant value in some
; other vformal, R3.  We are prepared for a vformal to take on several
; different constant values, e.g., R3 might be 1 or 2 in some function, but
; never any other value.

; We detect such ``disguised constants'' by processing the preliminary clock
; and semantic function definitions with an iterative process that propagates
; constant settings through a system of function definitions.  We make two
; really basic assumptions.  First, the top-level entry to the system may be
; called with any arguments (satisfying the state invariant :hyps) so external
; context must be captured by the state invariant.  Second, all the functions
; in the system are called on the state and hence, if g calls f and certain
; things are known about the status of various vformals in g, then those same
; things are propagated to f unless they're overridden by explicit vformal
; settings in the call of f from g.  For example, if it can be deduced that
; R3 = 1 in g and then g calls f with a virtual call of

; (f (:slot R2 23))

; then we know R3=1 in f, because the actual (not virtual) call of f from g is
; on (f (wr :locals (update-nth 2 23 (rd :locals s)) s)), so everything we know in
; g about state components of s are known to hold in f except those involving
; components explicitly assigned in the call to f.

; For every vformal we build an alist that pairs the vformal with either
; :CHANGING, meaning we know nothing about it or with a true list of evgs,
; meaning that in every call seen so far the vformal has one of those constant
; values.  We start by assuming all vformals used by the top-level entry are
; :changing and repeatedly propagate this information (appropriately modified
; via the virtual calls in that function) through all other functions.  We stop
; when the data collected from one pass is the same as that from the last.  We
; keep the collected constants in lexorder to insure that an equality test will
; suffice.  We also build in a maximum number of iterations, just in case.
; When we finish, we have, for every function (pc) in the system, a data
; structure that tells us all the vformals that are always (one of several)
; constants in every call of that function.  We then turn those discoveries
; into hypotheses about each function, e.g., (member (nth 3 (rd :locals s)) '(1
; 2)) whenever we're inside a given function, and then modify the preliminary
; definition of each function by adding the discovered hypotheses to the state
; invariant for each function.  The relevant functions are:

; generate-fn-to-pc-and-vcalls-alist -- transform preliminary defuns to just
;   their virtual calls

; disguised-constant-4-tuple-lst -- identification of disguised constants and
;   their lexordered ranges in the form of a list of 4-tuples, each of the form
;   (fn pc v_i u'_i), where u'_i is the lexordered range of the disguised
;   constant v_i in fn (which was derived starting at pc).

; disguised-constant-hyp -- creates a hyp expressing the discovered invariants

; modify-hyps-in-defun-pairs -- adds the discovered hyp to the preliminary
;  defuns

; Regarding (A.5.2) the handling of mutual recursion, it should be noted that
; mutually recursive clock and semantic functions occur when we encounter
; nested loops.  For example, the semantic function for the outer loop will
; call that for the inner, and that for the inner will call back to the outer
; when it is done.  But ACL2 does not handle mutual recursion well: it cannot
; do inductions.

; So we transform mutually recursive defuns of clock and semantic functions
; into singly-recursive definitions that use the pc as the flag.  This is done
; toward the very end of the processing.  In particular, all the analysis
; described above takes place on ``function symbols'' that are (in principle)
; mutually recursive.  So, for example, SEM-2 may call itself and SEM-10 and
; SEM-10 may similarly call itself and SEM-2.  Even the names SEM-2 and SEM-10
; are used to identify the functions being ``defined'' and their subroutines.
; But after we have modified each function definition with its discovered
; disguised constant hypotheses, we look at the call-graph-ordering and may
; determine that SEM-2 and SEM-10 are mutually recursive.  At that point we
; invent a new name, e.g., SEM-2-10, and create a new body by combining (and
; renaming the functions called within) the bodies of the two functions.  This
; mapping of several distinct proto-function definitions into one is done by
; apply-call-graph-ordering-to-defun-pairs, which uses the function
; transform-to-singly-recursive to do the transformation the name suggests.
; There is an essay about that transformation in the code.

; The results are a list of DEFUNM/DEFUNM-NX events, in the right order, for
; the clock and semantic functions.

; ---
; (A.6) generate the correctness theorem relating the clock and semantic
;       functions

; The final step in this whole process is to generate the correctness theorems.
; This is pretty simple: for every cutpoint we know the clock and semantic
; function, and we know the initial pc and the state invariant, hyps.  So the
; correctness theorem is

; (implies (and ,@hyps
;               (equal (get-pc st) pc))
;          (equal (run st (clk-pc st))
;                 (sem-pc st)))

; The correctness theorem is generated by generate-correctness-theorem.

; Of course, if SEM-2 and SEM-10 are mutually recursive, then instead of
; generating the theorem above (which would be about those non-existent
; function symbols) we generate the corresponding theorem about clk-2-10 and
; sem-2-10.

; Then, cleverly, Terminatricks knows how to guess weights on the flags so help
; find a measure that decreases.

; ---
; (A.7) apply the user-supplied :annotations argument to the generated events

; def-semantics allows the user to specify some :annotations that may
; modify the automatically generated events.

; Annotations will be an alist and each pair in it will be of one of two
; shapes:

; (name (DECLARE ...)) -- means that name is the name of a generated defun-like
;  event and the automatically generated declarations are to be replaced in
;  their entirety by the given DECLARE form.  Furthermore (!!!), the DEFUNM-NX
;  that would have been generated becomes a standard ACL2 DEFUN-NX!  That is,
;  providing an entire DECLARE means that the user is using def-semantics to
;  generate the body but is taking over the admission entirely.

; (name :keyword . rest) -- means different things depending on what sort of
;   generated event has the given name.

;   * If name is defun-like, :keyword and everything following it is added to
;     the front of the automatically generated XARGS, so that (DECLARE (XARGS
;     . auto-xargs)) becomes (DECLARE (XARGS :keyword ,@rest . auto-xargs))
;     Thus, adding an :in-theory (for example) annotation means that the user
;     is just telling def-semantics to go ahead with its guesses but here are some
;     hints.

;   * If name is a defthm, :keyword must be :hints and it and everything
;    following it are added to the generated defthm in the :hints position.

;  Note that we don't actually know what sort of event name there is until we're
;  asked to add the appropriate annotation.  So our pre-processing error
;  checking on annotations is limited.  However, when we attempt to use an
;  annotation pair we check more and might cause a hard error.

; The application of :annotations to the generated events is scattered around
; the code in the functions:

;  generate-clock-function-defun-pair
;  generate-semantic-function-defun-pair
;  transform-to-singly-recursive
;  generate-correctness-theorem

; In general, to find these locations, search for :annotations, specifically
; where we (assoc-eq :annotations dsem-alist) which is the idiom for extracting
; the translated annotations from the alist holding all the arguments to
; def-semantics.

; This completes the sketch of how def-semantics works.

; ---
; More Details on the Def-Projection Command

; As noted, the def-projection command works in eight main steps.  Below we
; repeat verbatim the headers describing each step and elaborate a little.

; ---
; (B.1) given a projector term (specifying the state component of interest) and a
;       semantic function, create the term (projector (semantic st)), expand
;       the semantic function call and simplify

; A projector term must be a state component pattern in the state variable.
; A typical projector is (nth 3 (rd :locals s)), where s is the state variable
; in the model.

; Projectors can only be applied to semantic functions: functions of one state
; argument, namely the state variable.  Semantic functions are generally
; created by def-semantics.

; To carry out this first step, we substitute the body of the semantic function
; for the state variable in the projector and then use simplify-under-hyps to
; simplify that term under the state invariant.

; See apply-projector-to-term.

; ---
; (B.2) find every state component referenced outside the projected recursive
;       calls and collect the state component and its type; these are the
;       initially relevant components

; We will eventually make up a variable name for each relevant state component
; referenced outside the projected recursive calls.  Roughly speaking, these
; new variables will become the formals of the new function to be defined.
; However, to determine the final values of those components, we have to track
; their changes through each recursion and make sure that the new function
; makes those same changes to the corresponding formals.  The set of state
; components identified here can be thought of as controlling the termination
; tests and the base case.  But those components constitute just the initial
; set of relevant components; the set will be have to be closed under
; recursion.  That is, if R0 and R1, say, are used in the test and base, but
; the recursion sets R1 to R1 * R2, then we also have to make a formal for R2
; and track it.  That is done later.

; In addition, we want to allow the user to assert restrictions on the state
; components, possibly stronger restrictions than those imposed by the state
; invariant -- or restrictions that are intrinsic to the state accessors and so
; cannot be captured in the invariant.  (There is an Essay On Identifying State
; Components and their Types in the code that elaborates this vague idea.)  So
; as we scan the simplified projected semantic function body to collect the
; initially relevant state components we also collect their user-declared
; types.

; See find-all-state-components-and-types-outside.

; ---
; (B.3) replace all projected recursive calls of the semantic function by
;       unquoted naturals and build an alist mapping those naturals to the new
;       states inside those calls

; We copy term, replacing ``projected recursive calls'' of the semantic
; function by integers (not quoted evgs!) and build an alist pairing those
; integers with the next states found within the ``projected recursive calls.''
; The projected recursive calls are calls of the given semantic function symbol
; surrounded by the projector, e.g., (NTH '1 (RD :LOCALS (sem-fn s'))).

; For example, given the term

; (IF tst1
;     (IF tst2
;         (NTH '1 (RD :LOCALS (sem-fn s')))
;         (NTH '1 (RD :LOCALS (sem-fn s''))))
;     s)

; where the projector term is (NTH '1 (RD :LOCALS S)) and s, s' and s'' are
; various state expressions, we'd return:

; (mv '(IF tst1
;          (IF tst2
;              0
;              1)
;          s)
;     '((1 . s'') (0 . s')))

; Note that if the returned alist is nil there are NO calls of sem-fn term.
; This could happen in several ways but we suspect the two most common are
; because the code concerned is straight-line or because the code enters an
; already analyzed loop after some preamble.  By the way, it is possible for
; term (and hence the returned term') to be constant: e.g., the code enters an
; already-analyzed loop on known values and the simplifier just computes it
; out.

; See enumerated-projected-body.

; ---
; (B.4) for each site, determine the new value of each of the relevant state
;       components in the new state at that site; close the set of relevant
;       components by iteration

; Think of the state components that occur outside of the ``projected recursive
; calls'' of the semantic function as an initial set of relevant components.
; We have to determine how those components are changed in recursion.  So, for
; example, the ``outside'' components might be R0 and R1, but as the function
; recurs, R1 might become R1+R2.  That means that R2 is relevant to the final value
; of R1, even though R2 does not occur ``outside.''  So the computation done
; in this step is really in two phases.

; First, given a set of so-far-recognized as relevant state components, we
; collect their new values in each of the states occurring inside the
; enumerated projected recursive calls.  This is done by the function
; components-and-types-to-actual-expressions-by-call.  The determination of the
; new value is done by applying the relevant state component to the state and
; simplifying -- just another projection.  It might be possible to do it by the
; simpler mechanism of converting the state to a list of :SLOT expressions as
; by changed-virtual-formal-slots (from Terminatricks), but it is not done that
; way!  One advantage of doing it the slow way, by simplification, is that we
; thus take advantage of any previously proved projections -- something that we
; think is necessary.

; The second phase is to scan the resulting list of new values looking for new
; state components -- ones that now become recognized as relevant -- and
; iterating.  This is done by the function
; components-and-types-to-actual-expressions-by-call*.

; A minor aspect of the code that is not described above is that for each state
; component identified as relevant we also keep a term that restricts its
; ``type'' as specified by the user when the state component patterns were
; identified.  These types eventually become part of the governing hypotheses
; of the function we'll define.

; ---
; (B.5) introduce calls of the new function at each site, generalizing the
;       relevant state components and their occurrences in the actuals

; Having closed the set of relevant components, we next produce a new formal
; variable name for each component, turn each enumerated projected recursive
; call into a call of the about-to-be-defined new function on the relevant
; actuals, and then generalize away the state components in favor of their
; corresponding formal variable names.  The construction of the call of the new
; function symbol is done by the function make-fn-call-for-call-no.

; New variable names are generated by vformal-to-variable-name and there is an
; Essay on :var-names -- Two Ways for the User to Control the Generation of
; Variable Names.

; Note that at this time, the actuals to the new function are listed in some
; arbitrary order depending on the order in which they were discovered.  (We
; haven't actually paid attention to how they are ordered.)  We'll permute them
; into a sensible order before we submit the generated defun.

; Having created, for each of the enumerated projected recursive call sites, a
; call of the new function on the appropriate actuals expressed in terms of new
; formal variable names, we go back into the abstracted body (produced by step
; (B.3) above) and replace the unquoted evgs by the corresponding calls of the
; new function and generalize the state components outside of those call sites
; to their corresponding formals.  This is done by
; re-introduce-recursions-and-generalize.

; ---
; (B.6) determine the restrictions imposed by the invariant on the relevant state
;       components

; Naively, the definition of the new projection function will be protected by a
; top-level test in its body on (hyps s), where hyps is the state invariant.
; This is typically needed to make sure that whatever parts of the state
; invariant insured termination of the semantic function is available for
; termination of the new function.

; But this is wrong because the new function will not take s as a formal, it
; only takes the values of the relevant components of state, e.g., R0, R2, and
; R7.  Suppose that (nth 2 (rd :locals s)) is a relevant state component, which
; will be known as R2 when it is a formal parameter.  The question is, what
; does (hyps s) tell us about (nth 2 (rd :locals s))?  To find out, we
; ``invert'' the state component, creating a term, s', that assigns R2 to that
; component:

; (wr :locals (update-nth 2 R2 (rd :locals s)) s)

; and we then simplify (hyps s') under the assumption of (hyps s).  Presumably,
; all the hypotheses about parts of s not changed in s' will be simplified away
; and we'll be left with hypotheses about R2.  Those are the hypotheses we will
; put into the top-level test of the body of the new projector function.

; This description is misleading only in that we ``invert'' all the relevant
; state components in a single expression, s', e.g., assigning the new values
; R0, R2, and R7 to the corresponding components of s, and simplify (hyps s')
; under (hyps s), recovering all the hyps about the relevant components in one
; big simplification.

; See invariant-on-vformals.

; ---
; (B.7) rearrange all the definitions' formals and calls so that formals are
;       in alphabetical order

; For the user's sanity, we think it helps if the formals are listed in
; alphabetical order.  This is sensible since the user controls the naming of
; the formals.  For example, if registers are given the names R0, R1, R2, ...,
; and the new function, fn, only uses R0, R2, and R7, it is easier to remember
; that they're listed in ascending order than it is to remember some arbitrary
; order.  If we didn't do this, then the formals of fn might be (R7 R0 R2) and
; when you saw a call like (fn a b c) you'd have to remember that ordering to
; figure out that R0 has become expression b.  (In fact, in earlier versions of
; Codewalker we did not re-order and suffered exactly this problem.)

; So having created the tentative body of the new projection fn with the
; formals and actuals listed in some arbitrary (but internally consistent)
; order, we order the formals alphabetically, build a ``permuation map'' that
; tells us where to put each formal/actual to respect this order, and then
; apply that map to the tentative body.  For example, if the formals of
; fn were originally (R7 R0 R2) then the permutation map would be
; ((0 . 2) (1 . 0) (2 . 1)), and applying that map to the expression
; (fn a b c) would produce (fn b c a).

; See apply-permutation-map-to-term.

; This rather late rearrangement of the formals/actuals could probably be
; avoided had we thought about the issue earlier.  As it actually happened, we
; implemented all the steps above before this one, found the results a little
; hard to comprehend -- especially when a projection function has 7 arguments
; in some completely arbitrary order -- and decided to impose a sensible
; ordering after the fact.

; ---
; (B.8) determine whether there are other projected state components that
;       still occur in the body and if so cause an error

; It is still possible that the proposed definition of the projected function
; fails to be a definition because the state variable is still mentioned,
; despite not being a formal.  The easiest way for this to happen is if we
; tried to project, say (NTH 1 (RD :LOCALS S)) from SEM-0 before we had
; projected it from a subroutine of SEM-0, e.g., SEM-6.  The foregoing
; processing would produce a ``body'' for fn containing (NTH 1 (RD :LOCALS
; (SEM-6 S))).  If we see such a term while projecting SEM-0 we call it a
; ``projected other call,'' whereas if we're projecting SEM-6 it would be a
; ``projected recursive call.''

; So we scan the body looking for such ``sub-projections'' and if we find any
; we report sensible error messages telling the user to think of names for
; those projections and to do them first.  If the state variable still occurs,
; we cause a less helpful message.

; See all-projector-and-other-fnsymb.

; =============================================================================
; The Code for Codewalker

; Because we have so extensively documented Codewalker above, the only comments
; placed in the code below are (a) cross-references to the Implementation Guide
; such as ``See Guide (A.3),'' (b) document specific functions interfaces, or
; (c) futher elaborate the discussions above.  We assume you've read all the
; material above before attempting to really understand the code below.

(in-package "ACL2")

(include-book "terminatricks")

; This must be in :LOGIC mode, so we put it up here, before shifting to
; :PROGRAM mode.  Technically, it ought to be down by (defconst
; *snorkel-depth* ...) below.

(encapsulate ; See Guide (A.3).
 ((codewalker-tip
   (cnt path splitters s)
   t)
  (codewalker-wrapper-snorkeler
   (cnt rpath known-cutpoints splitters depth s)
   t))
 (local (defun codewalker-tip
          (cnt path splitters s)
          (declare (ignore cnt path splitters))
          s))
 (local (defun codewalker-wrapper-snorkeler
          (cnt rpath known-cutpoints splitters depth s)
          (declare (ignore cnt rpath known-cutpoints splitters depth))
          s))
 (defthm codewalker-tip-ignores-splitters
   (implies (syntaxp (not (equal splitters *nil*)))
            (equal (codewalker-tip cnt path splitters s)
                   (codewalker-tip cnt path nil       s))))
 (defthm codewalker-wrapper-snorkeler-ignores-splitters
   (implies (syntaxp (not (equal splitters *nil*)))
            (equal (codewalker-wrapper-snorkeler
                    cnt rpath known-cutpoints splitters depth s)
                   (codewalker-wrapper-snorkeler
                    cnt rpath known-cutpoints nil       depth s))))
 (in-theory (disable codewalker-tip-ignores-splitters
                     codewalker-wrapper-snorkeler-ignores-splitters)))

(program)

(set-state-ok t)

; The following two definitions from Matt Kaufmann are essentially versions of
; remove-guard-holders[-lst] from before July 2021, to preserve the existing
; behavior of codewalker.

(defun remove-guard-holders-legacy (term wrld)

; Warning: Keep in sync with ACL2 source function remove-guard-holders.

; Return a term equal to term, but slightly simplified, even perhaps inside
; quoted lambda objects.  See remove-guard-holders-weak for a version that does
; not take a world argument and does not simplify quoted lambda objects.

; See the warning in remove-guard-holders1.

  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (let ((lamp nil)) ; (remove-guard-holders-lamp)
    (cond (wrld (possibly-clean-up-dirty-lambda-objects
                 nil
                 (remove-guard-holders-weak term lamp)
                 wrld
                 lamp))
          (t (remove-guard-holders-weak term lamp)))))

(defun remove-guard-holders-lst-legacy (lst wrld)

; Warning: Keep in sync with ACL2 source function remove-guard-holders.

; Return a list of terms element-wise equal to lst, but slightly simplified,
; even perhaps inside quoted lambda objects.  See remove-guard-holders-weak-lst
; for a version that does not take a world argument and does not simplify
; quoted lambda objects.

  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (plist-worldp wrld))))
  (let ((lamp nil)) ; (remove-guard-holders-lamp)
    (cond (wrld (possibly-clean-up-dirty-lambda-objects-lst
                 nil
                 (remove-guard-holders-weak-lst lst lamp)
                 wrld
                 lamp))
          (t (remove-guard-holders-weak-lst lst lamp)))))

(defun update-codewalker-splitters (s0 s1 pc splitters)
  (cond ((or (not (quotep pc))
             (not (quotep splitters)))
         (er hard 'update-codewalker-splitters
             "The last two args of UPDATE-CODEWALKER-SPLITTERS are supposed ~
to be quoted evgs, but pc = ~x0; splitters = ~x1."
             pc splitters))
        ((> (count-ifs s1) (count-ifs s0))
         `((splitters1 . ,(kwote (cons (cadr pc) (cadr splitters))))))
        (t `((splitters1 . ,splitters)))))

; Here is the ``API'' for the machine model.  See Guide: Data Structures
; Driving Codewalker for an overview.  Individual fields are explained below.

; No thought has been given to frequency of access.  This was a balanced 16-tip
; binary tree until package-witness was added.

(defrec model-api
  ((((run . svar) . (stobjp . hyps))
    .
    ((step . get-pc) . (put-pc . updater-drivers)))
   .
   (((constructor-drivers . state-comps-and-types) package-witness . (callp . ret-pc))
    .
    ((returnp . clk+) . (name-print-base . var-names))))
  nil)

; The fields above are the translated versions of the fields documented in the
; Reference Guide for def-model-api.  See translate-model-api-alist for how we
; handle the translation of each field if it isn't obvious.  Recall that the
; :var-names field in this record is ALWAYS a function in this data structure:
; translation converts the ``list of tuples'' option into a lambda expression.

; Essay on the Passing of Untranslated Arguments

; Three macros (def-model-api, def-semantics, and def-projection) in this system
; take keyword arguments -- and the number of such arguments may grow in the
; future.  In all cases, the user-supplied arguments must be error-checked and
; translated before being used.  We adopt a uniform convention for how to do
; this.

; The keys of the macro are paired with the untranslated, user-supplied values,
; resulting in an alist.  We then pass the alist into some kind of translate
; function that either causes an error or assembles the final structure.  In
; the case of def-model-api, the final structure is a model-api defrec.  In the
; case of the def-semantics and def-projection commands, the final structure is an
; alist pairing the keys of the macro to the translated values.  These two
; alists are named dsem-alist and dpro-alist, respectively.

; The next block of code is devoted to translating API.
; See Guide: Data Structures Driving Codewalker.

(defun translate-fn-field (field ctx fn arity svar svar-pos state)
  (let* ((w (w state)))
    (cond
     ((and (symbolp fn)
           (equal (arity fn w) arity)
           (if (equal svar-pos -1)
               (not (member-eq svar (formals fn w)))
               (equal (len (member-eq svar (formals fn w)))
                      (- arity svar-pos))))
      (value fn))
     ((and (consp fn)
           (eq (car fn) 'lambda)
           (consp (cdr fn))
           (true-listp (cadr fn))
           (equal (len (cadr fn)) arity)
           (if (equal svar-pos -1)
               (not (member-eq svar (cadr fn)))
               (equal (len (member-eq svar (cadr fn)))
                      (- arity svar-pos))))

; We know fn is of the form (LAMBDA (x1...xn) . any) and that the svar, if any,
; is in the correct position.  We create and translate the pseudo-term ((LAMBDA
; (x1...xn) . any) x1...xn).  Then we return the ffn-symb of the result.  It
; could be that the created pseudo-term fails to be a term because the xi are
; illegal.  But if that is the case, they will not be distinct variables either
; and we'll report the illegal variables instead.

      (er-let* ((call (translate (cons fn (cadr fn))
                                 t t nil ctx
                                 w state)))
        (value (ffn-symb (remove-guard-holders-legacy call
; Matt K. mod 3/2019 for new argument of remove-guard-holders:
                                                      w)))))
     (t (er soft ctx
            "The ~x0 argument must be either an existing function symbol or ~
             a well-formed LAMBDA expression.  The arity of the function ~
             symbol or LAMBDA expression must be ~x1 and ~#2~[the formals ~
             must not include~/the ~n3 formal must be~] the state variable ~
             ~x4.  But ~x5 does not satisfy these requirements."
            field
            arity
            (if (equal svar-pos -1) 0 1)
            (list svar-pos)
            svar
            fn)))))

; Below we define some functions that translate true-lists of things.  But the
; functions themselves do not actually check the true-lisp condition because if
; you check it only at the end the error message just prints the non-nil final
; cdr, not the argument.  So we define the following function and use it
; in this idiom:
;  (er-progn (chk-true-listp x ctx "The foo field of a bar" state)
;            (translate-list-of-terms x state))
; so that either it reports a non-true-listp error about all of x or else it
; complains about the translation of some element, or else it returns the
; list of translated values.

(defun chk-true-listp (x ctx msg state)
  (cond
   ((true-listp x) (value nil))
   (t (er soft ctx
          "~@0 is supposed to be a true-list, but the value supplied is not: ~x1."
          msg
          x))))

(defun translate-list-of-terms (terms state)
  (cond
   ((atom terms) (value nil))
   (t
    (er-let* ((term (translate (car terms) t t nil
                               'translate-list-of-terms
                               (w state) state))
              (rest (translate-list-of-terms (cdr terms) state)))
      (value (remove-guard-holders-lst-legacy (cons term rest)
; Matt K. mod 3/2019 for new argument of remove-guard-holders:
                                              (w state)))))))

(defun translate-list-of-terms-list (lst state)
  (cond
   ((atom lst) (value nil))
   (t (er-let* ((term-lst (translate-list-of-terms (car lst) state))
                (rest (translate-list-of-terms-list (cdr lst) state)))
        (value (cons term-lst rest))))))

(defun translate-list-of-term-term-doublets (doublets state)
  (cond
   ((atom doublets) (value nil))
   ((and (consp (car doublets))
         (consp (cdr (car doublets)))
         (null (cddr (car doublets))))
    (er-let* ((term1 (translate (car (car doublets)) t t nil
                                'translate-list-of-term-term-doublets
                                (w state) state))
              (term2 (translate (cadr (car doublets)) t t nil
                                'translate-list-of-term-term-doublets
                                (w state) state))
              (rest (translate-list-of-term-term-doublets (cdr doublets) state)))
; Matt K. mod 3/2019 by adding new world argument of remove-guard-holders:
      (value (cons (list (remove-guard-holders-legacy term1 (w state))
                         (remove-guard-holders-legacy term2 (w state)))
                   rest))))
   (t (er soft 'translate-list-of-term-term-doublets
          "This function takes a true list of doublets, each of the form ~
           (term1 term2), and translates each termi.  The element ~x0 of your ~
           list is not of this form."
          (car doublets)))))

(mutual-recursion

(defun untranslate-updater-driver-term (term)
; We replace every ':value and ':base by :value and :base, respectively.
  (cond
   ((variablep term) term)
   ((fquotep term)
    (cond
     ((eq (cadr term) :value) (cadr term))
     ((eq (cadr term) :base) (cadr term))
     (t term)))
   (t (cons (ffn-symb term)
            (untranslate-updater-driver-term-lst (fargs term))))))

(defun untranslate-updater-driver-term-lst (lst)
  (cond
   ((endp lst) nil)
   (t (cons (untranslate-updater-driver-term (car lst))
            (untranslate-updater-driver-term-lst (cdr lst)))))))

(mutual-recursion

(defun how-many-occurrences (term1 term2)
; Count how many times term1 occurs in term2.
  (cond
   ((equal term1 term2) 1)
   ((variablep term2) 0)
   ((fquotep term2) 0)
   (t (how-many-occurrences-lst term1 (fargs term2)))))

(defun how-many-occurrences-lst (term1 lst)
  (cond
   ((endp lst) 0)
   (t (+ (how-many-occurrences term1 (car lst))
         (how-many-occurrences-lst term1 (cdr lst)))))))

(mutual-recursion

(defun term-uses-lambdap (term)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambdap (ffn-symb term)) t)
        (t (term-uses-lambdap-lst (fargs term)))))

(defun term-uses-lambdap-lst (lst)
  (cond
   ((endp lst) nil)
   (t (or (term-uses-lambdap (car lst))
          (term-uses-lambdap-lst (cdr lst)))))))

(defun translate-updater-drivers1 (doublets state)

; Each element of doublets is (term1 term2) where both are translated terms.
; We check that term1 satisfies the syntactic rules of an updater term and
; term2 those of an accessor term, as per the comment in
; translate-updater-drivers.  If so, we translate each to their special forms,
; by mapping ':value and ':base to :value and :base.

  (cond
   ((atom doublets) (value nil))
   (t (let* ((updater (car (car doublets)))
             (accessor (cadr (car doublets)))
             (xupdater (untranslate-updater-driver-term updater))
             (xaccessor (untranslate-updater-driver-term accessor)))

; Warning: xupdater and xaccessor are not terms!  They may contain unquoted
; :VALUE and :BASE symbols.  We nevertheless explore them like terms when we
; can afford the mistaking of :VALUE and :BASE for variable symbols.

        (cond
         ((not (equal (how-many-occurrences :value xupdater) 1))
          (er soft 'translate-updater-drivers
              "The updater term of an updater driver doublet must contain ~
               exactly one occurrence of :VALUE and this term, ~x0, contains ~
               ~x1."
              xupdater
              (how-many-occurrences :value xupdater)))
         ((not (equal (how-many-occurrences :base xupdater) 1))
          (er soft 'translate-updater-drivers
              "The updater term of an updater driver doublet must contain ~
               exactly one occurrence of :BASE and this term, ~x0, contains ~
               ~x1."
              xupdater
              (how-many-occurrences :base xupdater)))
         ((term-uses-lambdap xupdater)
          (er soft 'translate-updater-drivers
              "The updater term of an updater driver must not use any LAMBDA ~
               expressions because it may confuse our hack for insuring that ~
               the term uses :VALUE and :BASE the correct number of times.  ~
               This term contains a LAMBDA expression, ~x0."
              xupdater))
         ((not (equal (how-many-occurrences :value xaccessor) 0))
          (er soft 'translate-updater-drivers
              "The accessor term of an updater driver doublet must not ~
               contain :VALUE and this term, ~x0, does."
              xaccessor))
         ((not (equal (how-many-occurrences :base xaccessor) 1))
          (er soft 'translate-updater-drivers
              "The accessor term of an updater driver doublet must contain ~
               exactly one occurrence of :BASE and this term, ~x0, contains ~
               ~x1."
              xaccessor
              (how-many-occurrences :base xaccessor)))
         ((term-uses-lambdap xaccessor)
          (er soft 'translate-updater-drivers
              "The accessor term of an updater driver must not use any LAMBDA ~
               expressions because it may confuse our hack for insuring that ~
               the term uses :BASE the correct number of times.  This term ~
               contains a LAMBDA expression, ~x0."
              xaccessor))
         ((not (subsetp (all-vars accessor) (all-vars updater)))
          (er soft 'translate-updater-drivers
              "The variables of the updater term, ~x0, are not a superset of ~
               those of the accessor term, ~x1."
              xupdater
              xaccessor))
         (t (er-let* ((lst (translate-updater-drivers1 (cdr doublets) state)))
              (value (cons (list xupdater xaccessor)
                           lst)))))))))

(defun translate-updater-drivers (doublets state)

; The list of updater-drivers is supposed to be a list of doublets, each of the
; form (update-term accessor-term), where update-term should involve two
; special symbols, :value and :base and is otherwise a translatable term, and
; accessor-term is a term involving the special symbol :base and the same
; variables as the updater.  We translate each doublet and then coerce the
; ':value and ':base terms to their special counterparts or cause an error.
; Each special symbol is to occur at most once.  We prohibit lambda expressions
; because that confuses the counting.  Note that we might have checked that the
; accessors actually extract the alleged :VALUE, but we don't.

  (er-let* ((doublets (er-progn
                       (chk-true-listp doublets
                                       'def-model-api
                                       "The :UPDATER-DRIVERS argument"
                                       state)
                       (translate-list-of-term-term-doublets doublets state))))
    (translate-updater-drivers1 doublets state)))

; We now almost repeat the development of translate-updater-drivers1, above,
; except for constructor.  We think near duplication allows us to produce
; better error messages with less complication than we could with a generalized
; translation process capable of handling both.

(defun translate-constructor-drivers1-accessors
  (xconstructor vars accessors state)

; We untranslate and check each accessor against the rules laid out in
; translate-constructor-drivers.  Here xconstructor is the untranslated
; constructor term for each of the accessors and vars is the set of vars of
; xconstructor.

  (cond
   ((atom accessors) (value nil))
   (t (let* ((accessor (car accessors))
             (xaccessor (untranslate-updater-driver-term accessor)))

; Warning: xconstructor and xaccessor are not terms!  They may contain unquoted
; :VALUE and :BASE symbols.  And note that we untranslate ':VALUE to :VALUE in
; each accessor even though the special symbol is not supposed to appear.  We
; will give it special meaning simply because we suspect the user might since
; it is given special meaning in updater doublets.  Despite these violations of
; of the notion of well-formed terms, we nevertheless explore them as though
; they were when we can afford the mistaking of :VALUE and :BASE for variable
; symbols.

        (cond
         ((not (equal (how-many-occurrences :value xaccessor) 0))
          (er soft 'translate-updater-drivers
              "No accessor term of a constructor driver may contain ~
               :VALUE and this term, ~x0, does."
              xaccessor))
         ((not (equal (how-many-occurrences :base xaccessor) 1))
          (er soft 'translate-updater-drivers
              "Each accessor term of a constructor driver must contain ~
               exactly one occurrence of :BASE and this term, ~x0, contains ~
               ~x1."
              xaccessor
              (how-many-occurrences :base xaccessor)))
         ((term-uses-lambdap xaccessor)
          (er soft 'translate-updater-drivers
              "No accessor term of a constructor driver may use a LAMBDA ~
               expression because it may confuse our hack for insuring that ~
               the term uses :BASE the correct number of times.  This term ~
               contains a LAMBDA expression, ~x0."
              xaccessor))
         ((not (subsetp (all-vars accessor) vars))
          (er soft 'translate-updater-drivers
              "The variables of the constructor term, ~x0, are not a superset ~
               of those of one of its accessor terms, ~x1."
              xconstructor
              xaccessor))
         (t (er-let* ((lst (translate-constructor-drivers1-accessors
                            xconstructor vars
                            (cdr accessors)
                            state)))
              (value (cons xaccessor lst)))))))))

(defun translate-constructor-drivers1 (lst state)

; Each element of lst is (term0 term1 ... termn) where all elements are
; translated terms.  We check that term0 satisfies the syntactic rules of a
; constructor term and that every other termi those of an accessor term, as per
; the comment in translate-constructor-drivers.  If so, we translate each to
; their special forms, by mapping ':base to :base.

  (cond
   ((atom lst) (value nil))
   (t (let* ((constructor (car (car lst)))
             (accessors (cdr (car lst)))
             (xconstructor (untranslate-updater-driver-term constructor)))

; Warning: xconstructor is not a term!.  It may contain unquoted :VALUE and
; :BASE symbols.  And note that we untranslate ':VALUE to :VALUE here (and,
; eventually, in each accessor) even though the special symbol is not supposed
; to appear.  We will give it special meaning simply because we suspect the
; user might since it is given special meaning in updater doublets.  Despite
; these ``terms/lists of terms'' not being well-formed, we nevertheless explore
; them as though they were when we can afford the mistaking of :VALUE and :BASE
; for variable symbols.

        (cond
         ((not (equal (how-many-occurrences :value xconstructor) 0))
          (er soft 'translate-constructor-drivers
              "The constructor term of a constructor driver must not contain ~
               the special symbol :VALUE and this term does, ~x0."
              xconstructor))
         ((not (equal (how-many-occurrences :base xconstructor) 0))
          (er soft 'translate-constructor-drivers
              "The constructor term of a constructor driver must not contain ~
               the special symbol :BASE and this term does, ~x0."
              xconstructor))
         ((term-uses-lambdap xconstructor)
          (er soft 'translate-constructor-drivers
              "The constructor term of a constructor driver must not use any LAMBDA ~
               expressions because it may confuse our hack for insuring that ~
               the term uses :VALUE and :BASE the correct number of times.  ~
               This term contains a LAMBDA expression, ~x0."
              xconstructor))
         (t (er-let* ((xaccessors
                       (er-progn
                        (chk-true-listp accessors
                                        'DEF-MODEL-API
                                        "The list of constructor drivers"
                                        state)
                        (translate-constructor-drivers1-accessors
                         xconstructor
                         (all-vars constructor)
                         accessors state)))
                      (lst (translate-constructor-drivers1 (cdr lst) state)))
              (value (cons (cons xconstructor xaccessors)
                           lst)))))))))

(defun translate-constructor-drivers (lst state)

; The list of constructor-drivers is supposed to be a list of elements, each of
; the form (constructor-term accessor-term1 ... accessor-termn), where
; constructor-term should involve one special symbol, :base, and is otherwise a
; translatable term, and each accessor-termi is a term involving the special
; symbol :base and the same variables as the updater.  We translate each term
; and then coerce ':base to its special counterpart or cause an error.  :Base
; is to occur exactly once in each term; :VALUE should not appear at all.  We
; prohibit lambda expressions because that confuses the counting.  Note that we
; might have checked that the accessors actually extract the corresponding
; argument of the constructor-term, but we don't.

  (er-let* ((lst (er-progn
                  (chk-true-listp lst
                                  'DEF-MODEL-API
                                  "The :CONSTRUCTOR-DRIVERS argument"
                                  state)
                  (translate-list-of-terms-list lst state))))
    (translate-constructor-drivers1 lst state)))

; Essay on Generating Variable Names for Virtual Formals

; A var-name-rules is a list of triples, (pattern fmt-str term_0 ... term_k),
; where pattern is a term, fmt-str is a string appropriate for fmt and the
; term_i are terms in the variables of the pattern (excluding svar).  To
; generate a name for a virtual formal, term, we find the first pattern
; matching alist in term such that all variables in the pattern are bound to
; constants except, possibly, svar, which must be bound to svar.  Then we
; create fmt-alist by replacing the pattern variables in bound in the unifying
; alist with their evgs and then evaluating each term_i with respect to that
; alist, and then binding successive characters, #\0, ..., \#k with those
; values.  Then we create a string by printing fmt-str under fmt-alist.

; For example, if the pattern were (NTH i (NTH j svar)) then str might be
; "REG-~x0~x1" and term_0 is j and term_1 is i.  Suppose svar is FOO::SVAR.
; Thus, if the pattern is used to match (nth '3 (nth '7 FOO::SVAR)) then the
; variable name generated is FOO::REG-7-3.  (Note that this example
; intentionally swapped the order of the variables for illustrative purposes.)

; We generate the (alleged) variable name using the str and alist of the
; left-most pattern that matches term.  Thus, for example, if the first pattern
; in alist is (NTH i (NTH '1 svar)) and the second is (NTH i (NTH j svar)), we
; would generate the variable name for (NTH i (NTH '1 svar)) preferentially.

(defun member-instance (term i patterns alist0)

; This function finds first pattern in patterns that matches term and returns
; (mv flg alist i), where flg is t iff such a pattern exists, alist is the
; unifying subst, and i is the index in patterns of the winning pattern (i=0
; initially).  All results are nil when no pattern is found.

  (cond
   ((endp patterns) (mv nil nil nil))
   (t (mv-let
       (flg alist)
       (one-way-unify1 (car patterns)
                       term
                       alist0)
       (cond
        (flg
         (mv t alist i))
        (t (member-instance term (+ i 1) (cdr patterns) alist0)))))))

(defun translate-var-names (alist svar state-comps state)

; State-comps should be (strip-cars state-comps-and-types).  This function is
; only used if the specified setting for :var-names is supposed to be a list of
; (pattern fmt-string term_0 ...) tuples, not a function symbol or lambda
; expression.

  (cond
   ((atom alist)
    (value nil))
   ((and (true-listp (car alist))
         (<= 2 (len (car alist)))
         (<= (len (car alist)) 12)
         (stringp (cadr (car alist))))
    (cond
     ((eq (car (car alist)) :otherwise)
      (cond
       ((null (cddr (car alist)))
        (value (cons (list :otherwise (cadr (car alist)))
                     nil)))
       (t (er soft 'translate-var-names
              "The value supplied for :VAR-NAMES is ill-formed.  Each element ~
               should be of the form (pattern fmt-string term_0 ... term_n), ~
               and pattern is allowed to be :OTHERWISE only on the last ~
               element and only if n=0, i.e., no term_i are supplied.  Your ~
               element, ~x0, is thus ill-formed.  The :OTHERWISE pattern ~
               specifies the default fmt-string for any state component not ~
               matching one of the earlier ones.  We do not allow any term_i ~
               because they are evaluated with respect to the bindings of the ~
               non-:svar variables in the substitution produced by matching ~
               the pattern with the given state component to be generalized ~
               and that substitution will be empty, meaning each term_i must ~
               be a constant expression, in which case you might as well just ~
               specify the fmt-string you want."
              (car alist)))))
     (t
      (er-let* ((pattern (translate (car (car alist)) t t nil
                                    'translate-var-names
                                    (w state) state))
                (term-lst (translate-list-of-terms (cddr (car alist)) state))
                (rest (translate-var-names (cdr alist) svar state-comps state)))

        (mv-let
         (ans subst-alist i)
         (member-instance pattern
                          0
                          state-comps
                          (list (cons svar svar)))
         (declare (ignore subst-alist i))
         (cond
          ((null ans)
           (er soft 'translate-var-names
               "The value supplied for :VAR-NAMES is ill-formed.  Each ~
                element should be of the form (pattern fmt-string term_0 ... ~
                term_n), where pattern is an instance of some pattern in ~
                :STATE-COMPS-AND-TYPES with :SVAR, ~x0, bound to itself. But ~
                one of your :VAR-NAMES patterns, namely ~x1, is not such an ~
                instance."
               svar
               pattern))
          ((subsetp-eq (all-vars1-lst term-lst nil)
                       (remove1-eq svar (all-vars pattern)))
           (value (cons (list* pattern
                               (cadr (car alist)) ; fmt-string
                               term-lst)          ; term-lst for bindings
                        rest)))
          (t (er soft 'translate-var-names
                 "The value supplied for :VAR-NAMES is ill-formed.  Each ~
                  element should be of the form (pattern fmt-string term_0 ~
                  ... term_n).  But your term_i involve variable~#0~[~/s~] ~
                  ~&0 not occuring in the pattern, ~x1, that triggers ~
                  fmt-string ~x2."
                 (set-difference-eq (all-vars1-lst term-lst nil)
                                    (remove1-eq svar (all-vars pattern)))
                 pattern
                 (cadr (car alist))))))))))
   (t (er soft 'translate-var-names
          "The value supplied for :VAR-NAMES is ill-formed.  It must be the ~
           name of a function of one argument, a lambda expression of one ~
           argument, or a true-list of ``var name rules.''  Each var name ~
           rule must be of the form (pattern fmt-string term_0 term_1 ...), ~
           where fmt-string is a string and there are no more than 10 term_i ~
           terms.  You evidently tried to supply a list of var name rules, ~
           but your rule ~x0 is not of the correct form."
          (car alist)))))

; We will frequently form terms by consing a function name onto some arguments,
; as would happen if we wrote `(,fn ,arg1 ,arg2).  However, often, fn is a
; (translated) lambda expression, as when we specify the :run function to be
; (lambda (s n) (x86 s n)).  We don't want to form ((lambda (s n) (x86 s n))
; arg1 arg2) because it is unlikely to be a good rewrite or relieve hyps
; target.  So we beta-reduce terms by writing (make-fn-application fn args).

(defun make-fn-application (fn args)

; Fn is a function symbol of arity n or a translated lambda expression with n
; formals.  Args is a list of n translated terms.  We form the term (fn
; . args), but beta-reduce it at the top-level.

  (cond ((flambdap fn)
         (subcor-var (lambda-formals fn)
                     args
                     (lambda-body fn)))
        (t (cons fn args))))

; Given a virtual formal on some base and a new variable, new-var, to replace
; that virtual formal in some derived function, we need to compute the
; constraints imposed on new-var by the external invariant imposed on base.
; This is source (b) mentioned below in the Essay On Identifying State
; Components.  For example, take the M1 machine and imagine a good-statep
; condition on state s that requires all locals to be natural numbers.  Suppose
; (nth 7 (locals s)) is a virtual formal on base s and that we're going to
; replace that virtual formal by the variable new-var.  What may we assume
; about new-var given (good-statep s)?  Answer: (natp var).

; The way we figure this out is described in the Guide, (B.6), where we discuss
; ``inverting'' state accessors.

(defun find-first-member-instance (term con-drivers alist0)
  (cond
   ((endp con-drivers) (mv nil nil nil nil))
   (t (mv-let (flg alist i)
              (member-instance term 0 (cdr (car con-drivers)) alist0)
              (cond ((null flg)
                     (find-first-member-instance term (cdr con-drivers) alist0))
                    (t (mv t alist (car con-drivers) i)))))))

(defun invert-vformal1 (vformal base gup-drivers con-drivers)

; Vformal is a virtual formal in base and the last two arguments are our
; standard updater and constructor drivers tables.  We peel off one layer of
; the virtual formal and return (mv update-expr1 next-base).  If next-base is
; nil, there is no next base.  If update-expr1 is nil, vformal is unrecognized.

  (cond
   ((or (variablep vformal)
        (fquotep vformal))
    (if (equal vformal base)
        (mv vformal nil)
        (mv nil nil)))
   (t (mv-let
       (flg alist ele)
       (find-first-instance vformal 'cadr gup-drivers)
; Note:  find-first-instance is different from find-first-member-instance!
       (cond
        (flg
         (mv (sublis-var (cons '(:value . :value) alist) (car ele))
             (cdr (assoc-eq :base alist))))
        (t (mv-let
            (flg alist ele i)
            (find-first-member-instance vformal con-drivers nil)
            (cond
             (flg
              (mv (update-nth (+ i 1)
                              :value
                              (fcons-term (ffn-symb (car ele))
                                          (sublis-var-lst alist
                                                          (cdr ele))))
                  (cdr (assoc-eq :base alist))))
             (t (mv nil nil))))))))))

; Now we return the (body of the) generalized setter function for a virtual
; formal, vformal, on base, using var as the new value.

(defun invert-vformal (vformal var base gup-drivers con-drivers)

; Given a virtual formal on a base and the formal variable to replace it, var,
; we return the ``assignment expression'' that assigns var as the value of
; vformal in base.  For example, if vformal is (nth 7 (locals s)) and
; base is s and var is xxx, then we return:

; (make-state (pc s) (update-nth 7 xxx (locals s)) (stack s) (program s)).

; If we can't invert vformal, we return nil.

  (mv-let (updater next-vformal)
          (invert-vformal1 vformal base gup-drivers con-drivers)
          (cond
           ((null updater) nil)
           ((null next-vformal) var)
           (t (invert-vformal next-vformal
                              (subst-var var :value updater)
                              base gup-drivers con-drivers)))))

(defun invert-vformals (vformal-replacement-pairs
                        base gup-drivers con-drivers assignments uninvertables)

; Now we invert a list of vformal-replacement-pairs containing (vformali
; . new-vari).  However, for error reporting reasons we divide our answer into
; two lists: (mv assignments uninvertables) where uninvertables is a list of
; those vformals that we were unable to invert.  In the case that uninvertables
; is nil, the assignments is a list pairing each new variable with an
; expression that sets the corresponding (but now unrecorded) virtual formal in
; base to that variable.

  (cond
   ((endp vformal-replacement-pairs)
    (mv assignments uninvertables))
   (t (let* ((vformal1 (car (car vformal-replacement-pairs)))
             (var1 (cdr (car vformal-replacement-pairs)))
             (body1 (invert-vformal vformal1 var1
                                    base gup-drivers con-drivers)))
        (invert-vformals
         (cdr vformal-replacement-pairs)
         base gup-drivers con-drivers
         (if body1 (cons (cons var1 body1) assignments) assignments)
         (if body1 uninvertables (cons vformal1 uninvertables)))))))

; Because we've just exhibited what an ``assignment'' is, we go ahead and
; define how to compose a series of assignments.  This concept is not necessary
; for the translation check and is used later when we try to figure out the
; restrictions imposed by the invariant on individual vformals.

(defun compose-vformal-assignments (assignments base ans)

; Assuming that we were able to invert every virtual formal into an expression
; that assigned a given new variable to that slot, we compose the assignments
; into a single expression in the base and the new variables.  This is the
; ``generalization of the base state wrt the vformals.''

; Assignments is a list of pairs, (vari . bodyi).  Think of bodyi as a function
; that assigns the value vari to some virtual formal slot.  Call that function
; set-fni.  Then we can think of assignments as: ((var1 . set-fn1) (var2
; . set-fn2) ... (vark . set-fnk)).  We return the composed expression:
; (set-fn1 var1 (set-fn2 var2 ... (set-fnk vark base))).

; Ans should be nil initially and that is used as a flag to treat the first
; assignment specially -- it doesn't need a lambda wrapper.

; Note: In computing each composition we allow for the possibility that bodyi
; contains variables other than base and vari.  It is unclear whether this
; possibility ever arises!  It certainly doesn't if the only variable used in a
; virtual formal is the base.  However, if (nth i (locals s)) were somehow
; being treated as a virtual formal, then i would be a variable symbol in the
; body.

  (cond ((endp assignments)
         (if (null ans) base ans))
        ((null ans)
         (compose-vformal-assignments (cdr assignments) base
                                      (cdr (car assignments))))
        (t (let* ((var1 (car (car assignments)))
                  (body1 (cdr (car assignments)))
                  (other-vars (set-difference-eq (all-vars body1) (list base var1)))
                  (set-fn `(lambda (,var1 ,base ,@other-vars) ,body1))
                  (ans1 `(,set-fn ,var1 ,ans ,@other-vars)))
             (compose-vformal-assignments (cdr assignments) base ans1)))))

(defun translate-model-api-alist (alist state)

; Alist is an alist in which each key is the keyword name of a field of a
; proposed model-api and each key is bound in a pair to an untranslated value.
; We translate each value appropriately and return a translated model-api
; record.  (In an earlier version we packaged the untranslated bindings into a
; model-api record instead of an alist, and then we translated the record.  But
; we felt this was a violation (albeit a benign one) of the supposed invariant
; that model-api records contain translated values so we abandoned it.)

  (er-let*
    ((svar
      (cond
       ((eq (legal-variable-or-constant-namep
             (cdr (assoc-eq :svar alist)))
            'variable)
        (value (cdr (assoc-eq :svar alist))))
       (t (er soft 'translate-model-api-alist
              "The :SVAR value of a machine description must be a legal ~
               variable symbol and ~x0 is not."
              (cdr (assoc-eq :svar alist))))))
     (run
      (translate-fn-field
       :run
       'def-model-api
       (cdr (assoc-eq :run alist))
       2 svar 0
       state))
     (stobjp
      (cond ((cdr (assoc-eq :stobjp alist))
             (if (stobjp svar t (w state))
                 (value t)
                 (er soft 'translate-model-api-alist
                     "When the :STOBJP flag is set in a machine description, ~
                      the state variable ~x0 ought to be the name of a ~
                      single-threaded objected but it is not!"
                     svar)))
            (t (value nil))))
     (hyps
      (er-progn
       (chk-true-listp (cdr (assoc-eq :hyps alist))
                       'def-model-api
                       "The :HYPS argument"
                       state)
       (translate-list-of-terms
        (cdr (assoc-eq :hyps alist))
        state)))
     (step
      (translate-fn-field
       :step
       'def-model-api
       (cdr (assoc-eq :step alist))
       1 svar 0
       state))
     (get-pc
      (translate-fn-field
       :get-pc
       'def-model-api
       (cdr (assoc-eq :get-pc alist))
       1 svar 0
       state))
     (put-pc
      (translate-fn-field
       :put-pc
       'def-model-api
       (cdr (assoc-eq :put-pc alist))
       2 svar 1
       state))
     (updater-drivers
      (er-progn
       (chk-true-listp (cdr (assoc-eq :updater-drivers alist))
                       'def-model-api
                       "The :UPDATER-DRIVERS argument"
                       state)
       (translate-updater-drivers (cdr (assoc-eq :updater-drivers alist))
                                  state)))
     (constructor-drivers
      (er-progn
       (chk-true-listp (cdr (assoc-eq :constructor-drivers alist))
                       'def-model-api
                       "The :CONSTRUCTOR-DRIVERS argument"
                       state)
       (translate-constructor-drivers (cdr (assoc-eq :constructor-drivers alist))
                                      state)))
     (state-comps-and-types
      (er-progn
       (chk-true-listp (cdr (assoc-eq :state-comps-and-types alist))
                       'def-model-api
                       "The :STATE-COMPS-AND-TYPES argument"
                       state)
       (translate-list-of-term-term-doublets
        (cdr (assoc-eq :state-comps-and-types alist))
        state)))
     (var-names
      (let ((x (cdr (assoc-eq :var-names alist))))
        (cond
         ((or (and (symbolp x) (not (eq x nil)))
              (and (consp x)
                   (eq (car x) 'LAMBDA)))
          (translate-fn-field
           :var-names
           'def-mode-api
           x
           1 svar -1
           state))
         (t ; we treat the supplied value as an alist of vnrules
          (er-let* ((vnrules
                     (er-progn
                      (chk-true-listp x
                                      'def-model-api
                                      "The :VAR-NAMES argument"
                                      state)
                      (translate-var-names x svar
                                           (strip-cars state-comps-and-types)
                                           state))))
            (value
             `(lambda (term)
                (trigger-var-name-rule term
                                       ',svar
                                       ',vnrules))))))))
     (package-witness
      (value
       (cond
        ((null (cdr (assoc-eq :package-witness alist))) svar)
        ((symbolp (cdr (assoc-eq :package-witness alist)))
         (cdr (assoc-eq :package-witness alist)))
        (t svar))))
     (callp
      (cond ((or (eq (cdr (assoc-eq :callp alist))
                     t)
                 (eq (cdr (assoc-eq :callp alist))
                     nil))
             (value `(lambda (,svar) 'nil)))
            (t
             (translate-fn-field
              :callp
              'def-model-api
              (cdr (assoc-eq :callp alist))
              1 svar 0
              state))))
     (ret-pc
      (cond ((or (eq (cdr (assoc-eq :ret-pc alist))
                     t)
                 (eq (cdr (assoc-eq :ret-pc alist))
                     nil))
             (value `(lambda (,svar)
                       (binary-+
                        '1
                        ,(make-fn-application get-pc (list svar))))))

            (t
             (translate-fn-field
              :ret-pc
              'def-model-api
              (cdr (assoc-eq :ret-pc alist))
              1 svar 0
              state))))
     (returnp
      (cond ((or (eq (cdr (assoc-eq :returnp alist))
                     t)
                 (eq (cdr (assoc-eq :returnp alist))
                     nil))
             (value `(lambda (,svar) 'nil)))
            (t
             (translate-fn-field
              :returnp
              'def-model-api
              (cdr (assoc-eq :returnp alist))
              1 svar 0
              state))))
     (clk+
      (translate-fn-field
       :clk+
       'def-model-api
       (cdr (assoc-eq :clk+ alist))
       2 svar -1
       state)))
    (let ((name-print-base
           (or (cdr (assoc-eq :name-print-base alist))
               10)))
      (cond
       ((not (member-equal name-print-base '(2 8 10 16)))
        (er soft 'def-model-api
            "The only :NAME-PRINT-BASE values supported are 2, 8, 10, and 16. ~
              ~x0 is illegal."
            name-print-base))
       (t
        (mv-let
         (assignments uninvertables)
         (invert-vformals
          (pairlis-x2 (strip-cars state-comps-and-types) ; just the components
                      (genvar 'project-fn-to-fn "NEW-" 0 (list svar)))
          svar
          updater-drivers
          constructor-drivers
          nil nil)
         (declare (ignore assignments))

; Note:  We are ignoring the assignments because we are just doing error
; checking here.  We could perhaps improve efficiency marginally by storing
; the assignmetns as part of the ``translation'' of the state-comps-and-types
; but that (a) complicates the story and (b) probably doesn't help much because
; we don't think inversion is all that expensive.

         (cond
          (uninvertables
           (er soft 'def-model-api
               "Every state component must be invertable.  The following were ~
                not:  ~x0.  This probably means you need to inspect the
                :UPDATER-DRIVER and/or :CONSTRUCTOR-DRIVERS fields of the API."
               uninvertables))
          (t
           (value
            (make model-api
                  :run run
                  :svar svar
                  :stobjp stobjp
                  :hyps (remove-guard-holders-lst-legacy hyps
; Matt K. mod 3/2019 for new argument of remove-guard-holders:
                                                         (w state))
                  :step step
                  :get-pc get-pc
                  :put-pc put-pc
                  :updater-drivers updater-drivers
                  :constructor-drivers constructor-drivers
                  :state-comps-and-types state-comps-and-types
                  :callp callp
                  :ret-pc ret-pc
                  :returnp returnp
                  :clk+ clk+
                  :name-print-base name-print-base
                  :var-names  var-names
                  :package-witness package-witness))))))))))

(defmacro def-model-api (&key run svar stobjp hyps step
                              get-pc put-pc
                              updater-drivers constructor-drivers state-comps-and-types
                              callp ret-pc returnp
                              clk+ name-print-base
                              var-names package-witness)
  `(make-event
    (er-let* ((api
               (translate-model-api-alist
                '((:run . ,run)
                  (:svar . ,svar)
                  (:stobjp . ,stobjp)
                  (:hyps . ,hyps)
                  (:step . ,step)
                  (:get-pc . ,get-pc)
                  (:put-pc . ,put-pc)
                  (:updater-drivers . ,updater-drivers)
                  (:constructor-drivers . ,constructor-drivers)
                  (:state-comps-and-types . ,state-comps-and-types)
                  (:callp . ,callp)
                  (:ret-pc . ,ret-pc)
                  (:returnp . ,returnp)
                  (:clk+ . ,clk+)
                  (:name-print-base . ,name-print-base)
                  (:var-names . ,var-names)
                  (:package-witness . ,package-witness))
                state)))
      (value
       `(progn
          (table model-api
                 :record
                 (quote ,api))
          (table generalized-updater-drivers
                 :list
                 (quote ,(access model-api api :updater-drivers)))
          (table constructor-drivers
                 :list
                 (quote ,(access model-api api :constructor-drivers))))))))

; Codewalker-tip and extracting pcs from state terms

; A codewalker-tip expression has the form:
; (CODEWALKER-TIP cnt path splitters s)
;                 1   2    3         4

; Note: We limit the length of the paths we can explore to the value below.
; Furthermore, there is no current provision for handling coverage of the graph
; when the max path length is reached.  That is, the path trees we compute may
; not actually go from cutpoint to cutpoint but only from cutpoint to some
; random place max steps away -- we don't detect it unless (as will probably
; happen) the proof of correctness fails.

(defconst *snorkel-depth* 300)  ; depth reaches 300 and then snorkels.

(defun extract-pcs-from-if-term (term knowns unknowns)

; Given a normalized IF-term that represents a pc, return (mv knowns unknowns)
; where knowns is a list of all the constants that term might return and
; unknowns is a list of all the other pc values encountered.

  (cond ((variablep term)
         (mv knowns
             (add-to-set term unknowns)))
        ((fquotep term)
         (mv (add-to-set (cadr term) knowns)
             unknowns))
        ((eq (ffn-symb term) 'IF)
         (mv-let (knowns unknowns)
                 (extract-pcs-from-if-term (fargn term 2) knowns unknowns)
                 (extract-pcs-from-if-term (fargn term 3) knowns unknowns)))
        (t (mv knowns
               (add-to-set term unknowns)))))

; See Guide.
; (A.1) compute a conservative (over-estimate of the) control flow graph of the
;       program

(defun state-poised-at-pc (pc api)
  `(,(access model-api api :put-pc)
    (quote ,pc)
    ,(access model-api api :svar)))

(defun next-pcs (pc api state)

; Given a pc and a machine description we step the machine once from that pc
; and extract the new pcs.  We return (mv knowns unknowns).  The knowns is a
; list of all constants that could be the new pc and unknowns is a list of all
; the other (probably unresolved symbolic) pc values.

  (mv-let (knowns unknowns)
          (extract-pcs-from-if-term
           (simplify-under-hyps (access model-api api :hyps)
                                `(,(access model-api api :get-pc)
                                  (,(access model-api api :step)
                                   ,(state-poised-at-pc pc api)))
                                state)
           nil nil)
          (prog2$
           (cw "pc ~x0 ==> ~x1 [unkn: ~x2]~%"
               pc knowns unknowns)
           (mv knowns unknowns))))

(defun focus-regionp-approvesp (ctx pred pc state)
  (mv-let (erp val)
          (cond
           ((symbolp pred)
; Matt K. mod, 10/2017: Replaced call of ev-fncall-w, now untouchable, by call
; of magic-ev-fncall.
            (magic-ev-fncall pred (list pc) state nil nil))
           (t
; If we were allowed to call ev-w we would use:
;             (ev-w (list pred (kwote pc))
;                   nil (w state) nil nil nil nil nil)
; But ev-w is on untouchables.  Instead, I'll use simplify-under-hyps
            (let ((val
                   (simplify-under-hyps nil
                                        (list pred (kwote pc))
                                        state)))
              (cond
               ((quotep val) (mv nil (cadr val)))
               (t (mv t nil))))
            ))
          (cond
           (erp
            (er hard ctx
                "The focus-region predicate ~X01 caused an error (or at least ~
                 failed to fully evaluate to a constant) when applied to the ~
                 pc ~x2."
                pred nil pc))
           (t val))))

(mutual-recursion

(defun make-backward-link-graph
  (pc last-pc blink-graph unknowns-alist dsem-alist api state)

; We construct the backward graph first: An entry in blink-graph, (pc
; . pc-lst), means that pc is ``reachable'' in one step from the pcs in pc-lst.
; We reached pc from last-pc and we assume last-pc is within the focus region.

; We explore the ``reachable'' pcs starting from the initial statep described
; by api.  We quote reachable because we do absolutely no contextual reasoning:
; it is as though every branch were possible.

; Think of pc and api together describing the state, s, which is the api initial
; state but poised at pc.  Imagine that control has been transferred to this s
; from a state with pc last-pc, which is some constant.  -1 should be
; used initially, denoting the intended (top level) entry into the code.
; Blink-Graph is a list of all the pcs visited so far and the pcs from which
; each was visited.  For example, blink-graph might be (except for order)

; ((0 -1) (1 0) (2 1) (3 2 5) (4 3) (5 4) (6 5 6)))

; which means we entered at 0 from the imaginary ``top'' and successively
; visited each pc except 3, which we reached two ways: once from 2 and once
; from 5, and 6, which we reached from 5 and also from 6.  Note that since 6
; transfers control to itself, one can think of the instruction at 6 as a
; (conditional) HALT.

; If the instruction at pc jumps to a non-constant place, we add a pc entry to
; the alist unknowns-alist, which pairs each such pc with the list of symbolic
; values the next pc may take on.  If unknowns-alist is non-nil, then the
; instructions at those pcs might jump ANYWHERE.  Thus, if unknowns-alist is
; non-nil, the rest of the graph is pretty useless.  However, the user might
; wish to inspect the instructions at those pcs to determine what is going on.

; If the instruction at pc jumps to a pc outside the focus region, we record
; that fact but we record the external pc as we would a HALT: it jumps to
; itself.

; Operationally, we store how we reached pc (i.e., from last-pc) and then
; explore forward from pc provided pc is within the focus region.  If pc is not
; within the focus region, we record it as we would a HALT>

; We quit exploring when we get no new entries in blink-graph.

  (let ((temp (assoc-equal pc blink-graph)))
    (cond
     (temp
      (mv (put-assoc-equal pc (append (cdr temp) (list last-pc)) blink-graph)
          unknowns-alist))
     (t
      (let* ((val
              (focus-regionp-approvesp
               'make-backward-link-graph
               (cdr (assoc-eq :focus-regionp dsem-alist))
               pc state))
             (blink-graph
              (put-assoc-equal pc
                               (if val
                                   (list last-pc)
                                   (list last-pc pc))
                               blink-graph)))
        (cond
         (val
          (mv-let (knowns unknowns)
                  (next-pcs pc api state)
                  (make-backward-link-graph-lst knowns pc blink-graph
                                                (if unknowns
                                                    (cons (cons pc unknowns)
                                                          unknowns-alist)
                                                    unknowns-alist)
                                                dsem-alist api state)))
         (t (mv blink-graph unknowns-alist))))))))

(defun make-backward-link-graph-lst
  (pcs last-pc blink-graph unknowns-alist dsem-alist api state)
  (cond
   ((endp pcs) (mv blink-graph unknowns-alist))
   (t (mv-let (blink-graph unknowns-alist)
              (make-backward-link-graph (car pcs) last-pc blink-graph
                                        unknowns-alist dsem-alist api state)
              (make-backward-link-graph-lst (cdr pcs) last-pc blink-graph
                                            unknowns-alist
                                            dsem-alist api state))))))

; Now we build the forward link graph by reversing the links.

(defun make-forward-link-graph1 (pc from-pcs flink-graph)
  (cond
   ((endp from-pcs) flink-graph)
   (t (make-forward-link-graph1
       pc
       (cdr from-pcs)
       (put-assoc-equal (car from-pcs)
                  (cons pc (cdr (assoc-equal (car from-pcs) flink-graph)))
                  flink-graph)))))

(defun make-forward-link-graph (blink-graph flink-graph)
; Given a backward link graph we reverse the links.
  (cond ((endp blink-graph) flink-graph)
        (t (make-forward-link-graph
            (cdr blink-graph)
            (make-forward-link-graph1 (car (car blink-graph))
                                      (cdr (car blink-graph))
                                      flink-graph)))))

(defun link-graphs (dsem-alist api state)

; Given a machine description we construct the forward link graph and the
; backward link graph.  We return (mv unknowns-alist flink-graph blink-graph).
; If unknowns-alist is non-nil, then the pcs listed as keys in it lead to
; unknown (symbolically given) destinations and we return nil link graph
; answers.

  (mv-let (blink-graph unknowns-alist)
          (make-backward-link-graph
           (cdr (assoc-eq :init-pc dsem-alist))
           -1 nil nil dsem-alist api
           state)
          (cond
           (unknowns-alist (mv unknowns-alist nil nil))
           (t (let ((flink-graph (make-forward-link-graph blink-graph nil)))
                (mv nil flink-graph blink-graph))))))

; See Guide.
; (A.2) identify loops and halts, the so-called ``cutpoints''

(defun some-element-not-lexorder (lst x)

; We return t if there is a y in lst such that y > x.

  (cond ((endp lst) nil)
        ((lexorder (car lst) x)
         (some-element-not-lexorder (cdr lst) x))
        (t t)))

(defun loop-pcs (blink-graph)
  (cond ((endp blink-graph) nil)
        ((member-equal (car (car blink-graph)) (cdr (car blink-graph)))
         (cond
          ((<= 3 (len (cdr (car blink-graph))))
           (cond ((some-element-not-lexorder (cdr (car blink-graph)) (car (car blink-graph)))
                  (cons (car (car blink-graph))
                        (loop-pcs (cdr blink-graph))))
                 (t (loop-pcs (cdr blink-graph)))))
          (t (loop-pcs (cdr blink-graph)))))
        ((<= 2 (len (cdr (car blink-graph))))
         (cond ((some-element-not-lexorder (cdr (car blink-graph)) (car (car blink-graph)))
                (cons (car (car blink-graph))
                      (loop-pcs (cdr blink-graph))))
               (t (loop-pcs (cdr blink-graph)))))
        (t (loop-pcs (cdr blink-graph)))))

; The concept of ``branching pcs'' is defined and executed but its result is
; never actually used.  We could delete this function and its call below, if we
; wanted.

(defun branching-pcs (flink-graph)
  (cond ((endp flink-graph) nil)
        ((<= 2 (len (cdr (car flink-graph))))
         (cons (car (car flink-graph))
               (branching-pcs (cdr flink-graph))))
        (t (branching-pcs (cdr flink-graph)))))

(defun halting-pcs (flink-graph)
  (cond ((endp flink-graph) nil)
        ((and (equal (car (car flink-graph))
                     (car (cdr (car flink-graph))))
              (null (cdr (cdr (car flink-graph)))))
         (cons (car (car flink-graph))
               (halting-pcs (cdr flink-graph))))
        (t (halting-pcs (cdr flink-graph)))))

(defun categorize-pcs (flink-graph blink-graph)

; We wrap the foregoing utilities up into one function because it is hard to
; remember which graph to pass to which utility!  We return (mv loop-pcs
; branching-pcs halting-pcs cutpoint-pcs).  The cutpoint pcs are those in the
; union of the loop pcs and the halting pcs.

  (let ((loop-pcs (loop-pcs blink-graph))
        (halting-pcs (halting-pcs flink-graph)))
    (mv loop-pcs
        (branching-pcs flink-graph)  ; ignored by caller
        halting-pcs
        (union-equal halting-pcs loop-pcs))))

; (A.3) simulate from cutpoint to cutpoint to get composed state transitions,
;       called path-tree expressions, along all paths

; Now that we know the cutpoints we can compute the semantics of each path
; between cutpoints.

(defun wrapper-events (api)
  (let ((s (access model-api api :svar))
        (get-pc (access model-api api :get-pc))
        (step (access model-api api :step)))
    `((with-output
;       :off :all
       :gag-mode nil
       (encapsulate
        nil
        (set-irrelevant-formals-ok t)
        (defun-nx CODEWALKER-WRAPPER
          (cnt rpath known-cutpoints splitters depth ,s)
          (declare
           (xargs :measure (nfix (- *snorkel-depth* (nfix depth)))))
          (if (or (not (natp depth))
                  (>= depth *snorkel-depth*))
              (CODEWALKER-WRAPPER-SNORKELER
               cnt rpath known-cutpoints splitters depth ,s)
              (if (or (member-equal ,(make-fn-application get-pc (list s))
                                    rpath)
                      (and rpath
                           (member-equal ,(make-fn-application get-pc (list s))
                                         known-cutpoints)))
                  (CODEWALKER-TIP
                   cnt
                   (revappend
                    (cons ,(make-fn-application get-pc (list s)) rpath)
                    nil)
                   splitters
                   ,s)
                  (CODEWALKER-WRAPPER
                   (+ 1 cnt)
                   (cons ,(make-fn-application get-pc (list s))
                         rpath)
                   known-cutpoints
                   splitters
                   (+ 1 depth)
                   (,step ,s)))))

; The function above won't open under ACL2's heuristics, so we force it to
; expand when either the pc is constant or the depth is exceeded.  We separate
; the three mutually exclusive cases into three rules, but the hyps -- except
; for the one involving the step function in the third rule -- are not
; expensive because everything involved should be constants.

        (defthm codewalker-wrapper-rule-1
          (implies (and (natp depth)
                        (>= depth *snorkel-depth*))
                   (equal (CODEWALKER-WRAPPER
                           cnt rpath known-cutpoints splitters depth ,s)
                          (CODEWALKER-WRAPPER-SNORKELER
                           cnt rpath known-cutpoints splitters depth ,s))))

        (defthm codewalker-wrapper-rule-2
          (implies (and (natp depth)
                        (< depth *snorkel-depth*)
                        (equal pc ,(make-fn-application get-pc (list s)))
                        (syntaxp (quotep pc))
; Pc, rpath, and known-cutpoints are all quoted evgs, so this should be evaluable.
                        (or (member-equal pc rpath)
                            (and rpath
                                 (member-equal pc known-cutpoints))))
                   (equal (CODEWALKER-WRAPPER
                           cnt rpath known-cutpoints splitters depth ,s)
                          (CODEWALKER-TIP
                           cnt
                           (revappend (cons pc rpath) nil)
                           splitters
                           ,s))))

        (local
         (defthm codewalker-wrapper-ignores-splitters
           (implies (syntaxp (not (equal splitters *nil*)))
                    (equal
                     (CODEWALKER-WRAPPER
                      cnt rpath known-cutpoints splitters depth ,s)
                     (CODEWALKER-WRAPPER
                      cnt rpath known-cutpoints nil       depth ,s)))
           :hints (("Goal"
                    :in-theory
                    (enable codewalker-tip-ignores-splitters
                            codewalker-wrapper-snorkeler-ignores-splitters)))))

        (defthm codewalker-wrapper-rule-3
          (implies (and (natp depth)
                        (< depth *snorkel-depth*)
                        (equal pc ,(make-fn-application get-pc (list s)))
                        (syntaxp (quotep pc))
; Pc, rpath, and known-cutpoints are all quoted evgs, so this should be evaluable.
                        (not (or (member-equal pc rpath)
                                 (and rpath
                                      (member-equal pc known-cutpoints))))
; We need to know the next state to compute the new value of splitters.
                        (equal s1 (,step ,s))
; We bind splitters1 to either '(pc . splitters) or splitters, depending on whether
; the next state has more IFs than the current one.
                        (bind-free (update-codewalker-splitters ,s s1 pc splitters)
                                   (splitters1))
                        )
                   (equal (CODEWALKER-WRAPPER
                           cnt rpath known-cutpoints splitters depth ,s)
                          (CODEWALKER-WRAPPER
                           (+ 1 cnt)
                           (cons pc rpath)
                           known-cutpoints
                           splitters1 ; new value of splitters
                           (+ 1 depth)
                           s1)))) ; next state

        (in-theory (disable codewalker-wrapper))

        ))
      )))

; The functions below should only be executed after the wrapper-events have
; been executed.

(defun collect-terminal-cutpoints (path-tree halting-pcs)

; A ``path-tree'' for pc0 is a normalized IF-expression that contains
; CODEWALKER-TIP expressions at every non-trivial non-tested tip.  The
; path-tree for pc0 is equal to the result of running the state (described by
; some implicit api) from pc0 to any known cutpoint.  Each codewalker-tip is an
; expression of the form:

; (CODEWALKER-TIP 'k '(pc0 pc1 pc2 ... pck) splitters s')

; where k is the number of steps to go from pc0 to another cutpoint, pck, the
; listed pci are the pcs visited along the path, splitters is the list of pcs
; that introduced additional IFs after rewriting, and s' is state reached along
; that path (and which thus has pc pck).

; This function collects all the terminal pcs listed in the path-tree, except
; those that are halting pcs.

  (cond ((variablep path-tree) nil)
        ((fquotep path-tree) nil)
        ((eq (ffn-symb path-tree) 'CODEWALKER-TIP)
         (let ((k (fargn path-tree 1))
               (path (fargn path-tree 2))
;              (splitters (fargn path-tree 3)) ; splitters is irrel here.
;              (s1 (fargn path-tree 4))        ; state is irrel here
               )
           (cond ((and (quotep k)
                       (natp (cadr k))
                       (quotep path)
                       (true-listp (cadr path))
                       (equal (+ 1 (cadr k))
                              (length (cadr path))))
                  (let ((pck (car (last (cadr path)))))
                    (cond ((member-equal pck halting-pcs)
                           nil)
                          (t (list pck)))))
                 (t
                  (er hard 'path-tree-tuple-from-cutpoint
                      "In every (CODEWALKER-TIP k path ...) term, k is ~
                       supposed to be a quoted natural indicating how many ~
                       steps were taken, path is supposed to be a quoted ~
                       true-list of the pcs visited along the path, and the ~
                       length of path is supposed to be one greater than k.  ~
                       These invariants are not met by ~X01."
                      path-tree
                      nil)))))
        ((EQ (ffn-symb path-tree) 'IF)
         (union-equal (collect-terminal-cutpoints (fargn path-tree 2) halting-pcs)
                      (collect-terminal-cutpoints (fargn path-tree 3) halting-pcs)))
        ((eq (ffn-symb path-tree) 'CODEWALKER-WRAPPER)
         (er hard 'path-tree-tuple-from-cutpoint
             "Every tip in a path-tree is supposed to be a CODEWALKER-TIP ~
              expression and we've just encountered the CODEWALKER-WRAPPER ~
              term shown below.  Look at the last argument, <s>, of that ~
              term, which is supposed to simplify to some semi-explicit ~
              state.  We probably cannot determine the pc of <s>.  This is ~
              generally an indication that the rewriter has insufficient ~
              rules to simplify such a term.   You might submit the following ~
              challenge to ACL2 and see if you can prove rules to rewrite the ~
              left-hand side of the conclusion to a quoted constant.~%(thm ~
              (implies <hyps> (equal (<get-pc> <s>) xxx)))~%where <hyps> and ~
              <get-pc> are the :hyps and :get-pc of your model's API. This is ~
              clearly not a theorem -- note the arbitrary xxx -- but you need ~
              the left-hand side of the conclusion to simplify to a quoted ~
              constant! ~%~%Unexpected tip in path-tree, ~X01."
             path-tree
             nil))
        (t (er hard 'path-tree-tuple-from-cutpoint
               "Every tip in a path-tree is supposed to be a CODEWALKER-TIP ~
                expression and we've just encountered an unexpected tip: ~X01."
               path-tree
               nil))))

(defun max-snorkel-data (tuple1 tuple2)
; See the next function.
  (cond
   ((null tuple1) tuple2)
   ((null tuple2) tuple1)
   (t (let ((step-cnt1 (car tuple1))
            (cont-cnt1 (cadr tuple1))
            (nest-depth1 (caddr tuple1))
            (splitters1  (cadddr tuple1))
            (step-cnt2 (car tuple2))
            (cont-cnt2 (cadr tuple2))
            (nest-depth2 (caddr tuple2))
            (splitters2  (cadddr tuple2)))
        (cond
         ((not (equal step-cnt1 step-cnt2))
          (er hard 'snorkel-data
              "We thought the step counts of all CODEWALKER-WRAPPER-SNORKELER ~
               terms would be equal but they are not!  We see these two ~
               tuples:~%tuple1 = ~x0~%~tuple2 = ~x1~%"
              tuple1 tuple2))
         (t (list step-cnt1
                  (+ cont-cnt1 cont-cnt2)
                  (max nest-depth1 nest-depth2)
                  (union-equal splitters1 splitters2))))))))

(mutual-recursion

(defun snorkel-data (term depth)

; This function returns non-nil iff term contains CODEWALKER-WRAPPER-SNORKELER
; subterms.

; When non-nil, the answer is a tuple:
; (step-cnt continuation-cnt nesting-depth splitters),
; where

; * step-cnt is the number of steps taken so far.  It is always a multiple of
;   *snorkel-depth*;

; * continuation-cnt is the number of continuations, i.e.,
; * CODEWALKER-WRAPPER-SNORKELER terms, in the partial path tree

; * nesting-depth is the function-nesting depth of the deepest continuation.

; * splitters is the list of pcs causing splits

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((eq (ffn-symb term) 'IF)
         (max-snorkel-data
          (snorkel-data (fargn term 2) (+ 1 depth))
          (snorkel-data (fargn term 3) (+ 1 depth))))
        ((eq (ffn-symb term) 'CODEWALKER-WRAPPER-SNORKELER)
         (list (cadr (fargn term 1)) ; step cnt evg
               1                     ; continuation cnt
               depth                 ; nesting depth
               (cadr (fargn term 4)) ; splitters
               ))
        (t (snorkel-data-lst (fargs term) (+ 1 depth)))))

(defun snorkel-data-lst (terms depth)
  (cond ((endp terms) nil)
        (t (max-snorkel-data
            (snorkel-data (car terms) depth)
            (snorkel-data-lst (cdr terms) depth))))))

(mutual-recursion
(defun abstract-snorkeled-path-tree (term)
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((equal (ffn-symb term) 'if)
    (cons-term* 'if
                (fargn term 1)
                (abstract-snorkeled-path-tree (fargn term 2))
                (abstract-snorkeled-path-tree (fargn term 3))))
   ((equal (ffn-symb term) 'codewalker-tip)
    :TIP)
   ((equal (ffn-symb term) 'codewalker-wrapper-snorkeler)
     (list :CONTINUATION-FROM-PC (car (cadr (fargn term 2)))))
   (t (cons-term (ffn-symb term)
                 (abstract-snorkeled-path-tree-lst (fargs term))))))
(defun abstract-snorkeled-path-tree-lst (terms)
  (cond ((endp terms) nil)
        (t (cons (abstract-snorkeled-path-tree (car terms))
                 (abstract-snorkeled-path-tree-lst (cdr terms)))))))

(mutual-recursion

(defun replace-codewalker-wrapper-snorkelers (term)

; In preparation for diving in again, we copy term and replace all the
; CODEWALKER-WRAPPER-SNORKLER terms with fresh CODEWALKER-WRAPPER terms (with
; depth reset to 0).

  (cond ((variablep term) term)
        ((fquotep term) term)
        ((eq (ffn-symb term) 'IF)
         (cons-term* 'IF
                     (fargn term 1)
                     (replace-codewalker-wrapper-snorkelers (fargn term 2))
                     (replace-codewalker-wrapper-snorkelers (fargn term 3))))
        ((eq (ffn-symb term) 'CODEWALKER-WRAPPER-SNORKELER)
         (cons-term* 'CODEWALKER-WRAPPER
                     (fargn term 1) ; step cnt for this path so far
                     (fargn term 2) ; rpath
                     (fargn term 3) ; known-cutpoints
                     (fargn term 4) ; splitters
                     *0*            ; depth in this round, reset to 0!
                     (fargn term 6) ; machine state so far
                     ))
        (t (cons-term (ffn-symb term)
                      (replace-codewalker-wrapper-snorkelers (fargs term))))))

(defun replace-codewalker-wrapper-snorkelers-lst (terms)
  (cond ((endp terms) nil)
        (t (cons (replace-codewalker-wrapper-snorkelers (car terms))
                 (replace-codewalker-wrapper-snorkelers-lst (cdr terms)))))))

(defun simplify-codewalker-wrapper-under-hyps-with-snorkeling
  (hyps concl pc0 last-data state)

; We may eventually wish to implement some sort of loop stopping check in which
; we compare the current data tuple with the last one.  But at the moment we
; don't because it is thought possible that successive data tuples might be
; identical even though simplifications occurred, e.g., because the simplifier
; for some reason worked on terms in the expression other than
; codewalker-wrapper terms.

  (declare (ignore last-data))

; We simplify concl under hyps and return the resulting term.  However, we
; implement snorkeling, but it is triggered only by
; CODEWALKER-WRAPPER-SNORKELER terms in the answer.  Thus, this is is NOT a
; general-purpose simplify-under-hyps with snorkeling!

  (let* ((path-tree (simplify-under-hyps hyps concl state))
         (data (snorkel-data path-tree 0)))

; If data is non-nil, then it is (max-depth . (cnt1 ... cntn)) and path-tree is
; only partially simplified.  In particular, the stack depth was in danger of
; being exceeded and so the simplifier quit and replaced the codewalker-wrapper
; term it was simplifying by a codewalker-wrapper-snorkeler term.  The stack
; near-overflow was almost certainly due to long paths through the code,
; requiring many steps, the simplification of each of which pushes a new frame.
; So if data is non-nil, we print a rather brief report and recur.  It is hoped
; the user will abort the computation if it seems not to be making progress!

    (cond
     ((null data)
      (value path-tree))
     (t
      (let ((step-cnt (car data))
            (continuation-cnt (cadr data))
            (nesting-depth (caddr data))
            (splitters (cadddr data)))
        (pprogn
         (fms "SNORKEL REPORT: pc: ~x0; steps ~x1~%number of continuations: = ~
               ~x2~%nesting depth: ~x3~%splitter pcs: ~X46~%partial-path-tree = ~
               ~%~X56~%"
              (list (cons #\0 pc0)
                    (cons #\1 step-cnt)
                    (cons #\2 continuation-cnt)
                    (cons #\3 nesting-depth)
                    (cons #\4 (merge-sort-lexorder splitters))
                    (cons #\5 (abstract-snorkeled-path-tree path-tree))
                    (cons #\6 nil))
              (standard-co state)
              state
              nil)
         (simplify-codewalker-wrapper-under-hyps-with-snorkeling
          hyps
          (replace-codewalker-wrapper-snorkelers path-tree)
          pc0 ; beginning of path
          data ; last-data
          state)))))))

(defun path-tree-tuple-from-cutpoint (cutpoint known-cutpoints halting-pcs api state)

; A path-tree-tuple is a 3-tuple (list start-pc (terminal-pc1 ...) path-tree),
; where path-tree is a path-tree from initial pc start-pc, the list of terminal
; pcs includes every non-halting terminal pc in the path-tree.

  (let* ((hyps (access model-api api :hyps))
         (s (access model-api api :svar))
         (put-pc (access model-api api :put-pc)))
    (er-let*
      ((path-tree
        (simplify-codewalker-wrapper-under-hyps-with-snorkeling
         hyps
         `(CODEWALKER-WRAPPER '0 'NIL ',known-cutpoints 'NIL '0
                              ,(make-fn-application put-pc
                                                    (list (kwote cutpoint) s)))
         cutpoint nil state)))  ; starting pc, last-data, ACL2 STATE
      (value
       (list cutpoint
             (collect-terminal-cutpoints path-tree halting-pcs) path-tree)))))

(defun path-tree-tuples-from-cutpoint-lst
  (cutpoint-lst known-cutpoints halting-pcs api state)

; This is a simple ``workhorse'' that iterates over cutpoints and collects a
; path tree tuple for each one.

  (cond
   ((endp cutpoint-lst) (value nil))
   (t (er-let* ((tuple (path-tree-tuple-from-cutpoint
                        (car cutpoint-lst)
                        known-cutpoints halting-pcs api state))
                (rest (path-tree-tuples-from-cutpoint-lst
                       (cdr cutpoint-lst)
                       known-cutpoints halting-pcs api state)))
        (value (cons tuple rest))))))

; See Guide:
; (A.4) compute reflexive-transitive closure of cutpoint-to-cutpoint relations
;       to construct a call graph, inducing an order the clock and semantic
;       functions

; However, the code for call-graph-ordering is not in this book.  It is in the
; Terminatricks book.

; (A.5) define clock and semantic functions from the path-tree expressions;
;       this would be straightforward except for two important additions:
;       (A.5.1) identifying certain trivial invariants that may be crucial to
;               termination, and
;       (A.5.2) removing mutual recursion.

; From each path-tree-tuple we generate a clock function defun, pairing the
; defun with its start-pc:

(defun pair-fns-with-level-nos (fns wrld)
  (cond ((endp fns) nil)
        (t (cons (cons (get-level-no (car fns) wrld)
                       (car fns))
                 (pair-fns-with-level-nos (cdr fns) wrld)))))

(defun fn-symb-with-max-level-no (fn wrld)
  (cond ((symbolp fn) fn)
        (t (cdr
            (car
             (merge-sort-car->
              (pair-fns-with-level-nos
               (all-fnnames (lambda-body fn)) wrld)))))))

(defun generate-def-semantics-name (str1 pc-lst str2 dsem-alist api)
; Note:  The :root-name in the api is always a string ending in #\-.
  (let ((root-name (cdr (assoc-eq :root-name dsem-alist)))
        (base (access model-api api :name-print-base)))
    (intern-in-package-of-symbol
     (mv-let (col str)
             (fmt1-to-string "~s1~sr~*p~s2"
                             (list (cons #\1 str1)
                                   (cons #\r root-name)
                                   (cons #\b
                                         (case base
                                           (2 "B")
                                           (8 "O")
                                           (16 "X")
                                           (otherwise "")))
                                   (cons #\p `("" "~sb~x*" "~sb~x*-" "~sb~x*-" ,pc-lst))
                                   (cons #\2 str2))
                             0
                             :fmt-control-alist
                             (list (cons 'print-base base)
                                   (cons 'current-package
                                         (access model-api api :package-witness))))
             (declare (ignore col))
             str)
     (access model-api api :package-witness))))

(defun fnsymbol-name-prefix (kind)

; Kind is either :CLOCK or :SEMANTIC and this function returns the prefix
; string we use when forming fnnames of that kind.  Warning: If you change the
; prefix strings used, be sure to to change get-kind-from-fnsymbol-name!

  (if (eq kind :CLOCK) "CLK-" "SEM-"))

(defun get-kind-from-fnsymbol-name (str)

; Str is the symbol name, i.e., a string, of either a :CLOCK or :SEMANTIC
; function.  We return the kind.  It is convenient that both CLK- and SEM- are
; four characters long!  We cause a hard error if str is not of one of the two
; forms.

  (let ((msg "This function is supposed to be applied to a string whose ~
              initial prefix is either \"CLK-\" or \"SEM-\" and ~x0 is ~
              neither!"))
    (cond ((and (stringp str)
                (<= 3 (length str)))
           (cond ((and (eql (char str 0) #\C)
                       (eql (char str 1) #\L)
                       (eql (char str 2) #\K)
                       (eql (char str 3) #\-))
                  :clock)
                 ((and (eql (char str 0) #\S)
                       (eql (char str 1) #\E)
                       (eql (char str 2) #\M)
                       (eql (char str 3) #\-))
                  :semantic)
                 (t (er hard 'get-kind-from-fnsymbol-name msg str))))
          (t (er hard 'get-kind-from-fnsymbol-name msg str)))))

(defun snorkel-clock-expr (fn k clk)

; Fn is the clk+ function from the API, k is a nat, and clk is either NIL or a
; clock expression term.  We form an untranslated clock expression term that
; represents k or (clk+ k clk), depending on clk, except k is snorkeled.

  (cond
   ((<= k *snorkel-depth*)
    (cond
     ((null clk) (kwote k))
     (t (make-fn-application fn (list (kwote k) clk)))))
   (t (make-fn-application
       fn
       (list (kwote *snorkel-depth*)
             (snorkel-clock-expr fn (- k *snorkel-depth*) clk))))))

(defun generate-clock-function-body (path-tree halting-pcs dsem-alist api)
  (cond ((variablep path-tree) 0)
        ((fquotep path-tree) 0)
        ((eq (ffn-symb path-tree) 'CODEWALKER-TIP)
; (CODEWALKER-TIP k path splitters s), k, path, and splitters quoted consts
         (let* ((k (cadr (fargn path-tree 1))) ; (fargn path-tree 1) is QUOTEd
                                               ; but k is the evg!
                (path (fargn path-tree 2))
;               (splitters (fargn path-three 3))
                (s1 (fargn path-tree 4))
                (pck (car (last (cadr path)))))
           (cond ((member-equal pck halting-pcs)
                  (snorkel-clock-expr (access model-api api :clk+)
                                      k
                                      nil))
                 ((and (>= k 1)
                       (equal (nth (- k 1) ; next to last element
                                   (cadr path))   ; of path
                              pck))
; Path terminated in a stutter, pc0 --> pc1 --> ... --> pck --> pck.
                  (snorkel-clock-expr (access model-api api :clk+)
                                      k
                                      nil))
                 (t (snorkel-clock-expr
                     (access model-api api :clk+)
                     k
                     (make-fn-application
                      (generate-def-semantics-name (fnsymbol-name-prefix :clock)
                                                   (list pck)
                                                   ""
                                                   dsem-alist api)
                      (list s1)))))))
        ((EQ (ffn-symb path-tree) 'IF)
         (cons-term* 'IF
                     (fargn path-tree 1)
                     (generate-clock-function-body (fargn path-tree 2)
                                                   halting-pcs
                                                   dsem-alist api)
                     (generate-clock-function-body (fargn path-tree 3)
                                                   halting-pcs
                                                   dsem-alist api)))
        (t (er hard 'generate-clock-function-body
               "Unexpected tip in path-tree, ~x0."
               path-tree))))

(defun generate-semantic-function-body (path-tree halting-pcs dsem-alist api)
  (cond ((variablep path-tree) (access model-api api :svar))
        ((fquotep path-tree) (access model-api api :svar))
        ((eq (ffn-symb path-tree) 'CODEWALKER-TIP)
; (CODEWALKER-TIP k path splitters s), k, path, and splitters quoted consts
         (let* ((k (fargn path-tree 1))
                (path (fargn path-tree 2))
;               (splitters (fargn path-three 3))
                (s1 (fargn path-tree 4))
                (pck (car (last (cadr path)))))
           (cond ((member-equal pck halting-pcs)
                  s1)
                 ((and (>= (cadr k) 1)
                       (equal (nth (- (cadr k) 1)
                                   (cadr path))
                              pck))
; Path terminated in a stutter, pc0 --> pc1 --> ... --> pck --> pck.
                  s1)
                 (t `(,(generate-def-semantics-name
                        (fnsymbol-name-prefix :semantic)
                        (list pck)
                        ""
                        dsem-alist api)
                      ,s1)))))
        ((EQ (ffn-symb path-tree) 'IF)
         (cons-term* 'IF
                     (fargn path-tree 1)
                     (generate-semantic-function-body (fargn path-tree 2)
                                                      halting-pcs
                                                      dsem-alist api)
                     (generate-semantic-function-body (fargn path-tree 3)
                                                      halting-pcs
                                                      dsem-alist api)))
        (t (er hard 'generate-semantic-function-body
               "Unexpected tip in path-tree, ~x0."
               path-tree))))

; But we don't need a logic-mode version of undistribute-if.  But we were
; concerned about its correctness so we admitted it in :logic mode and proved
; the theorem we cared most about.  We have commented out those events but left
; them for posterity.

; (defun tip-cnt (term)
;   (declare (xargs :mode :logic))
;   (cond ((variablep term) 1)
;         ((fquotep term) 1)
;         ((eq (ffn-symb term) 'IF)
;          (+ (tip-cnt (fargn term 2))
;             (tip-cnt (fargn term 3))))
;         (t 1)))

; The following will be admited in :program mode in this file but could be
; admitted in :logic mode after the definition of tip-cnt above.

(defun undistribute-ifs (term)

; Commented out by Matt K. after v7-2 since tip-cnt is undefined but :program
; mode measures must now be terms:
; (declare (xargs :measure (tip-cnt term)))

  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((eq (ffn-symb term) 'IF)
    (let ((a (fargn term 1))
          (b (undistribute-ifs (fargn term 2)))
          (c (undistribute-ifs (fargn term 3))))
      (cond

; Because this function is doubly recursive (``reflexive'') we have to test the
; measure on the nested recursions.  When operating in :logic mode I'd leave
; these tests in and then prove that they are always true after the function is
; admitted.  But for :program mode purposes we don't need these tests.
;      ((or (not (<= (tip-cnt b) (tip-cnt (fargn term 2))))
;           (not (<= (tip-cnt c) (tip-cnt (fargn term 3)))))
;       term)

       ((and (or (variablep b)
                 (fquotep b)
                 (not (eq (ffn-symb b) 'IF)))
             (nvariablep c)
             (not (fquotep c))
             (eq (ffn-symb c) 'IF))
        (let ((c1 (fargn c 1))
              (c2 (fargn c 2))
              (c3 (fargn c 3)))

; The term is of the form (if a b (if c1 c2 c3)).  We are here enforcing two
; rewrite rules:

; (if a xxx (if c1 xxx c3)) = (if (or a c1) xxx c3)          b and c2 the same
; (if a xxx (if c1 c2 xxx)) = (if (or a (not c1)) xxx c2)    b and c3 the same

          (cond
           ((equal b c2)
            (undistribute-ifs
             `(if (if ,a 't ,c1) ,b ,c3)))
           ((equal b c3)
            (undistribute-ifs
             `(if (if ,a 't (NOT ,c1)) ,b ,c2)))
           (t `(if ,a ,b ,c)))))
       ((and (or (variablep c)
                 (fquotep c)
                 (not (eq (ffn-symb c) 'IF)))
             (nvariablep b)
             (not (fquotep b))
             (eq (ffn-symb b) 'IF))
        (let ((b1 (fargn b 1))
              (b2 (fargn b 2))
              (b3 (fargn b 3)))

; The term is of the form (if a (if b1 b2 b3) c).  We are here enforcing two
; rewrite rules:

; (if a (if b1 xxx b3) xxx) = (if (or (not a) b1) xxx b3)          b2 and c the same
; (if a (if b1 b2 xxx) xxx) = (if (or (not a) (not b1)) xxx b2)    b3 and c the same

          (cond
           ((equal b2 c)
            (undistribute-ifs
             `(if (if (NOT ,a) 't ,b1) ,c ,b3)))
           ((equal b3 c)
            (undistribute-ifs
             `(if (if (NOT ,a) 't (NOT ,b1)) ,c ,b2)))
           (t `(if ,a ,b ,c)))))
       (t `(if ,a ,b ,c)))))
   (t term)))

; Here we prove that the tests for the nested recursions both succeed.
; (defthm tip-cnt-undistribute-ifs
;   (<= (tip-cnt (undistribute-ifs x)) (tip-cnt x))
;   :rule-classes :linear)

; Now we define an evaluator for IF- and NOT-expressions.

; (defevaluator if-evaluator if-evaluator-lst ((IF a b c) (not a)))

; And here is the theorem that undistribute-if preserves the meaning of
; its argument:

; (thm (equal (if-evaluator (undistribute-ifs x) a)
;             (if-evaluator x a)))

; The clock and semantic functions we generate from the path-tree-tuples are
; actually non-executable functions, i.e., we generate DEFUN-NX events, not
; DEFUN events.  The reason is that the bodies are created by rewriting and
; hence all available simplifying rules have been applied to them.  There is no
; guarantee that the stobj state is still used in a single-threaded way.  We
; could generate DEFUNs if the :stobjp field of api is nil, but we don't.

(defun generate-clock-function-defun-pair
  (path-tree-tuple halting-pcs dsem-alist api)

; We generate a pair of the form (pc . (event1 event2 ...)).  Except, in the
; present case, the only event in the list is a DEFUN-NX or DEFUNM-NX of the
; clock function that starts at the beginning of the path tree tuple.  The same
; holds true of generate-semantic-function-defun-pair.

; Another hidden constraint on this function and on its twin,
; generate-semantic-function-defun-pair, is that the body of the generated
; function is ALWAYS of a translated term of the form

; (IF <conjoined-hyps-from-api>
;     <codewalk-results>
;     <base>)

; Thus, we know (fargn <body> 1) is just the :hyps from the api and (fargn
; <body> 2) is the term produced by the codewalk.  (<base> will be '0 for clock
; functions and svar for semantic functions.)  This is important because we
; will explore these un-admitted but translated bodies to detect simple
; invariants and then will insert those invariants into the test of the IF
; above.

; Later we'll use the pc keys of all such pairs to put the events into call
; graph order.  But there is a major wrinkle.  If the call graph requires
; functions f and g to be defined mutually recursively, we will not define f
; and g in a MUTUAL-RECURSION but instead make up a new name, fg, and define a
; flagged version of a combined f and g.  But that will mean also changing all
; the events that call and/or disable f and g so as to use the new name and
; appropriate flag value.  Similarly, if we have to put two correctness
; theorems together we generate the more general flagged theorem and
; appropriately handle the subsequent disabling of the clock.

; To be precise: This function and generate-semantic-function-defun-pair
; generate:

; (pc . ((def clk/sem-fn (svar) ...dcls... body))),

; where def is either DEFUN-NX or DEFUNM-NX, depending on whether the dcls
; include any provided by the user.

; Note in particular the extra level of parens after the dot!  The cdr of the
; pair is a list of events.  But in the case of defun-pairs (as generated for
; both clock and semantic functions) it is always a singleton list of events!

; Warning: If this form is violated, reconsider the handling of mutually
; recursive functions as described in the Essay on Mutually Recursive
; Functions, below.

  (let* ((pc0 (car path-tree-tuple))
         (path-tree (caddr path-tree-tuple))
         (s (access model-api api :svar))
         (clk-fn (generate-def-semantics-name (fnsymbol-name-prefix :clock)
                                           (list pc0)
                                           ""
                                           dsem-alist api))
         (user-supplied-pair
          (assoc-eq clk-fn
                    (cdr (assoc-eq :annotations dsem-alist))))

; user-supplied-dcls must be one of two forms:  (clk-fn (DECLARE ...)) or
; (clk-fn :keyword ...).  If the former, the user is taking over; if
; the latter, we just extend the XARGS.  See the Essay on Annotations.

         (body (generate-clock-function-body path-tree halting-pcs
                                             dsem-alist api))
         (body1 `(IF ,(conjoin (access model-api api :hyps))
                     ,body
                     '0))
         (defcmd (if (and user-supplied-pair
                          (consp (cadr user-supplied-pair)))
                     'DEFUN-NX
                     'DEFUNM-NX))
         (dcls (if (and user-supplied-pair
                        (consp (cadr user-supplied-pair)))
                   (cdr user-supplied-pair)
                   (if (eq (access model-api api :stobjp) t)
                       `((DECLARE
                          (XARGS
                           ,@(cdr user-supplied-pair)
                           :STOBJS (,(access model-api api :svar)))))
                       `((DECLARE
                          (XARGS
                           ,@(cdr user-supplied-pair))))))))
; Recall important invariants: cdr is a singleton list with some flavor of
; defunm whose body is an (IF <hyps-of-api> <body> '0).
    (cons pc0
          `((,defcmd ,clk-fn (,s)
             ,@dcls
             ,body1)))))

(defun generate-clock-function-defun-pairs
  (path-tree-pairs halting-pcs dsem-alist api)
  (cond
   ((endp path-tree-pairs) nil)
   (t (cons (generate-clock-function-defun-pair
             (car path-tree-pairs)
             halting-pcs dsem-alist api)
            (generate-clock-function-defun-pairs
             (cdr path-tree-pairs)
             halting-pcs dsem-alist api)))))

(defun generate-semantic-function-defun-pair
  (path-tree-tuple halting-pcs dsem-alist api)

; See the comment in generate-clock-function-defun-pair.

; Warning: See the warning in the above function too!

  (let* ((pc0 (car path-tree-tuple))
         (path-tree (caddr path-tree-tuple))
         (s (access model-api api :svar))
         (sem-fn (generate-def-semantics-name (fnsymbol-name-prefix :semantic)
                                           (list pc0)
                                           ""
                                           dsem-alist api))
         (user-supplied-pair
          (assoc-eq sem-fn
                    (cdr (assoc-eq :annotations dsem-alist))))
         (body (generate-semantic-function-body path-tree halting-pcs
                                                dsem-alist api))
         (body1 `(IF ,(conjoin (access model-api api :hyps))
                     ,body
                     ,(access model-api api :svar)))
         (defcmd (if (and user-supplied-pair
                          (consp (cadr user-supplied-pair)))
                     'DEFUN-NX
                     'DEFUNM-NX))
         (dcls (if (and user-supplied-pair
                        (consp (cadr user-supplied-pair)))
                   (cdr user-supplied-pair)
                   (if (eq (access model-api api :stobjp) t)
                       `((DECLARE
                          (XARGS
                           ,@(cdr user-supplied-pair)
                           :STOBJS (,(access model-api api :svar)))))
                       `((DECLARE
                          (XARGS
                           ,@(cdr user-supplied-pair))))))))
    (cons pc0
          `((,defcmd ,sem-fn (,s)
              ,@dcls
              ,body1)))))

(defun generate-semantic-function-defun-pairs
  (path-tree-pairs halting-pcs dsem-alist api)
  (cond ((endp path-tree-pairs) nil)
        (t (cons (generate-semantic-function-defun-pair
                  (car path-tree-pairs)
                  halting-pcs dsem-alist api)
                 (generate-semantic-function-defun-pairs
                  (cdr path-tree-pairs)
                  halting-pcs dsem-alist api)))))

; Note:  the following pairs of functions are clones of each other.

;     clock                                semantics
; generate-clock-function-body         generate-semantic-function-body
; generate-clock-function-defun-pair   generate-semantic-function-defun-pair

; For each starting pc, we generate a CLK-root-name-pc and SEM-root-name-pc.

; See Guide.
;       (A.5.1) identifying certain trivial invariants that may be crucial to
;               termination, and

; Essay on the Design of a Simple Invariant Detector:  Disguised Constants

; Note: This essay recapitulates the sketch of (A.5.1) but with still more
; implementation-level detail.  It was written prior to the Guide and the
; example developed therein.  Thus, the example is different and the imagined
; machine model is different.  Translating from the essay's model to the
; Guide's, this essay's ``(rd (:loc 1) s)'' is the Guide's ``(nth 1 (rd :locals
; s)).''

; Suppose a piece of code loads -1 into local 2 then iterates, counting local 1
; down by successively adding local 2 to it.  The recursive calls of the loop
; clock and semantics functions will be on some state expression like this:

; (wr (:LOC 1) (+ (rd (:LOC 1) s) (rd (:LOC 2) s)) s)

; or, if we think of r1 and r2 as the two virtual formals:

; r1 <-- (+ r1 r2);
; r2 <-- r2;          [implicit, by virtue of being absent]

; which has an obvious expression as a vcall with :slot expressions.

; Of course there's no way to admit this function since we have not recorded
; the fact that r2, i.e., (:LOC 2), is constantly -1.  We call r2, i.e., (rd
; '(:LOC 2) s), a ``disguised constant'' in this function.  The purpose of this
; next section is to detect such simple invariants and modify the definition of
; the loop function (and its correctness theorem) appropriately.  To do this we
; must inspect the entire system of proposed definitions.

; This discussion focuses first on simple loops, i.e., singly recursive
; functions.  Then we discuss modifications for multiple loops, i.e., flagged
; mutual recursions.

; For example, let CLK-0 and SEM-0 be the respective top-level clock and
; semantic functions (which load (:LOC 2) with -1) and let CLK-2 and SEM-2 be
; the loop functions.  Then in a case like that described above we will see:

;  (defunm clk-0 (s)                          ; Top-level entry initializes
;    (c+ '2 (clk-2 (wr '(:LOC 2) '-1 s))))    ;  disguised constant

;  (defunm clk-2 (s)                          ; Loop function uses it but
;    (if <hyps-from-api>                       ;  does not alter it.
;        (if (equal (rd '(:LOC 1) s) '0)
;            0
;            ...(clk-2 (wr '(:LOC 1)
;                           (+ (rd '(:LOC 1) s) (rd '(:LOC 2) s))
;                           s))...)
;        0))

; and a similar arrangement for sem-0 and sem-2.  The key property, in this
; simple case, is that every function that calls clk-2 (except clk-2 itself)
; sets '(:LOC 2) to '-1 and clk-2 does not change '(:LOC 2).

; Things get more complicated for nested loops.  Consider a program with a
; top-level entry that calls an outer loop which calls an inner loop.  Given
; the way we actually translate this, the top-level calls the outer loop, which
; calls the inner loop, which calls itself and the outer loop.  Suppose both
; loops use distinct disguised constants.  There are two possibilities, (a) the
; top-level initializes both disguised constants and the loops just use them,
; or (b) the top-level initializes the outer loop's constant and the outer loop
; initializes the inner loop's constant.  In either case, we see something
; different than the simple case described above: it's possible for a loop
; function that uses a disguised constant to be called without that constant
; being explicitly set by the caller.  Instead, that constant's value is
; ``passed through.''  This is easy to to see in case (a): the top level set
; the constant for the inner loop and the outer loop just calls the inner loop
; on a state that's already been set up.  But this also happens in case (b)
; because the inner loop calls the outer loop without setting the outer loop's
; constant.

; So the key to discovering disguised constants is to propagage assignments of
; constants through the entire system of definitions.

; To make the discovery of disguised constants a little simpler, we introduce
; the notion of a call of a function on virtual formals, or a so-called
; ``vcall.''  Given a call of a clk or sem function, gn, on a modified state,
; the corresponding vcall is of the form (gn ...(:SLOT v_i a_i)...), where the
; :SLOT expressions are as in Terminatricks.  We thus transform calls like:

; (clk-2 (wr '(:LOC 1) (+ (rd '(:LOC 1) s) (rd '(:LOC 2) s))
;          (wr '(:LOC 4) '17
;            (wr ':PC '2 s)))

; into the ``vcall''

; (clk-2 (:SLOT ':PC '2)
;        (:SLOT '(:LOC 1) (+ (rd '(:LOC 1) s) (rd '(:LOC 2) s)))
;        (:SLOT '(:LOC 4) '17))

; A vcall is a pair consisting of a function symbol consed onto a list of :SLOT
; expressions in arbitary order.

; We convert the entire system of preliminary definitions into an alist of
; pairs of the form (fn pc . vcalls), where vcalls is the list of all vcalls
; appearing in the body of the preliminary defun of fn.  The resulting alist is
; named fn-to-pc-and-vcalls-alist.

; We now turn to the discovery of disguised constants.  This is done by
; building another data structure recording what we know about the vformals
; upon entry to each function in the system.  One pass over the entire system
; definition, is called a ``step.''  We iterate steps until the recorded facts
; no longer change.  So the key is what we do in one such step.

; One step of constant propagation sweeps through the entire system of
; definitions and propagates knowledge of constants much like the Java Byte
; Code Verifier propagates type signatures.  We record our discovered knowledge
; in an alist that pairs function names with alists that record what we know
; about the virtual formals upon every entry (visited so far) to the associated
; function.  A typical entry in ans is:

; (fn . (...(v_i . u_i)...))

; where the v_i are virtual formals and the u_i record what we know about the
; value of v_i on every call of fn.  We call (...(v_i . u_i)...) the ``vformal
; alist for fn.''  U_i is either :changing, meaning that the value of v_i has
; been seen to change in some ``arbitrary'' way, or u_i is a non-empty
; true-list of evgs, meaning that v_i takes on one of those explicit values on
; each call.  If a vformal is not mentioned in the vformal alist for fn it
; means that we haven't (yet) seen any assignment to it, which makes it an
; unchanging vformal (so far).

; Now imagine that we are in function g.  The vformal alist for g will tell us
; what we know about some vformals.  Imagine that g calls f after setting some
; vformal, v_i to some actual a_i.  We will have a vformal alist for f.  How do
; we modify it in light of this call and its current context?

; First, every (v_i . u_i) pair in the vformal alist for g that is not
; overridden by a slot in the call of f, should be ``merged'' into the vformal
; alist for f.

; Second, we merge (v_i . u) -- and we do mean ``u'' not ``u_i'' -- into the
; vformal alist for fn, where u is derived from a_i as follows: if a_i is a
; quoted constant, u is the singleton list containing the evg of that constant
; (so we can just union it into other such lists); else u is :changing.

; To merge (v_i . u_i) into an alist with no v_i entry is just to add (v_i
; . u_i) to it.  To merge (v_i . u_i) into an alist containing (v_i . w_i) we
; take the weaker of the u_i and w_i: if either is :changing we use :changing,
; if both are constants/lists of constants, we combine them into a longer list.
; (Remember that the basic meaning of a u_i is a disjunction, so if v_i is 1 or
; 2 or v_i is 3 or 4, then v_i is 1 or 2 or 3 or 4.)

; Eventually this iterated step process will stabilize.  When it does, we will
; have identified some supposed invariants about certain v_i in certain fn,
; namely, for every (v_i . u_i) in fn's vformal-alist (except those where u_i
; is :changing) we know that every entry to fn has v_i set to a member of u_i.
; Those v_i are the ``disguised constants'' of fn and u_i is the ``range.''

; If v is a disguised constant with range r in fn, then we can modify the hyps
; in fn governing the recursive calls of fn with the additional conjunct
; (member v 'r).  This can be optimized in the case that r is a singleton list.

; We need not perform this modification on the correctness theorem.  This was a
; surprising discovery (forced by repeatedly trying to figure out the right hyp
; to add).  How could it be that (m1 s (clk s)) = (sem s), if sem uses a
; disguised constant, v_i, and we haven't stipulated in the correctness theorem
; that v_i is in the range u_i?

; The reason is that (clk s) on the left-hand side of the conclusion contains
; the test that v_i is in u_i and if that condition is violated, clk returns 0
; so the left-hand side is S.  The exact same test is in (sem s) and it also
; produces S.  So this is a ``convenient weakness.''  Convenient because we
; needn't modify correctness theorems, and a weakness because it means our
; correctness theorems have some ``hidden'' hypotheses, namely the v_i in u_i
; conditions.  But the only way to eliminate these hidden hypotheses would be
; to replace the disguised constants with actual constants and redefine clk and
; sem to be terminating without the range conditions and then insert the range
; conditions into the correctness theorem hyps.

; The culmination of all our processing of disguised constants is the
; disguised-constant-4-tuple-lst, which is a list of 4-tuples of the form: (fn
; pc v_i u'_i), where u'_i is the lexordered range of the disguised constant
; v_i in fn (which was derived starting at pc).

; We will check that the disguised constant 4-tuple for a clock function at a
; given pc is identical (in v_i and u'_i) to that for the semantic function at
; pc.  This can be done by computing the 4-tuples for all the clock functions
; and for all the semantic functions, stripping off the cars (the idiosyncratic
; clock or semantic function symbols) and comparing the two lists of triples
; with equal.

; Once this check has been performed, we may use either list of 4-tuples as
; long as we key on the pc.  It is from this list of 4-tuples that we generate
; the (member v 'r) hyps to insert into the definitions, based on the pc
; involved.

; Now we discuss how all this fits into the basic flow of def-semantics.  The key
; function is def-semantics-post-events, where we use

;  generate-clock-function-defun-pairs
;  generate-semantic-function-defun-pairs

; to produce lists of pcs paired with singleton lists of events.  At this point
; in the flow, even multiple loops are coded as separate recursive functions
; (that will be combined into a flagged singly recursive function later in the
; flow).

; Note that we cannot identify disguised constants until we have made the first
; cut at generating the clock and semantic function definitions.  We call these
; the ``preliminary'' definitions, since our intent is possibly to modify them.

; So we first generate the preliminary clock and semantic function defun pairs,
; from each we generate a fn-to-pc-and-vcalls-alist, and from that we generate
; the two disguised-constants-4-tuple-lsts.  Then we compare the two 4-tuple
; lists to make sure the corresponding clock and semantic functions call for
; the same modifications.  Then we use the 4-tuple lists to modify the hyps in
; the two sets of definitions.

; End of the Design of a Simple Invariant Detector:  Disguised Constants

; This code converts preliminary function bodies into a list of the ``virtual
; calls'' contained therein, where a ``virtual call'' or vcall is (fn ...(:SLOT
; vi ai) ...).

(mutual-recursion

 (defun collect-calls-to-slots-alist (formals term fns-in-system wrld ans)

; We accumulate into ans pairs of the form (fn . slots), for every call in term
; of a function name listed in fns-in-system.  The slots is a list
; of (:SLOT vformal actual) specifying the virtual formals modified in the
; call and the new value.

   (cond
    ((variablep term) ans)
    ((fquotep term) ans)
    ((member-eq (ffn-symb term) fns-in-system)
     (add-to-set-equal
      (cons (ffn-symb term)
            (virtual-slots
             formals
             (fargs term)
             (cdr (assoc-eq :list
                            (table-alist 'generalized-updater-drivers wrld)))
             (cdr (assoc-eq :list
                            (table-alist 'generalized-updater-drivers wrld)))))
      ans))
    (t (collect-calls-to-slots-alist-lst formals
                                         (fargs term)
                                         fns-in-system wrld ans))))

 (defun collect-calls-to-slots-alist-lst (formals term-lst fns-in-system wrld ans)
   (cond
    ((endp term-lst) ans)
    (t (collect-calls-to-slots-alist-lst
        formals
        (cdr term-lst)
        fns-in-system
        wrld
        (collect-calls-to-slots-alist formals
                                      (car term-lst)
                                      fns-in-system wrld ans))))))

(defun generate-fn-to-pc-and-vcalls-alist (defun-pairs fns-in-system wrld)

; We convert a list of preliminary definition pairs, (pc . defn), into an alist
; with elements of the form (fn pc . vcalls), where vcalls are the virtual
; calls contained within the body of fn.

  (cond
   ((endp defun-pairs) nil)
   (t (let* ((pair (car defun-pairs))
             (pc (car pair))
             (defn (car (cdr pair)))
             (fn (cadr defn))
             (formals (caddr defn))
             (body (car (last defn))))

; The check below is for sanity only.  We don't expect it to fail unless we
; change the format generated by generate-clock-function-defun-pairs, etc.

        (cond
         ((and (consp pair)
               (true-listp (cdr pair))
               (equal (len (cdr pair)) 1)
               (symbolp fn)
               (true-listp formals)
               (equal (len formals) 1)
               (not (variablep body))
               (not (fquotep body))
               (eq (ffn-symb body) 'IF)
               (or (equal (fargn body 3) *0*)
                   (equal (fargn body 3) (car formals))))
          (cons
           (cons fn
                 (cons pc
                       (collect-calls-to-slots-alist formals
                                                     (fargn body 2)
                                                     fns-in-system
                                                     wrld
                                                     nil)))
           (generate-fn-to-pc-and-vcalls-alist (cdr defun-pairs)
                                               fns-in-system
                                               wrld)))
         (t (er hard 'generate-fn-to-pc-and-vcalls-alist
                "This function was supposed to be applied to a list of pairs ~
                 of the form (pc . ((def fn (svar) ...dcls... body))) where ~
                 def is some flavor of DEFUNM, fn is a function symbol, and ~
                 body is an IF-expression whose 3rd argument is either 0 or ~
                 svar.  This was understood to be the shape of the outputs of ~
                 the functions generate-clock-function-defun-pairs and ~
                 generate-semantic-function-defun-pairs.  But we've just seen ~
                 the entry ~X01 which is not of this form."
                pair
                nil)))))))

(defun map-actual-to-u (term)
  (if (quotep term)
      (cdr term)  ; (QUOTE a) ==> (a)
      :changing))

(defun merge-u1-and-u2 (u1 u2)
  (cond ((or (eq u1 :changing)
             (eq u2 :changing))
         :changing)
        (t (union-equal u1 u2))))

(defun merge-v-u-into-vformal-alist (v u alist)
  (let ((temp (assoc-equal v alist)))
    (cond ((null temp) (cons (cons v u) alist))
          (t (put-assoc-equal v (merge-u1-and-u2 u (cdr temp)) alist)))))

(defun merge-vformal-alists (alist1 alist2)
  (cond
   ((endp alist1) alist2)
   (t (merge-vformal-alists
       (cdr alist1)
       (merge-v-u-into-vformal-alist (car (car alist1))
                                     (cdr (car alist1))
                                     alist2)))))

(defun merge-slots-into-caller-vformal-alist (slots vformal-alist)

; Suppose some function G calls F with the (:SLOT v_i a_i) expressions in
; slots.  Let vformal-alist be the vformal alist for the caller G.  We create a
; vformal alist to merge into that of F.  Note that a slot in which v_i is
; assigned a constant overrides a :changing u in the caller!

  (cond ((endp slots) vformal-alist)
        (t (let ((v (cadr (car slots)))
                 (a (caddr (car slots))))
             (merge-slots-into-caller-vformal-alist
              (cdr slots)
              (cond ((quotep a)
                     (put-assoc-equal v (cdr a) vformal-alist))
                    (t (put-assoc-equal v :changing vformal-alist))))))))

(defun one-pass-constant-propagation-vcalls (vformal-alist-g vcalls ans)
  (cond
   ((endp vcalls) ans)
   (t (one-pass-constant-propagation-vcalls
       vformal-alist-g
       (cdr vcalls)
       (let* ((f (car (car vcalls)))
              (slots (cdr (car vcalls)))
              (vformal-alist-f (cdr (assoc-eq f ans))))
         (put-assoc-eq f
                       (merge-vformal-alists
                        (merge-slots-into-caller-vformal-alist
                         slots
                         vformal-alist-g)
                        vformal-alist-f)
                       ans))))))

(defun one-pass-constant-propagation (lst ans)
  (cond
   ((endp lst) ans)
   (t (one-pass-constant-propagation
       (cdr lst)
       (let* ((g (car (car lst)))
              (vcalls (cddr (car lst))))
         (one-pass-constant-propagation-vcalls
          (cdr (assoc-eq g ans))
          vcalls
          ans))))))


(defun constant-propagation (fn-to-pc-and-vcalls-alist ans trace)
  (cond
   ((> (len trace) 5)
    (er hard 'constant-propagation
        "Oops!  Constant-propagation seems to loop.  The trace -- earliest to ~
         latest -- is:  ~X01"
        (revappend (cons ans trace) nil)))
   (t
    (let ((ans1 (one-pass-constant-propagation fn-to-pc-and-vcalls-alist ans)))
      (cond
       ((equal ans ans1)
        ans)
       (t (constant-propagation fn-to-pc-and-vcalls-alist
                                ans1
                                (cons ans trace))))))))

; Given the alist mapping functions in the system to their vformal alists, we
; now identify the disguised constants.

(defun disguised-constant-4-tuple-lst2 (pc-term fn pc vformals-alist)
  (cond
   ((endp vformals-alist) nil)
   ((consp (cdr (car vformals-alist)))
    (cond
     ((equal pc-term (car (car vformals-alist)))
      (disguised-constant-4-tuple-lst2 pc-term fn pc (cdr vformals-alist)))
     (t
      (cons
       (list fn pc (car (car vformals-alist))
             (merge-sort-lexorder (cdr (car vformals-alist))))
       (disguised-constant-4-tuple-lst2 pc-term fn pc (cdr vformals-alist))))))
   (t (disguised-constant-4-tuple-lst2 pc-term fn pc (cdr vformals-alist)))))

(defun disguised-constant-4-tuple-lst1
  (pc-term fn-to-vformal-alist-alist fn-to-pc-and-vcalls-alist)

; Here, pc-term is the term from the machine model that accesses the pc from
; the state variable, e.g., (get-pc st).  It is used to identify which of the
; vformals is the pc, the settings of which we wish to ignore in this
; computation.  Each element of fn-to-vformal-alist-alist is of the form (fn
; . (...(v_i . u_i)...)) where u_i is either :changing or a non-empty true-list
; of evgs.  For each entry such that v_i maps to a list, we create a 4-tuple
; (fn pc v_i u'_i), where pc is the pc from which fn was derived and u'_i is
; the lexordered version of u_i, otherwise known as the ``range'' of v_i in fn.
; Finally, fn-to-pc-and-vcalls-alist is an alist with elements of the form (fn
; pc . vcalls), where vcalls are the virtual calls contained within the body of
; fn.

  (cond
   ((endp fn-to-vformal-alist-alist) nil)
   (t (append (disguised-constant-4-tuple-lst2
               pc-term
               (car (car fn-to-vformal-alist-alist))
               (cadr (assoc-eq (car (car fn-to-vformal-alist-alist))
                               fn-to-pc-and-vcalls-alist))
               (cdr (car fn-to-vformal-alist-alist)))
              (disguised-constant-4-tuple-lst1 pc-term
                                               (cdr fn-to-vformal-alist-alist)
                                               fn-to-pc-and-vcalls-alist)))))

(defun collect-all-known-vformals1 (vcalls vformals)
  (cond ((endp vcalls) vformals)
        (t (collect-all-known-vformals1
            (cdr vcalls)
            (union-equal
             (strip-cadrs (cdr (car vcalls)))
             vformals)))))

(defun collect-all-known-vformals (fn-to-pc-and-vcalls-alist vformals)
  (cond
   ((endp fn-to-pc-and-vcalls-alist)
    vformals)
   (t (collect-all-known-vformals
       (cdr fn-to-pc-and-vcalls-alist)
       (collect-all-known-vformals1
        (cddr (car fn-to-pc-and-vcalls-alist))
        vformals)))))

(defun initial-fn-to-vformal-alist-alist (fn-to-pc-and-vcalls-alist)

; The first function in the fn-to-pc-and-vcalls-alist is always the entry
; point, corresponding to the :init-pc of the api, thanks to the reordering of
; cutpoints in def-semantics-post-events.  We actually know that the pc of the
; entry function is the (cadr (car fn-to-pc-and-vcalls-alist)), but we just
; assume it can be anything because we handle the pc specially in forming the
; defun pairs.  So this function assumes that upon entry to the entry, every
; vformal is :changing.  Note that we don't make assignments here to vformals that
; are read but never written.  E.g., (nth 2 (rd :locals s)) might be involved in
; calculations but never assigned by any routine, in which case we don't even consider
; it as a possible disguised constant.

  (list (cons (car (car fn-to-pc-and-vcalls-alist))
              (pairlis-x2
               (collect-all-known-vformals fn-to-pc-and-vcalls-alist nil)
               :changing))))

(defun disguised-constant-4-tuple-lst (pc-term fn-to-pc-and-vcalls-alist)

; Identify disguised constants by creating a list of 4-tuples, each of the form
; (fn pc v_i u'_i), where u'_i is the lexordered range of the disguised
; constant v_i in fn (which was derived starting at pc).

  (let ((fn-to-vformal-alist-alist
         (constant-propagation fn-to-pc-and-vcalls-alist
                               (initial-fn-to-vformal-alist-alist
                                fn-to-pc-and-vcalls-alist)
                               nil)))
    (disguised-constant-4-tuple-lst1 pc-term fn-to-vformal-alist-alist
                                     fn-to-pc-and-vcalls-alist)))

; Now we compute the conjunct to add to the hypotheses for the definition of
; the (clock or semantic) function derived from pc, given the disguised
; constant 4-tuples.  (Note that the 4-tuples provided are always those for the
; clock functions only because we will have confirmed that the semantic
; functions have the same 4-tuples except for the names of the functions.)

(defun disguised-constant-hyp1 (pc disguised-constant-4-tuple-lst body)
  (cond
   ((endp disguised-constant-4-tuple-lst) nil)
   ((equal pc (cadr (car disguised-constant-4-tuple-lst)))
    (let ((v (caddr (car disguised-constant-4-tuple-lst)))
          (r (cadddr (car disguised-constant-4-tuple-lst))))
      (cond
       ((occur v body)
        (cons
         (if (null (cdr r))
             `(equal ,v ,(kwote (car r)))
             `(member-equal ,v ,(kwote r)))
         (disguised-constant-hyp1 pc (cdr disguised-constant-4-tuple-lst) body)))
       (t (disguised-constant-hyp1 pc (cdr disguised-constant-4-tuple-lst) body)))))
   (t (disguised-constant-hyp1 pc (cdr disguised-constant-4-tuple-lst) body))))

(defun disguised-constant-hyp (pc disguised-constant-4-tuple-lst body)
  (conjoin (disguised-constant-hyp1 pc disguised-constant-4-tuple-lst body)))

; And now we map over a list of defun-pairs and insert the disguised-constant hyp

(defun modify-hyps-in-defun-pair (disguised-constant-4-tuple-lst defun-pair)

; Defun-pair is (pc . ((def fn (svar) ...dcls... (IF hyp code base)))).
; We generate the disguised constant hyp for pc and conjoin it with hyp to produce
; a new defun-pair.

  (let* ((pc (car defun-pair))
         (event (car (cdr defun-pair)))
         (def (car event))
         (fn (cadr event))
         (formals (caddr event))
         (dcls (all-but-last (cdddr event)))
         (body (car (last event))) ; (IF hyps code base)
         (hyps (fargn body 1))
         (code (fargn body 2))
         (base (fargn body 3))
         (dc-hyp (disguised-constant-hyp pc disguised-constant-4-tuple-lst body)))
    (cond
     ((equal dc-hyp *t*) defun-pair)
     (t `(,pc . ((,def ,fn ,formals
                       ,@dcls
                       (IF ,(conjoin2 hyps dc-hyp) ,code ,base))))))))

(defun modify-hyps-in-defun-pairs (disguised-constant-4-tuple-lst defun-pairs)

; Each pair in defun-pairs is (pc . ((def fn (svar) ...dcls... body))), where
; body is (IF <conjoined-hyps-from-api> <body> <base>) and we add
; the conjunct(s) for the derived constant(s) of pc to
; <conjoined-hyps-from-api>.

  (cond
   ((endp defun-pairs) nil)
   (t (cons (modify-hyps-in-defun-pair disguised-constant-4-tuple-lst
                                       (car defun-pairs))
            (modify-hyps-in-defun-pairs disguised-constant-4-tuple-lst
                                        (cdr defun-pairs))))))

; This completes the identification of disguised constants.  We stitch all this together in
; def-semantics-post-events below.

; Preview of coming attractions:

; We will create the call graph of the clock and semantic functions from the
; start/terminal pc components of the path-tree-tuples.  Then we'll close it
; under reflexivity and transitivity and sort it to obtain a list like that
; above.  Then we strip out the terminal pcs and keep just the buckets of
; starting pcs.  The singleton elements in the final ordering correspond to
; singly-recursive functions and the other elements correspond to mutually
; recursive functions.  The functions should be introduced in the order listed,
; e.g., ((4) (1 2 3) (5)) means introduce the singly recursive function for pc
; 4, then the mutually recursive clique of fns for pcs 1, 2, and 3, and finally
; the singly-recursive function for 5.

(defun create-call-graph (path-tree-tuples)
  (cond ((endp path-tree-tuples) nil)
        (t (let* ((tuple (car path-tree-tuples))
                  (start-pc (car tuple))
                  (terminal-pcs (cadr tuple)))
             (cons (cons start-pc terminal-pcs)
                   (create-call-graph (cdr path-tree-tuples)))))))

; See Guide.
;       (A.5.2) removing mutual recursion.

; Essay on Transforming Mutually Recursive Functions to Singly-Recursion Ones

; Note: This elaborates a bit on (A.5.2).

; The result of the above function is an ``ordering'' such as (10 (20 30 40)
; 50) meaning the function for pc 10 should be defined first, then functions
; for pcs 20, 30, and 40 should be defined simultaneously
; (mutually-recursively), and then that for pc 50 should be defined.

; We will use this ordering to generate and order a set of ``defun pairs.''
; Initially, each such pair is (pc . ((def fn (s) ...))), where pc is a pc, def
; is either DEFUN-NX or DEFUNM-NX.  fn is the new function name -- typically it
; will be either CLK-pc or SEM-pc -- and s is the state variable.  The
; definition of fn assumes that the pc of the initial s is pc, i.e., the
; function is a derived function for the code starting at pc.

; However, the process of ``applying'' this ordering to the defun pairs (see
; apply-call-graph-ordering-to-defun-pairs) will actually transform the
; implicit mutual recursion into a singly recursive definition!  We refer to
; this as the ``transformation to singly-recursive form'' and it is done by the
; function transform-to-singly-recursive.  In particular, it will collect all
; the defuns of those fns in an implicitly mutually recursive clique, say
; fn-20, fn-30, and fn-40, and form a new definition of a singly-recursive
; function from them, named fn-20-30-40.  This has global ramifications: all
; subsequent calls of fn-20, fn-30, and fn-40 must be replaced by calls of the
; new fn-20-30-40.

; If the bodies of fn-20, fn-30, and fn-40 are body-20, body-30, and body-40,
; then the body of fn-20-30-40 is:

; (if (equal (pc s) 20)
;     body-20'
;     (if (equal (pc s) 30)
;         body-30'
;         body-40'))

; where the primed bodies are the original ones with all calls of the fns in
; the clique replaced by calls of fn-20-30-40.

; Note that this assumes that when one of the original bodies calls one of its
; peers recursively, (fn-pc new-s), the appropriate original function, fn-20,
; fn-30, or fn-40, can be determined by the pc of new-s.  We believe this is
; always the case, given the way clock and semantic functions are generated.

; Note that this method of transforming a mutually-recursive clique into a
; singly-recursive definition is not generally applicable!  In particular, the
; transformation does NOT introduce a flag standing for the name of the
; function being computed by the singly-recursive function.  All necessary
; information is encoded in the state argument because it only ``makes sense''
; to apply a clock or semantic function to a state with the pc stipulated when
; the function was dervied.  Being untyped, mutually-recursive ACL2 functions
; can be applied universally.  E.g., '(A (B X) (C Y)) is both a (pseudo-) term
; and a list of (pseudo-) terms and so it would make sense to use it as the
; second argument to either sublis-var or sublis-var-lst; one can't tell by
; looking at the data what type of thing something is and thus one can't know
; for sure which of the mutually-recursive functions in the clique is
; appropriate for it.  But with clock and semantic functions as derived here,
; it only ``makes sense'' to apply the functions to states with the appropriate
; pc.  We quote ``makes sense'' because one can apply it to states with other
; pcs and ACL2 will return an answer, but that answer will not be as predicted
; by the correctness theorem because the correctness theorem stipulates the
; initial pc.  Thus ``makes sense'' here means ``is correct as per the
; correctness theorem.''

; However, after the transformation to singly-recursive form, it is difficult
; to determine which function is being called!  To do so, one would have to
; recover the pc of the new state in the call, probably by symbolic rewriting,
; and possibly even considering the governing hypotheses of the call.

; Because we will also have to rename the occurrences of the original functions
; in the theorems about them, the process of applying the ordering to the defun
; pairs will also produce a renaming-alist, mapping the original names to the
; new name, e.g., ((fn-20 . fn-20-30-40) (fn-30 . fn-20-30-40) (fn-40
; . fn-20-30-40)).

(defun collect-cadr-assoc-equal (keys alist)
; Alist is assumed to map each key to a list of items and this function
; collects the first item in each list of the given keys.  The returned
; list is in the order the keys are listed.
  (cond ((endp keys) nil)
        (t (cons (cadr (assoc-equal (car keys) alist))
                 (collect-cadr-assoc-equal (cdr keys) alist)))))

(defun apply-renaming-alist-to-def (renaming-alist defun-event)

; Renaming-alist is a functional substitution and defun event is a defun-like
; event (DEFUN-NX ...) or (DEFUNM-NX ...).  We replace the body of the def with
; the result of renaming the functions in it.  We don't change the name of the
; event or any declarations that might be in it.  We return the renamed
; defun-event'.

  (cond ((and (consp defun-event)
              (member-eq (car defun-event) '(defun-nx defunm-nx)))
         (append (all-but-last defun-event)
                 (list (sublis-fn-simple renaming-alist (car (last defun-event))))))
        (t (er hard 'apply-renaming-alist-to-body
               "This function is supposed to be applied to an event of the ~
                form (DEFUN-NX ...) or (DEFUNM-NX ...) and ~X01 is neither!"
               defun-event
               nil))))

(defun apply-renaming-alist-to-def-lst (renaming-alist defun-events)

; Renaming-alist is a fn to fn renaming and defun-events is a list of
; defun-like events, (def fn (s) ... body).  We apply renaming-alist to each
; body and return a list of renamed defun-events in the same order.  Only the
; bodies of the defuns have been renamed!  We did not change the function names
; being defined nor did we hit the declarations.

  (cond ((endp defun-events) nil)
        (t (cons (apply-renaming-alist-to-def renaming-alist
                                              (car defun-events))
                 (apply-renaming-alist-to-def-lst renaming-alist
                                                  (cdr defun-events))))))

(mutual-recursion
 (defun peers-called (peer-fns term ans)
   (cond ((variablep term) ans)
         ((fquotep term) ans)
         ((flambdap (ffn-symb term))
          (peers-called-lst peer-fns
                            (fargs term)
                            (peers-called peer-fns
                                          (lambda-body (ffn-symb term))
                                          ans)))
         (t (peers-called-lst peer-fns
                              (fargs term)
                              (if (member-eq (ffn-symb term) peer-fns)
                                  (add-to-set-eq (ffn-symb term) ans)
                                  ans)))))

 (defun peers-called-lst (peer-fns terms ans)
   (cond ((endp terms) ans)
         (t (peers-called-lst peer-fns
                              (cdr terms)
                              (peers-called peer-fns (car terms) ans)))))
 )

(defun count-peers-called-lst (peer-fns defs)

; Given a list of mutually-recursive function names, peer-fns, and a list of
; their defun-like events, we return a list in 1:1 correspondence with the
; latter listing the number of peers called by each function.  E.g., given
; peers-lst (f g h) and defs in the same order, and assuming that f calls only
; one of the peers, g calls all three, and h calls only two, we return (1 3 2).

; Note that the returned counts are in the order of defs.

  (cond ((endp defs) nil)
        (t (cons (length (peers-called peer-fns (car (last (car defs))) nil))
                 (count-peers-called-lst peer-fns (cdr defs))))))

(defun generate-case-expression (key pcs terms)

; Key is a term, pcs is a list of k>0 evgs, and terms is a list of k terms.
; We return the translated form of

;  (case key
;    (pc_1 term_1)
;    (pc_2 term_2)
;    ...
;    (otherwise term_k)

  (cond
   ((endp (cdr pcs)) (car terms))
   (t (let ((pc (car pcs))
            (term (car terms)))
        `(if (equal ,key ',pc)
             ,term
             ,(generate-case-expression key (cdr pcs) (cdr terms)))))))

(defun monotonousp (lst)
; A list is `monotonous' iff every element is the same as every other.
  (cond ((endp lst) t)
        ((endp (cdr lst)) t)
        (t (and (equal (car lst) (cadr lst))
                (monotonousp (cdr lst))))))

(defun strip-bodies (defun-events)
  (cond ((endp defun-events) nil)
        (t (cons (car (last (car defun-events)))
                 (strip-bodies (cdr defun-events))))))

(defun transform-to-singly-recursive (pcs pairs renaming-alist dsem-alist api)

; We assume pcs has at least two elements and that all the elements in pcs are
; bound in pairs to defun-like singleton event lists.  We generate a defun-like
; event combining all of the definitions into one singly-recursive definition.
; We generate a DEFUN-NX form if the user has provided an annotation for this
; new function symbol.  Otherwise we generate a DEFUNM-NX form.

  (let* ((defs0 (collect-cadr-assoc-equal pcs pairs))
         (fns (strip-cadrs defs0))
         (bodies (strip-bodies
                  (apply-renaming-alist-to-def-lst renaming-alist defs0)))
         (new-fn (generate-def-semantics-name
                  (fnsymbol-name-prefix
                   (get-kind-from-fnsymbol-name ; :CLOCK or :SEMANTIC
                    (symbol-name (car fns))))
                  pcs
                  ""
                  dsem-alist api))
         (svar (access model-api api :svar))
         (key (make-fn-application (access model-api api :get-pc)
                                   (list svar)))
         (user-supplied-pair
          (assoc-eq new-fn
                    (cdr (assoc-eq :annotations dsem-alist))))
         (defcmd (if (and user-supplied-pair
                          (consp (cadr user-supplied-pair)))
                     'DEFUN-NX
                     'DEFUNM-NX))
         (dcls (if (and user-supplied-pair
                        (consp (cadr user-supplied-pair)))
                   (cdr user-supplied-pair)
                   (if (eq (access model-api api :stobjp) t)
                       `((DECLARE
                          (XARGS
                           ,@(cdr user-supplied-pair)
                           :STOBJS (,(access model-api api :svar)))))
                       `((DECLARE
                          (XARGS
                           ,@(cdr user-supplied-pair))))))))

; Note that pcs, defs0, fns, counts, and bodies are in the same order because
; defs0 is in the order listed in pcs and all the others are in the order
; listed by defs0.  Thus:

; lst       (nth i lst)    meaning

; fns          fn_i        original name of some CLK- or SEM- fn
; pcs          pc_i        starting pc from which fn_i dervied
; defs0        def0_i      defun-like event for fn_i
; bodies       body_i      body of fn_i with all peers replaced
;                          as per the renaming alist.

    `(,defcmd ,new-fn (,svar)
       ,@dcls
       ,(generate-case-expression key pcs bodies))))

(defun apply-call-graph-ordering-to-defun-pairs
  (ordering pairs events renaming-alist dsem-alist api)

; Ordering is a list containing lists of pcs.  Singleton elements denote pcs
; whose corresponding derived functions are singly recursive and non-singleton
; elements denote pcs whose corresponding derived functions are mutually
; recursive.  Pairs is a list of pairs, each with a pc in the car and a
; singleton list containing a defun-like event, e.g., DEFUN-NX and DEFUNM-NX,
; in the cdr, e.g.,

; ((10 . ((defun-nx fn-10 (s) ...))) (20 . ((defunm-nx fn-20 (s) ...))) ...)

; The bodies of the defun-like events are in translated form.  We order the
; events as specified by the ordering and transform all mutually recursive
; functions into singly recursive ones, possibly including
; terminatricks-hints.

; The renaming-alist maps original mutually-recursive function names to their
; singly recursive counterparts, e.g., ((fn-20 . fn-20-30-40) (fn-30
; . fn-20-30-40) ...)  and these renamings are applied to subsequent defun-like
; events.  The final reordered list of defun-like events is returned along with
; the final renaming alist, (mv events renaming-alist).

  (cond ((endp ordering)
         (mv (revappend events nil) renaming-alist))
        ((cdr (car ordering)) ; mutually recursive nest
         (let* ((pcs (car ordering))
                (old-fns (strip-cadrs (collect-cadr-assoc-equal pcs pairs)))
                (new-fn (generate-def-semantics-name
                         (fnsymbol-name-prefix
                          (get-kind-from-fnsymbol-name ; :CLOCK or :SEMANTIC
                           (symbol-name (car old-fns))))
                         pcs
                         ""
                         dsem-alist api))
                (new-renaming-alist (append (pairlis-x2 old-fns new-fn) renaming-alist))
                (new-def (transform-to-singly-recursive
                          pcs pairs
                          new-renaming-alist
                          dsem-alist api)))
           (apply-call-graph-ordering-to-defun-pairs
            (cdr ordering)
            pairs
            (cons new-def events)
            new-renaming-alist
            dsem-alist api)))
        (t
         (apply-call-graph-ordering-to-defun-pairs
          (cdr ordering)
          pairs
          (cons (apply-renaming-alist-to-def
                 renaming-alist
                 (cadr (assoc-equal (car (car ordering)) pairs)))
                events)
          renaming-alist
          dsem-alist api))))

; (A.6) generate the correctness theorem relating the clock and semantic
;       functions

(defun generate-equal-key-evg-lst (key evg-lst)
  (cond ((endp evg-lst) nil)
        (t (cons `(EQUAL ,key ',(car evg-lst))
                 (generate-equal-key-evg-lst key (cdr evg-lst))))))

(defun pretty-or (lst)
  (cond ((null lst) nil)
        ((null (cdr lst)) (car lst))
        (t (cons 'or lst))))

(defun pretty-and (conjuncts)
  (cond ((null conjuncts) t)
        ((null (cdr conjuncts)) (car conjuncts))
        (t (cons 'and conjuncts))))

(defun generate-correctness-theorem (pc-lst dsem-alist api wrld)

; Pc-Lst is a list pcs and is an element of some call-graph ordering.  If
; pc-lst is a singleton list then the pc in it corresponds to a
; singly-recursive (or possibly non-recursive) function.  If it is not a
; singleton, then the pc-lst in it gave rise to mutually recursive definitions
; which have been transformed into a singly-recursive function with a name
; derived from all the pc-lst.  Both semantic and clock functions for the
; pc-lst have already been defined.  We generate a list of events thought
; suitable for proving that the corresponding functions are correct.  The list
; contains just two events: a defthm and a subsequent in-theory disabling the
; relevant clock.

  (let* ((run (access model-api api :run))
         (s (access model-api api :svar))
         (hyp (conjoin (access model-api api :hyps)))
         (get-pc (access model-api api :get-pc))
         (clk-fn (generate-def-semantics-name (fnsymbol-name-prefix :clock)
                                           pc-lst "" dsem-alist api))
         (sem-fn (generate-def-semantics-name (fnsymbol-name-prefix :semantic)
                                           pc-lst ""  dsem-alist api))
         (thm-name (generate-def-semantics-name (fnsymbol-name-prefix :semantic)
                                             pc-lst "-CORRECT"
                                             dsem-alist api))
         (user-supplied-pair
          (assoc-eq thm-name
                    (cdr (assoc-eq :annotations dsem-alist)))))
    `((defthm ,thm-name
        (implies
         ,(pretty-and
           (untranslate-lst
            (append
             (flatten-ands-in-lit hyp)
             `(,(pretty-or
                 (generate-equal-key-evg-lst (make-fn-application get-pc (list s))
                                             pc-lst))))
            nil
            wrld))
         (equal ,(make-fn-application
                  run
                  (list s (make-fn-application clk-fn (list s))))
                ,(make-fn-application
                  sem-fn
                  (list s))))
        ,@(cdr user-supplied-pair))
      (in-theory (disable ,clk-fn)))))

(defun generate-call-graph-ordered-correctness-theorems
  (ordering dsem-alist api wrld)
  (cond
   ((endp ordering) nil)
   (t (append (generate-correctness-theorem
               (car ordering)
               dsem-alist api wrld)
              (generate-call-graph-ordered-correctness-theorems
               (cdr ordering)
               dsem-alist api wrld)))))

; We now begin putting it all together.

(defun untranslate-defuns (lst wrld)
  (cond
   ((endp lst) nil)
   ((and (consp (car lst))
         (member-eq (car (car lst)) '(defun defun-nx defunm defunm-nx)))
    (cons (append
           (all-but-last (car lst))
           (list (untranslate (undistribute-ifs (car (last (car lst)))) nil wrld)))
          (untranslate-defuns (cdr lst) wrld)))
   (t (cons (car lst)
            (untranslate-defuns (cdr lst) wrld)))))

(defun def-semantics-pre-events (dsem-alist api)
  (let ((api+ (change model-api
                      api
                      :hyps (append (access model-api api :hyps)
                                    (cdr (assoc-eq :hyps+ dsem-alist))))))
    (wrapper-events api+)))

(defun def-semantics-post-events (dsem-alist api state)
  (let ((api+ (change model-api
                      api
                      :hyps (append (access model-api api :hyps)
                                    (cdr (assoc-eq :hyps+ dsem-alist))))))
    (mv-let
     (unknowns-alist flink-graph blink-graph)
     (link-graphs dsem-alist api+ state)
     (cond
      ((null unknowns-alist)
       (mv-let
        (loop-pcs branching-pcs halting-pcs cutpoint-pcs)
        (categorize-pcs flink-graph blink-graph)
        (declare (ignore loop-pcs branching-pcs))
        (let* ((svar (access model-api api+ :svar))
               (pc-term (make-fn-application (access model-api api+ :get-pc)
                                             (list svar)))
               (known-cutpoints

; To insure that the function for the :init-pc is the first one in the list, we
; make sure the :init-pc is the first cutpoint!

                (cons (cdr (assoc-eq :init-pc dsem-alist))
                      (remove1-equal (cdr (assoc-eq :init-pc dsem-alist))
                                     cutpoint-pcs))))
          (er-let*
            ((path-tree-tuples
              (path-tree-tuples-from-cutpoint-lst
               (set-difference-equal known-cutpoints halting-pcs)
               known-cutpoints
               halting-pcs
               api+ state)))
            (let* ((ordering
                    (call-graph-ordering (create-call-graph path-tree-tuples)))
                   (prelim-clock-function-defun-pairs
                    (generate-clock-function-defun-pairs
                     path-tree-tuples
                     halting-pcs
                     dsem-alist
                     api+))
                   (clock-disguised-constant-4-tuple-lst
                    (disguised-constant-4-tuple-lst
                     pc-term
                     (generate-fn-to-pc-and-vcalls-alist
                      prelim-clock-function-defun-pairs
                      (strip-cadrs ; list of all clock fn names
                       (strip-cars
                        (strip-cdrs prelim-clock-function-defun-pairs)))
                      (w state))))
                   (prelim-semantic-function-defun-pairs
                    (generate-semantic-function-defun-pairs
                     path-tree-tuples
                     halting-pcs
                     dsem-alist
                     api+))
                   (semantic-disguised-constant-4-tuple-lst
                    (disguised-constant-4-tuple-lst
                     pc-term
                     (generate-fn-to-pc-and-vcalls-alist
                      prelim-semantic-function-defun-pairs
                      (strip-cadrs ; list of all semantic fn names
                       (strip-cars
                        (strip-cdrs prelim-semantic-function-defun-pairs)))
                      (w state)))))
              (cond
               ((not (equal (strip-cdrs clock-disguised-constant-4-tuple-lst)
                            (strip-cdrs semantic-disguised-constant-4-tuple-lst)))
                (er soft 'def-semantics
                    "The disguised constants in the system of clock functions are ~
                 different from those in the system of semantic functions.  ~
                 Below we show two lists, one for clock functions and one for ~
                 semantic functions.  Except for the names of the functions, ~
                 the two lists are supposed to be identical but are not.  ~
                 Each element of each list is of the form (fn pc vformal ~
                 range) meaning that in function fn, derived from the given ~
                 pc, vformal is a disguised constant with the given range of ~
                 possible values.~%~%~X02~%~%~X12"
                    clock-disguised-constant-4-tuple-lst
                    semantic-disguised-constant-4-tuple-lst))
               (t
                (let* ((clock-function-defun-pairs
                        (modify-hyps-in-defun-pairs
                         clock-disguised-constant-4-tuple-lst
                         prelim-clock-function-defun-pairs))
                       (semantic-function-defun-pairs
                        (modify-hyps-in-defun-pairs
                         semantic-disguised-constant-4-tuple-lst
                         prelim-semantic-function-defun-pairs)))
                  (mv-let
                   (clk-defuns clk-renaming-alist)
                   (apply-call-graph-ordering-to-defun-pairs
                    ordering
                    clock-function-defun-pairs
                    nil nil
                    dsem-alist
                    api+)
                   (declare (ignore clk-renaming-alist))
                   (mv-let
                    (sem-defuns sem-renaming-alist)
                    (apply-call-graph-ordering-to-defun-pairs
                     ordering
                     semantic-function-defun-pairs
                     nil nil
                     dsem-alist
                     api+)
                    (declare (ignore sem-renaming-alist))
                    (let ((events
                           `(progn
                              (set-verify-guards-eagerness 0)
                              ,@(untranslate-defuns clk-defuns (w state))
                              ,@(untranslate-defuns sem-defuns (w state))
                              ,@(generate-call-graph-ordered-correctness-theorems
                                 ordering
                                 dsem-alist
                                 api+
                                 (w state)))))
                      (pprogn
                       (fms "~%~%~s0 Def-semantics Analysis ~s0~%We will attempt to admit ~
                 the following events.  If this fails, consider attaching ~
                 :annotations to your def-semantics to provide adequate ~
                 guidance.  In the worst case, you could grab these events ~
                 and edit them as appropriate to lead ACL2 to admit ~
                 them.~%~%~x1~s0-~s0~s0~%"
                            (list (cons #\0 "--------------------")
                                  (cons #\1 events))
                            (standard-co state)
                            state
                            nil)
                       (value events)))))))))))))
      (t (er soft 'def-semantics
             "This code cannot be explored with the current rewrite-rule ~
              configuration.  Below is an alist pairing pcs to lists of ~
              terms, as in (pc . (term1 term2 ...)).  The termi are the ~
              possible, non-constant next pc values obtained by executing the ~
              instruction at pc.  Since their concrete values cannot be ~
              determined, we cannot trace the control structure of the code.  ~
              There are two possible explanations.  One is that the ~
              instruction at pc is some kind of computed jump that transfers ~
              control to a context- or data-sensitive location or to a ~
              location outside the bounds of the current program.  The other ~
              is that the rewrite rules available in this world are ~
              insufficient to allow us to resolve the symbolic terms to ~
              concrete values.~%~X01"
             unknowns-alist
             nil))))))

; If you set this variable, make-event will print some extra output showing you what is
; being evaluated and what events are produced.

; (assign make-event-debug t)

(defun correctness-theorem-namep (sym)
; We return t iff the name of symbol sym ends in -CORRECT.
  (let* ((str (symbol-name sym))
         (n (length str)))
    (cond
     ((< n 8) nil)
     (t (and (eql (char str (- n 8)) #\-)
             (eql (char str (- n 7)) #\C)
             (eql (char str (- n 6)) #\O)
             (eql (char str (- n 5)) #\R)
             (eql (char str (- n 4)) #\R)
             (eql (char str (- n 3)) #\E)
             (eql (char str (- n 2)) #\C)
             (eql (char str (- n 1)) #\T))))))

; Now we develop the code to translate the arguments of def-semantics.

(defun cheap-declare-formsp (lst)
  (cond ((atom lst) (eq lst nil))
        ((and (true-listp (car lst))
              (eq (car (car lst)) 'DECLARE))
         (cheap-declare-formsp (cdr lst)))
        (t nil)))

(defun chk-def-semantics-annotations (x state)
  (cond
   ((atom x)
    (cond ((equal x nil) (value nil))
          (t (er soft 'def-semantics
                 "The :ANNOTATIONS argument of a def-semantics expression is ~
                  supposed be a true list and yours is not, it ends in ~x0."
                 x))))
   ((and (consp (car x))
         (true-listp (car x))
         (symbolp (car (car x))))
    (cond
     ((correctness-theorem-namep (car (car x)))
      (cond
       ((member-eq (cadr (car x))
                   '(:RULE-CLASSES :HINTS :INSTRUCTIONS :OTF-FLG :DOC))
        (chk-def-semantics-annotations (cdr x) state))
       (t (er soft 'def-semantics
              "When a def-semantics annotation begins with a name like ~x0, the ~
               associated entry must list the keyword arguments for the ~
               DEFTHM event of that name that def-semantics will generate.  ~
               Thus, we expect to see one of the DEFTHM keyword arguments ~
               after the name, e.g., :RULE-CLASSES, :HINTS, :INSTRUCTIONS, ~
               :OTF-FLG, or :DOC.  But you wrote ~x1."
              (car (car x))

              (car x)))))
     ((and (consp (cdr (car x)))
           (cheap-declare-formsp (cdr (car x))))
      (chk-def-semantics-annotations (cdr x) state))
     ((and (consp (cdr (car x)))
           (keyword-value-listp (cdr (car x)))
           (subsetp-equal (evens (cdr (car x)))
                          *xargs-keywords*))
      (chk-def-semantics-annotations (cdr x) state))
     (t (er soft 'def-semantics
            "When a def-semantics annotation begins with a name like ~x0, the ~
             associated entry must either be a list of DECLARE forms for the ~
             named clock or semantic function def-semantics will try to ~
             introduce or else must be a keyword/value list as provided to in ~
             XARGS.  The former means that you wish to take over the ~
             admission of the ~x0 after def-semantics has generated the body; ~
             the latter means you wish to provide some additional hints ~
             during def-semantics' attempt to find a suitable measure.  But the ~
             pair you supplied, ~x1, matches neither form."
            (car (car x))
            (car x)))))
   (t (er soft 'def-semantics
          "Every def-semantics annotation should be of the form ~
           (<symbol> ...), i.e., should be true-list starting with a symbol,
           but you wrote the annotation ~x0"
          (car x)))))

(defun maybe-tack-hyphen-at-end (str)
  (cond
   ((equal str "") "")
   ((eql (char str (- (length str) 1)) #\-)
    str)
   (t (string-append str "-"))))

(defun translate-def-semantics-args (alist api state)

; This function takes an alist that contains pairs of the form (:key . val) and
; returns an equivalent alist containing (:key . val'), where the :keys are the
; keyword args to the def-semantics macro, val is the user supplied values, and
; val' is the translated form.  If some argument fails to translate, an error
; is signaled.  We will pass the resulting alist around as the
; ``dsem-alist.''

  (let ((root-name (cdr (assoc-eq :root-name alist)))
        (focus-regionp (cdr (assoc-eq :focus-regionp alist)))
        (init-pc (cdr (assoc-eq :init-pc alist)))
        (hyps+ (cdr (assoc-eq :hyps+ alist)))
        (annotations (cdr (assoc-eq :annotations alist)))
        (svar (access model-api api :svar)))
    (er-let*
      ((root-name
; Root-name is always translated to either the empty string or
; a string ending with hyphen.
        (cond
         ((null root-name) (value ""))
         ((symbolp root-name)
          (value (maybe-tack-hyphen-at-end (symbol-name root-name))))
         ((stringp root-name)
          (value (maybe-tack-hyphen-at-end root-name)))
         (t (er soft 'def-semantics
                "The :ROOT-NAME, when supplied, must be a symbol or string ~
                 and ~x0 is not!"
                root-name))))
       (focus-regionp
        (cond
         ((or (eq focus-regionp t)
              (eq focus-regionp nil))
          (value '(lambda (pc) 't)))
         (t (translate-fn-field
             :focus-regionp
             'def-semantics
             focus-regionp
             1 svar -1
             state))))
       (hyps+
        (er-progn
         (chk-true-listp hyps+
                         'def-semantics
                         "The :HYPS+ argument"
                         state)
         (translate-list-of-terms hyps+ state))))
      (let ((val
             (focus-regionp-approvesp
              'def-semantics
              focus-regionp
              init-pc
              state)))
        (cond
         ((not val)
          (er soft 'def-semantics
              "The initial pc, ~x0, falls outside the focus region."
              init-pc))
         (t
          (er-progn
           (chk-def-semantics-annotations annotations state)
; Here are the full-translated def-semantics arguments in alist form, aka
; ``dsem-alist.''
           (value
            `((:root-name . ,root-name)
              (:focus-regionp . ,focus-regionp)
              (:init-pc . ,init-pc)
              (:hyps+ . ,hyps+)
              (:annotations . ,annotations))))))))))

; See Guide:  Overview of How Def-semantics Works

(defmacro def-semantics (&key init-pc focus-regionp root-name hyps+ annotations)

; Matt Kaufmann taught us how to do this.  We find it very hard to think about
; make-event!  Thanks Matt!

  `(make-event
    (er-let*
      ((dsem-alist
        (translate-def-semantics-args
         '((:init-pc . ,init-pc)
           (:focus-regionp . ,focus-regionp)
           (:root-name . ,root-name)
           (:hyps+ . ,hyps+)
           (:annotations . ,annotations))
         (cdr (assoc-eq :record (table-alist 'model-api (w state))))
         state)))
      (value
       (list
        'make-event
        (cons 'er-progn
              (append
               (def-semantics-pre-events
                 dsem-alist
                 (cdr (assoc-eq :record (table-alist 'model-api (w state)))))
               `((def-semantics-post-events ',dsem-alist
                   (cdr (assoc-eq :record (table-alist 'model-api (w state))))
                   state)))))))))

; Now we move on to the development of projections.

; See Guide.
; (B.1) given a projector term (specifying the state component of interest) and a
;       semantic function, create the term (projector (semantic st)), expand
;       the semantic function call and simplify

(defun apply-projector-to-term (hyps proj-term svar term state)

; To apply a projector to a term we merely substitute the term for svar in the
; projection term and simplify it under the hyps.  Then we strip out the part
; of the result governed by hyps.  We return a simplified term.

  (simplify-under-hyps hyps
                       (subst-var term svar proj-term)
                       state))


; (B.2) find every state component referenced outside the projected recursive
;       calls and collect the state component and its type; these are the
;       initially relevant components

; Recall from Appendix A our discussion of the three sources of constraints on
; a new formal parameter introduced into projections by generalizing a state
; component: (a) tests on the state component made by the semantic function
; being projected, (b) tests on the state component derived from the API's
; :hyps, and (c) the type test associated with the state component in
; state-comps-and-types.  We refer to these ``sources'' in our comments below.

(defun state-componentp (term svar state-comps-and-types)

; A term is a state component iff it is an instance of the comp part of one of
; the state-comps-and-types doublets, (comp type), such that the
; variable svar is bound to itself and any other variables in comp are bound to
; quoted constants.  If term is a state component wrt svar then we return the
; type of that component, as given by the instance of the type part of the
; doublet.

  (cond
   ((endp state-comps-and-types) nil)
   (t (mv-let
       (flg alist)
       (one-way-unify1 (car (car state-comps-and-types))
                       term
                       (list (cons svar svar)))
       (cond
        ((and flg
              (all-quoteps (remove1-eq svar (strip-cdrs alist))))
         (sublis-var alist (cadr (car state-comps-and-types))))
        (t (state-componentp term svar (cdr state-comps-and-types))))))))

(defun every-term-with-svar-matches-some-pattern (term-lst svar patterns)
  (cond
   ((endp term-lst) t)
   ((not (occur svar (car term-lst)))
    (every-term-with-svar-matches-some-pattern (cdr term-lst)
                                               svar patterns))
   (t (mv-let
       (flg alist i)
       (member-instance (car term-lst) 0 patterns nil)
       (declare (ignore alist i))
       (and flg
            (every-term-with-svar-matches-some-pattern (cdr term-lst)
                                                       svar patterns))))))

(defun other-semantic-fn-callp (term sem-fn svar state-expression-patterns)

; We return t if term is of the form (some-other-semantic-fn a1 ... ak) where
; some-other-semantic-fn is not sem-fn, svar occurs in at least one ai, and
; every ai in which svar occurs is a ``next-state expression,'' where by that
; we mean matches one of the patterns in state-expression-patterns.  Those
; patterns are typically just the updater and constructor pseudo-terms from the
; generalized-updater-drivers or constructor-drivers.

  (and (not (variablep term))
       (not (fquotep term))
       (symbolp (ffn-symb term))
       (not (eq (ffn-symb term) sem-fn))
       (occur svar term)
       (every-term-with-svar-matches-some-pattern
        (fargs term) svar state-expression-patterns)))

(defun projector-and-other-fnsymb (term sem-fn svar
                                        state-component-patterns-and-types
                                        state-expression-patterns)

; We determine whether term is a ``projected other call'' (a projection of a
; call of a semantic function other than the one we're trying to project).  If
; so we return (mv projector fn), where projector is the projector from
; state-component-patterns-and-types (a list of (comp type) doublets)
; instantiated with the appropriate constants and fn is some semantic function
; other than sem-fn.  State-expression-patterns is used to determine if the
; arguments to the fn call look like state expressions; the elements of this
; list are typically the updater patterns and constructor patterns from
; generalized-updater-drivers and constructor-drivers.

  (cond
   ((endp state-component-patterns-and-types)
    (mv nil nil))
   (t (mv-let
       (flg alist)
       (one-way-unify (car (car state-component-patterns-and-types))
                      term)
       (cond
        ((and flg
              (all-quoteps
               (strip-cdrs (remove1-equal (assoc-eq svar alist) alist)))
              (other-semantic-fn-callp
               (cdr (assoc-eq svar alist))
               sem-fn
               svar
               state-expression-patterns))
         (mv (sublis-var (remove1-equal (assoc-eq svar alist) alist)
                         (car (car state-component-patterns-and-types)))
             (ffn-symb (cdr (assoc-eq svar alist)))))
        (t (projector-and-other-fnsymb term sem-fn svar
                                       (cdr state-component-patterns-and-types)
                                       state-expression-patterns)))))))

(mutual-recursion
(defun all-projector-and-other-fnsymb (term sem-fn svar
                                            state-component-patterns-and-types
                                            state-expression-patterns)

; We sweep term and collect (projector . some-other-semantic-fn) for every
; subterm classified as a projected other call.  See projector-and-other-fnsymb
; for the details of each pair collected.

  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   (t (mv-let (projector other-fn)
              (projector-and-other-fnsymb term sem-fn svar
                                          state-component-patterns-and-types
                                          state-expression-patterns)
              (cond
               ((null projector)
                (all-projector-and-other-fnsymb-lst
                 (fargs term) sem-fn svar
                 state-component-patterns-and-types
                 state-expression-patterns))
               (t (list (cons projector other-fn))))))))

(defun all-projector-and-other-fnsymb-lst
  (term-lst sem-fn svar
            state-component-patterns-and-types
            state-expression-patterns)
  (cond
   ((endp term-lst) nil)
   (t (union-equal
       (all-projector-and-other-fnsymb (car term-lst) sem-fn svar
                                       state-component-patterns-and-types
                                       state-expression-patterns)
       (all-projector-and-other-fnsymb-lst (cdr term-lst) sem-fn svar
                                           state-component-patterns-and-types
                                           state-expression-patterns))))))
(mutual-recursion

(defun find-all-state-components-and-types-outside
  (term sem-fn svar state-comps-and-types)

; Collect all state components outside the projected recursive calls of sem-fn
; and return a list of doublets, (comp' type') which are the state components,
; comp', and their respective types, type'.

  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((eq (ffn-symb term) sem-fn) nil)
   (t (let ((type
             (state-componentp term svar state-comps-and-types)))
        (cond
         (type (list (list term type)))
         (t (find-all-state-components-and-types-outside-lst
             (fargs term) sem-fn svar state-comps-and-types)))))))

(defun find-all-state-components-and-types-outside-lst
  (terms sem-fn svar state-comps-and-types)
  (cond
   ((endp terms) nil)
   (t (union-equal
       (find-all-state-components-and-types-outside
        (car terms) sem-fn svar state-comps-and-types)
       (find-all-state-components-and-types-outside-lst
        (cdr terms) sem-fn svar state-comps-and-types))))))


; See Guide.
; (B.3) replace all projected recursive calls of the semantic function by
;       unquoted naturals and build an alist mapping those naturals to the new
;       states inside those calls

(mutual-recursion

(defun enumerated-projected-body (term proj-term svar sem-fn alist)

; We copy term, replacing projected recursive calls of sem-fn by integers (not
; quoted evgs!) and build an alist pairing those integers with the next states
; found within the ``projected recursive calls.''  The projected recursive
; calls are calls of sem-fn surrounded by the projector, e.g., (NTH '1 (LOCALS
; (sem-fn svar'))).  We return (mv term' alist').

; For example, given the term

; (IF tst1
;     (IF tst2
;         (NTH '1 (LOCALS (sem-fn svar')))
;         (NTH '1 (LOCALS (sem-fn svar''))))
;     svar)

; where the projector term is (NTH '1 (LOCALS svar)) and the svar' and svar''
; are the next states, then we'd return:

; (mv '(IF tst1
;          (IF tst2
;              0
;              1)
;          svar)
;     '((1 . svar'') (0 . svar')))

; Note that if the returned alist is nil there are NO calls of sem-fn term.
; This could happen in several ways but we suspect the two most common are
; because the code concerned is straight-line or because the code enters an
; already analyzed loop after some preamble.  By the way, it is possible for
; term (and hence the returned term') to be constant: e.g., the code enters an
; already-analyzed loop on known values and the simplifier just computes it
; out.

  (cond ((variablep term) (mv term alist))
        ((fquotep term) (mv term alist))
        (t (mv-let
            (flg subst)
            (one-way-unify proj-term term)
            (let ((sem-fn-call (and flg (cdr (assoc svar subst)))))
              (cond
               ((and sem-fn-call
                     (not (variablep sem-fn-call))
                     (not (fquotep sem-fn-call))
                     (eq (ffn-symb sem-fn-call) sem-fn))
                (let ((next-state (fargn sem-fn-call 1)))
                  (mv (len alist)
                      (cons (cons (len alist) next-state)
                            alist))))
               (t (mv-let
                   (enumerated-args new-alist)
                   (enumerated-projected-body-lst (fargs term) proj-term svar sem-fn alist)
                   (mv (fcons-term (ffn-symb term) enumerated-args)
                       new-alist)))))))))

(defun enumerated-projected-body-lst (terms proj-term svar sem-fn alist)
  (cond ((endp terms)
         (mv nil alist))
        (t (mv-let
            (enumerated-arg alist)
            (enumerated-projected-body (car terms) proj-term svar sem-fn alist)
            (mv-let
             (enumerated-args alist)
             (enumerated-projected-body-lst (cdr terms) proj-term svar sem-fn alist)
             (mv (cons enumerated-arg enumerated-args) alist)))))))

; See Guide.
; (B.4) for each site, determine the new value of each of the relevant state
;       components in the new state at that site; close the set of relevant
;       components by iteration

(defun actual-expressions-by-call (hyps component svar call-number-to-next-state-alist state)
  (cond
   ((endp call-number-to-next-state-alist) nil)
   (t (cons (cons (caar call-number-to-next-state-alist)
                  (apply-projector-to-term hyps component svar
                                            (cdar call-number-to-next-state-alist)
                                            state))
            (actual-expressions-by-call hyps component svar
                                        (cdr call-number-to-next-state-alist)
                                        state)))))

(defun components-and-types-to-actual-expressions-by-call
  (hyps components-and-types svar call-number-to-next-state-alist state)

; We map over the so-far-identified-as-relevant state components (in doublets
; with their respective types) and make an alist where the keys are the
; individual (component type) doublets and the values are alists that map call
; numbers to the actual expression for the given component in that call.

; (((component1 type1) . ((0 . actual-expr0)
;                         (1 . actual-expr1)
;                         ...))
;  ((component2 type2) . ...)
;  ...)

; For example, if component1 is (nth '7 (locals s)) and in some recursive call,
; say call 1, that component is changed to (+ (nth '7 (locals s)) (nth '8
; (locals s))), then actual-expr1 above would be (+ (nth '7 (locals s)) (nth '8
; (locals s))), e.g., in call 1 the new state is
; (make-state ...
;   (update-nth '7 (+ (nth '7 (locals s)) (nth '8 (locals s))) (locals s))
;   ...).

  (cond ((endp components-and-types) nil)
        (t (cons (cons (car components-and-types)
                       (actual-expressions-by-call hyps (car (car components-and-types))
                                                   svar
                                                   call-number-to-next-state-alist
                                                   state))
                 (components-and-types-to-actual-expressions-by-call
                  hyps
                  (cdr components-and-types)
                  svar call-number-to-next-state-alist state)))))

(defun collect-new-components-and-types
  (sem-fn svar alist seen state-comps-and-types)

; The alist argument maps component expressions and type doublets, (componenti
; typei), to alists mapping call numbers, j, to the new values, actual-exprj,
; of the component in each call,

; (((component1 type1) . ((0 . actual-expr0)
;                         (1 . actual-expr1)
;                         ...))
;  ((component2 type2) . ...)
;  ...)

; See the comment in components-and-types-to-actual-expressions-by-call for an
; illustration of ``actual expressions''.

; The seen argument lists all so-far identified (component type) doublets.

; We identify all the state components mentioned in any actual expression of
; alist and return the list of those not occurring in seen, each in a doublet
; with its type, (comp' type').

  (cond
   ((endp alist)
    nil)
   (t (union-equal
       (set-difference-equal
        (find-all-state-components-and-types-outside-lst
         (strip-cdrs (cdr (car alist)))
         sem-fn
         svar
         state-comps-and-types)
        seen)
       (collect-new-components-and-types
        sem-fn svar (cdr alist) seen state-comps-and-types)))))

(defun components-and-types-to-actual-expressions-by-call*
  (hyps new-components-and-types sem-fn svar call-number-to-next-state-alist ans-alist
        state-comps-and-types
        state)
  (let* ((new-ans-alist
          (components-and-types-to-actual-expressions-by-call
           hyps new-components-and-types svar
           call-number-to-next-state-alist state))
         (ans-alist (append ans-alist new-ans-alist))
         (new-components-and-types
          (collect-new-components-and-types
           sem-fn svar new-ans-alist
           (strip-cars ans-alist)
           state-comps-and-types)))
    (cond
     ((null new-components-and-types) ans-alist)
     (t (components-and-types-to-actual-expressions-by-call*
         hyps new-components-and-types sem-fn svar
         call-number-to-next-state-alist ans-alist
         state-comps-and-types
         state)))))

; See Guide.
; (B.5) introduce calls of the new function at each site, generalizing the
;       relevant state components and their occurrences in the actuals

; First we deal with generating variable names for vformals.

; Essay on :var-names -- Two Ways for the User to Control the Generation of
; Variable Names

; We now develop the code to generate variable names for vformals.  We want the
; user to have some convenient control over the names generated.  For example,
; the vformal (IPC S) might generalize to the variable PC while the vformal
; (NTH 7 (REGS S)) might generalize to R7 or perhaps R07.

; All of the variable names generated will be in the symbol package of the svar
; of the API.  Furthermore, all of the names must be unique -- which is hard
; for the user to guarantee while generating one name at a time and so will be
; guaranteed by the system suffixing each name with an index as necessary.
; Finally, we offer no assurance that any name will actually be a legal ACL2
; variable name except by watching the generated DEFUN fail when we try to
; admit it with an illegal formal parameter name.

; So the issue boils down to how can the user suggest the STRING to be used as
; the initial (or ``root'') symbol-name of the variable generated for a given
; term?

; We actually implement two ways to provide such control: a relatively simple
; way to have some limited control and very general powerful way.  The powerful
; is for the user to specify a function that maps from terms to fmt msgs (or
; simply to a string).rg  (Note that a fmt msg m corresponds to the string
; printed by ~@m).  This function is stored in the :var-names slot of the
; API.

; But writing functions on terms is hard for some users so we provide a
; simpler, more limited, way to suggest strings.  The simple way is implemented
; in terms of the powerful way.  Instead of providing a function for
; :var-names, the user can provide def-model-api with an alist that
; associates terms (patterns) with msgs (actually, with the terms that when
; evaluated will produce the msgs).  When def-model-api detects that an alist
; has been provided where a function was expected, it translates the alist into
; a suitable lambda expression and stores that as :var-names.

; This allows the simple way to generate names that involve constants mentioned
; in the term, e.g., to map the term (NTH 123 (MEM S)) into "M123" and even to
; transform those constants with simple calculations.  For example, since 123 =
; 15*8 + 3, one might wish for (NTH 123 (MEM S)) to be named WORD-15-BYTE-3.
; The latter would be achieved by including this tuple in the alist:

; ((NTH I (MEM S)) "WORD-~x0-BYTE-~x1" (floor I 8) (mod i 8))

; So from the implementation perspective, there is only the powerful way: one
; way or another the user specifies a :var-names function to def-model-api
; and that function maps terms to msgs.  But most users will probably employ
; the simple way and not realize they're using the powerful way under the hood.

; Note that to match (NTH '123 (MEM S)) with the (NTH I (MEM S)) term above and
; generate a msg from the rest of the tuple the system must use one-way-unify
; to do the pattern matching -- insisting that the svar be bound to itself and
; all other variables be bound to constants, then it must strip out the quotes
; from around the evgs in the unifying substition -- the variable I will be
; bound to (QUOTE 123) in that substitution, and translate and evaluate the
; remaining terms, (floor I 8) and (mod I 8) under that alist binding variables
; to evgs.  If we didn't provide this feature of converting an alist to a
; :var-names, the user would have to use many of these same relatively
; sophisticated ACL2 primitives inside each user-defined :var-names.

; So a typical entry in the alist is (term fmt-string . term-lst).  Such
; entries are called ``var name rules'' (or vnrule'').

; We say a term ``triggers'' a vnrule (wrt to a given svar name) if the pattern
; of the vnrule one-way-unifies with the term under two restrictions: (a) svar
; is bound to itself in the unifying substitution and (b) every other variable
; in the pattern is bound to a quoted constant.

; Ideally, searching a list of vnrules for the first one that is triggered by a
; given term would produce a msg.  That msg would be obtained by evaluating the
; term-lst of the vnrule under an alist mapping variables to the evgs to which
; they were bound by one-way-unify.  But we want the function that does this
; search to be the workhorse in the translation of an alist to a :var-names
; lambda expression and that lambda expression cannot (or, at least, does not)
; take STATE.  So we secretly allow :var-names to return not just a msg
; (which is a cons with a stringp car) but a ``meta-msg'' which is

; ((fmt-string . term-lst) . evg-alist)

; and if it returns a meta-msg we evaluate the terms in term-lst under the
; evg-alist and we then create the message, as with (msg fmt-string . values).

; The evaluation of a user-defined :var-namess can just create the intended
; msg directly.  So we do not expect user-defined :var-namess to traffic in
; meta-msgs although if one did it would work perfectly well.

; Before proceeding, we exhibit an example.  Let's imagine that the svar state
; contains two fields, a pc and a memory and that the memory is accessed with
; nth.  So there are two shapes of state components, (PC S) and (NTH ma (MEM
; S)), where ma is some (quoted) constant.  Let's suppose we want (PC S) to
; generalize to PC and we want something like (NTH '7 (MEM S)) to generalize to
; M7.

; The user could define the following

; (defun MY-VAR-NAMES (term)
;   (case-match term
;     (('PC 'S) "PC")
;     (('NTH ('QUOTE ma) '(MEM S))
;      (msg "M~x0" ma))
;     (& "X")))

; and then

; (def-model-api ...
;   :var-names MY-VAR-NAMES
;   ...)

; Alternatively, the user could write:

; (def-model-api ...
;   :var-names (((PC S) "PC")
;               ((NTH MA (MEM S)) "M~x0" MA))
;   ...)

; This would translate into:

; (def-model-api ...
;    :var-names (lambda (term)
;                   (trigger-var-name-rule term
;                                          ',svar
;                                          '(((PC S) "PC")
;                                            ((NTH MA (MEM S)) "M~x0" MA))))
;    ...)

; where trigger-var-name-rule is a function defined below that searches
; the alist for the first pattern that unifies with term and returns
; a meta-msg.  For the term (NTH '7 (MEM S)) it would return
; (("M~x0" MA) . ((MA . 7))).  It can't produce the msg we want because
; it doesn't have STATE.  But we can produce the msg from that meta-msg
; by evaluating MA under ((MA . 7)) and binding the #\0 to the value.

; By using evaluation we can allow the alist to use any function that
; simple-translate-and-eval can handle, e.g., we allow the alist:

;   :var-names (((PC S) "PC")
;                ((NTH MA (MEM S)) "WORD-~x0-BYTE-~x1"
;                                  (floor MA 8)
;                                  (mod MA 8)))

; Because of the flexibility of fmt, we can actually do quite a lot with these
; tables.  For example, suppose that the first 16 memory locations were to be
; named R00, R01, ..., R15, and then locations above 15 were named M16, M17,
; etc.  Here is a table entry that would do that:

; ((NTH MA (MEM S))
;  "~#0~[R0~x1~/R~x1~/M~x1~]"
;  (if (< ma 10) 0 (if (< ma 16) 1 2))
;  ma)

; Of course, at some point it is probably easier for the user to define a
; special-purpose var-names than to mess around with tilde-directives.

(defun trigger-var-name-rule (term svar vnrules)

; We find the first vnrule in vnrules that is triggered by term and return the
; resulting meta-msg or nil if there is no triggered vnrule.

; If the user provides list a of vnrules in place of the :var-names in the
; def-model-api, then at translate time we set the :var-names to

; `(lambda (term)
;    (trigger-var-name-rule term ',svar ',vnrules)).

  (cond
   ((endp vnrules)
    nil)
   (t (let ((pattern (car (car vnrules)))
            (fmt-string-and-term-lst (cdr (car vnrules))))
        (cond
         ((eq pattern :otherwise)
; Term-lst is empty when pattern is :otherwise.
          fmt-string-and-term-lst)
         (t (mv-let (flg subst-alist)
                    (one-way-unify1 pattern term
                                    (list (cons svar svar)))
                    (cond
                     (flg
                      (let* ((const-subst (all-but-last subst-alist))
                             (values (strip-cdrs const-subst)))

; Note:  We know the binding of svar is the last element of subst-alist.
; So const-subst is the subst-alist except for the binding of svar.

                        (cond
                         ((all-quoteps values) ; all vars (except svar) are
                          (let ((evg-alist     ; bound to quotes
                                 (pairlis$ (strip-cars const-subst)
                                           (strip-cadrs values))))
                            (cons fmt-string-and-term-lst ; meta-msg
                                  evg-alist)))
                         (t (trigger-var-name-rule term svar (cdr vnrules))))))
                     (t (trigger-var-name-rule term svar (cdr vnrules)))))))))))

(defun simple-translate-and-eval-term-lst
  (term-lst evg-alist ok-stobjs-names msg ctx wrld state aok)

; Unlike its namesake, this function just returns the list of the values of the
; elements of term-lst under evg-alist, not the list of translations and value
; pairs.  We cause an error if any ``term'' in term-lst fails to translate or
; causes an error in evaluation.  Msg must be a cons of the form (string
; . char-alist), where #\x is not bound in char-alist.

  (cond ((endp term-lst)
         (value nil))
        (t (er-let*
             ((pair (simple-translate-and-eval
                     (car term-lst)
                     evg-alist
                     ok-stobjs-names
                     (cons (car msg)
                           (cons (cons #\x (car term-lst))
                                 (cdr msg)))
                     ctx wrld state aok))
              (rest (simple-translate-and-eval-term-lst
                     (cdr term-lst)
                     evg-alist
                     ok-stobjs-names
                     msg
                     ctx wrld state aok)))
             (value (cons (cdr pair) rest))))))

(defun generalized-meta-msg-to-string (term gmm state)

; Term is only used for error reporting.  We convert generalized meta-msg, gmm,
; to a string.  First we must consider what sort of object gmm is.  The common
; case is that it is a meta-msg produced by a user-supplied vnrules alist for
; :var-names.  In that case gmm is of the form ((fmt-string . term-lst)
; . evg-alist) and we fmt-to-string the fmt-string under the alist obtained by
; evaluating the term-lst under evg-alist and binding the resulting vars to
; successive character objects from #\0, ..., #\9.  (We do not bother to
; convert a meta-msg to a msg but go directly to the string.)  The other
; interesting case is that gmm is a msg (determined by being a cons with
; stringp car).  The pathological cases are that gmm is nil, a string, a
; symbol, or anything else.

  (cond
   ((consp gmm)
    (cond ((consp (car gmm))
           (let ((fmt-string (car (car gmm)))
                 (term-lst (cdr (car gmm)))
                 (evg-alist (cdr gmm)))
             (er-let* ((args (simple-translate-and-eval-term-lst
                              term-lst
                              evg-alist
                              nil ; ok-stobjs-names -- none
; Note that the msg below cannot be printed until #\x is bound, which happens
; in simple-translate-and-eval-term-lst, where #\x is bound to each successive
; term being eval'd.
                              (msg "The expression ~xx, which must be ~
                                    evaluated to generate a binding for the ~
                                    fmt string ~x0, triggered by the state ~
                                    component term ~x1,"
                                   fmt-string
                                   term)
                              'def-projection
                              (w state)
                              state
                              t)))
               (value
                (mv-let (col str)
                        (fmt1-to-string fmt-string
                                        (pairlis2
                                         '(#\0 #\1 #\2 #\3 #\4
                                           #\5 #\6 #\7 #\8 #\9)
                                         args)
                                        0
                                        :fmt-control-alist
                                        (list (cons 'current-package
                                                    (current-package state))))
                        (declare (ignore col))
                        str)))))
          (t ; gmm is a msg
           (value
            (mv-let (col str)
                    (fmt1-to-string (car gmm) (cdr gmm) 0
                                    :fmt-control-alist
                                    (list (cons 'current-package
                                                (current-package state))))
                    (declare (ignore col))
                    str)))))
   ((stringp gmm) (value gmm))
   ((and gmm (symbolp gmm)) (value (symbol-name gmm)))
   (t (value "NO-VAR-NAME-STRING"))))


(defun vformal-to-variable-name-string (var-names term state)

; var-names, as provided for in the API, is a function that takes a term and
; returns a generalized meta-msg.  We apply var-names to term to get a
; generalized meta-msg and then convert the meta-msg to a string to use as the
; root of the variable name for term.

  (er-let*
    ((pair (simple-translate-and-eval
            (list var-names (list 'quote term))
            nil ; alist -- but there are no vars above
            nil ; ok-stobjs-names -- none
            (msg "The expression ~x0, which must be evaluated to generate a ~
                  variable name for the quoted term,"
                 (list var-names (list 'quote term)))
            'def-projection
            (w state)
            state
            t)))
    (generalized-meta-msg-to-string term (cdr pair) state)))

(defun ensure-uniqueness-of-variable-name (root-str var i avoid-lst api)
  (cond
   ((member-eq var avoid-lst)
    (mv-let (col str)
            (fmt1-to-string "~s0-~x1"
                            (list (cons #\0 root-str)
                                  (cons #\1 i))
                            0
                            :fmt-control-alist
                            (list (cons 'current-package
                                        (access model-api api :package-witness))))
            (declare (ignore col))
            (ensure-uniqueness-of-variable-name
             root-str
             (intern-in-package-of-symbol
              str
              (access model-api api :package-witness))
             (+ 1 i)
             avoid-lst
             api)))
   (t var)))

(defun simple-generate-variable-lst (var-names terms avoid-lst api state)

; We generate a distinct variable for each term in terms, all in the package of
; svar and none of which occur in avoid-lst.  We return the list of those
; variables.  Note: there is no guarantee the results are legal variable names!
; That depends on how var-names is defined.  If it returned "*FOO*" the
; result will not be a legal variable.

  (cond
   ((endp terms) (value nil))
   (t (er-let*
        ((root-str
          (vformal-to-variable-name-string var-names (car terms) state))
         (var
          (value
           (ensure-uniqueness-of-variable-name
            root-str
            (intern-in-package-of-symbol
             root-str
             (access model-api api :package-witness))
            1
            avoid-lst
            api)))
         (rest
          (simple-generate-variable-lst var-names
                                        (cdr terms)
                                        (cons var avoid-lst)
                                        api
                                        state)))
        (value (cons var rest))))))

(defun get-actuals-for-call-no (k alist)

; Alist maps successive relevant state components to alists that map call
; numbers actual expressions for the given state component.  Given a call
; number k, we construct the list of successive actual expressions.  E.g., if k
; = 2 and alist:

;(((comp1 type1) . ((0 . new-comp1_0) (1 . new-comp1_1) (2 . new-comp1_2)))
; ((comp2 type2) . ((0 . new-comp2_0) (1 . new-comp2_1) (2 . new-comp2_2)))
; ((comp3 type3) . ((0 . new-comp3_0) (1 . new-comp3_1) (2 . new-comp3_2))))

; we return (new-comp1_2 new-comp2_2 new-comp3_2).  Thus, if you cons fn onto
; this and generalize away comp1, comp2, and comp3 to the corresponding new
; formal variables you get the kth call of fn.

  (cond ((endp alist) nil)
        (t (cons (cdr (assoc-equal k (cdr (car alist))))
                 (get-actuals-for-call-no k (cdr alist))))))

(defun make-fn-call-for-call-no (fn k alist generalizing-alist)

; We create the kth call of fn, expressed in terms of the new variables.

  (cons fn
        (sublis-expr-lst generalizing-alist
                         (get-actuals-for-call-no k alist))))

; Suppose term is an enumerated body, i.e., result of simplifying the
; application of the projector function to the body of the semantic function
; with the `recursive calls' replaced by successive integers.  Suppose fn is
; the name of the new fn, alist maps successive state components and types to
; alists mapping call numbers to new values of the component, and
; generalizing-alist is an expr-to-var alist generalizing the state components.
; Then we copy term, generalizing all the state components and replacing the
; call numbers by appropriate calls.

; Note: we do not handle the type restrictions on the components/new variables
; here.  Recalling the comment above in the Essay On Identifying State
; Components, restrictions on the new variables are of three kinds (a) tests
; made by the code, (b) tests derived from the invariant hyps, and (c)
; intrinsic types of components.  Term (and hence the result produced below)
; contain only the tests from (a).

(mutual-recursion

(defun re-introduce-recursions-and-generalize

; See comment above.

  (fn alist generalizing-alist term)
  (cond ((integerp term)
         (make-fn-call-for-call-no fn term alist generalizing-alist))
        ((assoc-equal term generalizing-alist)
         (cdr (assoc-equal term generalizing-alist)))
        ((variablep term) term)
        ((fquotep term) term)
        (t (cons (ffn-symb term)
                 (re-introduce-recursions-and-generalize-lst
                  fn alist generalizing-alist (fargs term))))))

(defun re-introduce-recursions-and-generalize-lst
  (fn alist generalizing-alist term-lst)
  (cond
   ((endp term-lst) nil)
   (t (cons
       (re-introduce-recursions-and-generalize
        fn alist generalizing-alist (car term-lst))
       (re-introduce-recursions-and-generalize-lst
        fn alist generalizing-alist (cdr term-lst)))))))

; See Guide.
; (B.6) determine the restrictions imposed by the invariant on the relevant state
;       components

(defun invariant-on-vformals (vformal-replacement-pairs base hyps state)
  (mv-let
   (assignments uninvertables)
   (invert-vformals vformal-replacement-pairs
                    base
                    (cdr (assoc-eq :list (table-alist 'generalized-updater-drivers (w state))))
                    (cdr (assoc-eq :list (table-alist 'constructor-drivers (w state))))
                    nil nil)
   (cond
    (uninvertables
     (er soft 'invariant-on-vformals
         "We were unable to invert ~&0.  This means you probably need to ~
          extend the driver tables in your DEF-MODEL-API command.  To see the ~
          current tables evaluate (TABLE ACL2::MODEL-API)."
         uninvertables))
    ((not (subsetp-equal (all-vars1-lst (strip-cdrs assignments) nil)
                         (cons base (strip-cdrs vformal-replacement-pairs))))
     (er soft 'invariant-on-vformals
         "It was thought impossible that the inversion of virtual formals ~
          into their corresponding single assignment expressions would ~
          produce terms involving variables other than the base variable, ~
          ~x0, and the new value variables, ~x1.  But the inversions below ~
          contain the variables ~x2.  The inversions are shown below as (var  ~
          assignment) doublets:~%~X34."
         base
         (strip-cdrs vformal-replacement-pairs)
         (all-vars1-lst (strip-cdrs assignments) nil)
         (pairlis$ (strip-cars assignments)
                   (pairlis-x2 (strip-cdrs assignments)
                               nil))
         nil))
    (t (let ((conjuncts
              (revappend
               (flatten-ands-in-lit
                (simplify-under-hyps
                 hyps
                 `((lambda (,base) ,(conjoin hyps))
                   ,(compose-vformal-assignments assignments base nil))
                 state))
               nil)))
         (cond
          ((not (subsetp-equal (all-vars1-lst conjuncts nil)
                               (strip-cdrs vformal-replacement-pairs)))
           (er soft 'invariant-on-vformals
               "The attempt to isolate the constraints imposed by the ~
                invariant terms, ~X01, on the state components of interest, ~
                ~X21, has failed.  The isolated invariants must mention only ~
                the variables ~x3, but they in fact mention ~x4.~%~%This can ~
                occur if some rewrite rules are missing or unable to fire.  ~
                In the latter case, it may be that your specified invariant ~
                on the initial state is too weak to imply the hypotheses of ~
                some rewrite rule.  Other causes of this symptom are that ~
                state components are not independent -- e.g., writing to one ~
                affects reading from another -- or it is impossible to write ~
                to a relevant component.~%~%The `isolated' invariants are ~
                shown below and might give you a clue about the cause of this ~
                problem.  These terms should simplify, under your invariant, ~
                to terms that mention no free variables other than the ~
                projected formals of the new function, ~X31.  Try to prove ~
                rewrite rules and/or strengthen your invariant to allow the ~
                offending terms to simplify into terms that mention no free ~
                variables other than ~X31.  `Isolated' contraints:~%~%~X51."
               hyps
               nil
               (strip-cars vformal-replacement-pairs)
               (strip-cdrs vformal-replacement-pairs)
               (all-vars1-lst conjuncts nil)
               conjuncts))
          (t
           (value (conjoin conjuncts)))))))))

; (B.7) rearrange all the definitions' formals and calls so that formals are
;       in alphabetical order

(defun permutation-map1 (lst i lst1)
  (cond ((endp lst) nil)
        (t (cons (cons i (- (len lst1)
                            (len (member-equal (car lst) lst1))))
                 (permutation-map1 (cdr lst) (+ 1 i) lst1)))))

(defun permutation-map-for-non-duplicates (lst)

; A ``permutation map'' (or ``pmap'') is a list of (i . j) pairs meaning the
; that ith component of a list is to become the jth component in the reordered
; list.

  (permutation-map1 lst 0 (merge-sort-lexorder lst)))

(defun apply-permutation-map-to-list1 (pmap lst ans)
  (cond ((endp pmap) ans)
        (t (apply-permutation-map-to-list1
            (cdr pmap)
            lst
            (update-nth (cdr (car pmap))
                        (nth (car (car pmap)) lst)
                        ans)))))

(defun apply-permutation-map-to-list (pmap lst)
  (apply-permutation-map-to-list1 pmap lst nil))

(mutual-recursion
 (defun apply-permutation-map-to-term (pmap fn term)
   (cond
    ((variablep term) term)
    ((fquotep term) term)
    ((eq fn (ffn-symb term))
     (cons-term
      fn
      (apply-permutation-map-to-list pmap (fargs term))))
    (t (cons-term
        (ffn-symb term)
        (apply-permutation-map-to-term-lst pmap fn
                                           (fargs term))))))

 (defun apply-permutation-map-to-term-lst (pmap fn term-lst)
   (cond
    ((endp term-lst) nil)
    (t (cons (apply-permutation-map-to-term pmap fn (car term-lst))
             (apply-permutation-map-to-term-lst pmap fn
                                                (cdr term-lst)))))))

; See Guide.
; (B.8) determine whether there are other projected state components that
;       still occur in the body and if so cause an error

(defun make-sub-def-projections (fn i required-sub-projections dpro-alist api)
  (cond
   ((endp required-sub-projections)
    nil)
   (t (let ((fnname-i
             (intern-in-package-of-symbol
              (string-append
               (symbol-name fn)
               (string-append
                "-SUBR-"
                (coerce (packn1 (list i)) 'string)))
              (access model-api api :package-witness))))
        (cons `(def-projection
                 :new-fn ,fnname-i
                 :projector ,(car (car required-sub-projections))
                 :old-fn ,(cdr (car required-sub-projections))
                 :hyps+ ,(cdr (assoc-eq :hyps+ dpro-alist)))
              (make-sub-def-projections fn (+ i 1)
                                        (cdr required-sub-projections)
                                        dpro-alist api))))))

; Now we begin putting it all together.

; See Guide. Overview of How the Def-Projection Command Works

(defun translate-def-projection-args (alist api state)

; We take the alist of keyword arguments provided to def-projection and translate
; each value, producing either an error or an alist mapping each keyword to its
; translated value.  The result is called ``dpro-alist'' in parallel with
; ``dsem-alist.''

  (let ((new-fn (cdr (assoc-eq :new-fn alist)))
        (projector (cdr (assoc-eq :projector alist)))
        (old-fn (cdr (assoc-eq :old-fn alist)))
        (hyps+ (cdr (assoc-eq :hyps+ alist)))
        (svar (access model-api api :svar)))
    (cond
     ((not (symbolp new-fn))
      (er soft 'def-projection
          "The first argument of DEF-PROJECTION must be a symbol and ~x0 isn't."
          new-fn))
     ((not (and (symbolp old-fn)
                (equal (arity old-fn (w state)) 1)))
      (er soft 'def-projection
          "The third argument of DEF-PROJECTION must be a function symbol of ~
           arity 1 naming the target semantic function; ~x0 isn't."
          old-fn))
     ((not (eq (legal-variable-or-constant-namep svar) 'variable))
      (er soft 'def-projection
          "The fourth argument of DEF-PROJECTION must be a symbol naming the ~
           state variable and ~x0 isn't."
          svar))
     (t (er-let*
          ((projector
            (translate projector t t nil 'def-projection (w state) state))
           (hyps+
            (er-progn
             (chk-true-listp hyps+
                             'def-projection
                             "The :HYPS+ argument"
                             state)
             (translate-list-of-terms hyps+ state))))

; Here are the full-translated def-projection arguments in alist form, aka
; ``dpro-alist.''

          (value
           `((:new-fn . ,new-fn)
             (:projector . ,projector)
             (:old-fn . ,old-fn)
             (:hyps+ . ,hyps+))))))))

(defun project-fn-to-fn (dpro-alist api state)
  (let* ((new-fn (cdr (assoc-eq :new-fn dpro-alist)))
         (projector (cdr (assoc-eq :projector dpro-alist)))
         (old-fn (cdr (assoc-eq :old-fn dpro-alist)))
         (hyps+ (cdr (assoc-eq :hyps+ dpro-alist)))
         (api+ (change model-api
                       api
                       :hyps (append (access model-api api :hyps)
                                     hyps+)))
         (svar (access model-api api+ :svar))
         (hyps (access model-api api+ :hyps))
         (state-comps-and-types
          (access model-api api+ :state-comps-and-types))
         (var-names
          (access model-api api+ :var-names))
         (init-body
          (apply-projector-to-term hyps projector svar
                                   (body old-fn t (w state)) state))
         (init-components-and-types
          (find-all-state-components-and-types-outside
           init-body old-fn svar state-comps-and-types))
         (state-expression-patterns
          (strip-cars
           (append
            (cdr
             (assoc-eq
              :list
              (table-alist 'generalized-updater-drivers (w state))))
            (cdr
             (assoc-eq
              :list
              (table-alist 'constructor-drivers (w state))))))))
    (mv-let
     (ebody call-number-alist)
     (enumerated-projected-body init-body projector svar old-fn nil)

; Ebody is init-body with all the projected recursions replaced by integers and
; call-number-alist is the map from those integers to the next state
; expressions in the corresponding recursions.

     (let* ((components-and-types-alist
             (components-and-types-to-actual-expressions-by-call*
              hyps
              init-components-and-types
              old-fn
              svar
              call-number-alist
              nil
              state-comps-and-types
              state))
            (vformals (strip-cars (strip-cars components-and-types-alist))))
       (er-let* ((formals
                  (simple-generate-variable-lst var-names vformals
                                                (list svar)
                                                api+
                                                state))
; The next three bindings need not be in this er-let*, but we'd just have to
; shift out to a let and then get back into an er-let* so we did it this way.

                 (pmap (value (permutation-map-for-non-duplicates formals)))
                 (generalizing-alist (value (pairlis$ vformals formals)))

; Body, below, contains the tests made by the code itself, expressed in terms
; of the new formals.  These tests are from source (a) of the discussion On
; Identifying State Components.
                 (body
                  (value (re-introduce-recursions-and-generalize
                          new-fn components-and-types-alist generalizing-alist ebody)))

                 (generalized-hyp
                  (invariant-on-vformals generalizing-alist svar hyps state)))

; Body1 contains the tests derived from the invariant, i.e., from source (b)
; above.

         (let* ((body1 (if (eq generalized-hyp *t*)
                           body
                           `(IF ,generalized-hyp
                                ,body
                                ,*0*)))

; Body2, below, contains the hyps (generalized to the new formals) derived from
; inherent properties of the virtual formals, i.e., from source (c).

                (inherent-hyp
                 (sublis-expr
                  generalizing-alist
                  (conjoin
                   (strip-cadrs
                    (strip-cars components-and-types-alist)))))
                (body2 (if (equal inherent-hyp *t*)
                           body1
                           `(IF ,inherent-hyp
                                ,body1
                                ,*0*)))

; Formals3 and body3 are the formals and body that we'll actually use.  They
; have been reordered to put the formals into lexorder.  Note: there is no
; formals1 or formals2, it's just that we want formals3 and body3 to be used
; together.

                (formals3 (apply-permutation-map-to-list pmap formals))
                (body3 (apply-permutation-map-to-term pmap new-fn body2))

                (required-sub-projections
                 (all-projector-and-other-fnsymb
                  body3 old-fn svar
                  state-comps-and-types
                  state-expression-patterns)))
           (cond
            (required-sub-projections
             (er soft 'def-projection
                 "The following additional projections should be performed ~
                  before this one has a chance of succeeding.  We don't do ~
                  this automatically because you may want to change the names ~
                  given to the various new functions or otherwise change the ~
                  commands.  We thought it best for you to be in charge.  ~
                  Resubmit the current projection when you've successfully done ~
                  those below.~%~%By the way, because new projections can ~
                  introduce new state components to be tracked, you may have ~
                  to iterate this process several times before all the ~
                  relevant state components are identified.  Here are the ~
                  projections we currently require:~%~%~*0~%~%These ~
                  projections are based on this partially simplified ~
                  ``definition'' for the function you requested. This ~
                  ``definition'' does not satisfy even the ~
                  most rudimentary syntactic rules for definitions because we ~
                  failed to simplify certain subexpressions.  Perhaps these ~
                  will suggest additional rules to prove or additional ~
                  hypotheses to add to this projection so that existing rules ~
                  will fire.~%~%~X12~%~%If all else fails, you might try ~
                  (trace$ acl2::simplify-under-hyps) and look at the returned ~
                  terms and see if any strike you as susceptible to further ~
                  simplification!"
                 (list* "~X*1~%~%" "~X*1~%~%" "~X*1~%~%" "~X*1~%~%"
                        (make-sub-def-projections new-fn 0
                                                  required-sub-projections
                                                  dpro-alist api+)
                        (list (cons #\1 nil)))
                 `(DEFUNM ,new-fn ,formals3 ,body3)
                 nil))
            ((occur svar body3)
             (er soft 'def-projection
                 "We were unable to eliminate all occurrences of the state ~
                  variable, ~x0, from the projected body of ~x1.  How might ~
                  you make it possible to eliminate the state ~
                  variable?~%~%One possibility is to add conjuncts to the ~
                  governing :hyps invariant in your DEF-MODEL-API command, so ~
                  that the offending occurrences are eliminated because they ~
                  appear on now-impossible paths.  This approach may not be ~
                  available to you, since the strengthened hypothesis must be ~
                  invariant as ~x1 recurs.~%~%Another possibility is to add ~
                  entries to the :STATE-COMPS-AND-TYPES of your DEF-MODEL-API ~
                  so that the expressions containing the offending ~
                  occurrences are generalized to new formal parameters.  This ~
                  approach may not be available because all the listed ~
                  patterns must be mutually ``orthogonal,'' changing the ~
                  value of one such state component must not affect the value ~
                  of any other.  Thus, for example, it is impossible for both ~
                  the 8 byte word starting at address m to be a component ~
                  while the 4 byte word starting at that same address m is ~
                  too:  they are not orthogonal.~%~%A third possibility is ~
                  that the offending occurrence of ~x0 appears in an argument ~
                  to a subfunction of ~x4.  If this is the case -- and some ~
                  component of the subfunction's value is being used in the ~
                  projection we're trying to develop here -- then it would be ~
                  helpful to first do that projection, i.e., create a ~
                  DEF-PROJECTION command of the relevant component of the ~
                  subfunction.  Then return to the def-projection you're ~
                  trying to do now.  Normally we detect this need for another ~
                  def-projection and warn you about it explicitly, but we ~
                  cannot do so here because the un-projected expression is ~
                  holding an un-eliminated occurrence of state.~%~%A fourth ~
                  alternative is to take the sketch of the derived projection ~
                  below as your starting point and edit it to your ~
                  satisfaction!  Below is an approximation of what ~
                  DEF-PROJECTION has generated. Unfortunately, we can't even ~
                  generate the final version because we can't make it satisfy ~
                  even the basic syntactic rules of a ~
                  definition.~%~%~X23~%~%Perhaps the ``definition'' above ~
                  will suggest additional rules to prove or additional ~
                  hypotheses to add to your model API.  If all else fails, ~
                  you might try (trace$ acl2::simplify-under-hyps) and look ~
                  at the returned terms and see if any strike you as ~
                  susceptible to further simplification!"
                 svar
                 new-fn
                 `(DEFUNM ,new-fn ,formals3 ,body3)
                 nil
                 old-fn))
            (t
             (value
              `(make-event
                (er-progn
                 (do-and-undo
                  (er-progn (defunm ,new-fn ,formals3 ,body3)
                            (assign def-projection-body4
                                    (simplify-under-hyps nil ',body3 state))))
                 (value
                  `(PROGN
                    (DEFUNM ,',new-fn ,',formals3
                      :OPTIONS (:NON-REC-FLAG-LEMMAS)
                      ,(untranslate
                        (undistribute-ifs
                         (@ def-projection-body4))
                        nil
                        (w state)))
                    (DEFTHM ,',(intern-in-package-of-symbol
                                (coerce (append (coerce (symbol-name new-fn) 'list)
                                                (coerce "-CORRECT" 'list))
                                        'string)
                                (access model-api api+ :package-witness))
                      (IMPLIES
                       ,',(pretty-and hyps)
                       (EQUAL
                        ,',(subst-var (list old-fn svar) svar projector)
                        (,',new-fn ,@',(apply-permutation-map-to-list
                                        pmap
                                        (strip-cars generalizing-alist)))))))))))))))))))

(defmacro def-projection (&key new-fn projector old-fn hyps+)
  `(make-event
    (er-let*
      ((dpro-alist
        (translate-def-projection-args
         '((:new-fn . ,new-fn)
           (:projector . ,projector)
           (:old-fn . ,old-fn)
           (:hyps+ . ,hyps+))
         (cdr (assoc-eq :record (table-alist 'model-api (w state))))
         state)))
      (value
       `(make-event
         (project-fn-to-fn ',dpro-alist
                           (cdr (assoc-eq :record (table-alist 'model-api (w state))))
                           state))))))

; =============================================================================
; How to Certify Codewalker

; The files you'll need (on some directory) to run Codewalker and a
; demonstration of it are:

; if-tracker.lisp
; simplify-under-hyps.lisp
; terminatricks.lisp
; codewalker.lisp
; m1-version-3.lisp
; basic-demo.lsp

; To certify all these books (except the last, which is not a book) execute the
; following in ACL2:

; (certify-book "if-tracker")          ; used by Terminatricks and Codewalker via
; (u)                                  ;  this one:
; (certify-book "simplify-under-hyps") ; used by Terminatricks and Codewalker
; (u)
; (certify-book "terminatricks")
; (u)
; (certify-book "codewalker")
; (u)
; (defpkg "M1"
;   (set-difference-eq (union-eq *acl2-exports*
;                                *common-lisp-symbols-from-main-lisp-package*)
;                      '(push pop pc program step)))
; (certify-book "m1-version-3" 1)
; (u)
; (u)

; If you want to use Emacs tags tables to jump around in the code, run etags in a shell and
; visit the tags table on this directory:

; % etags if-tracker.lisp simplify-under-hyps.lisp terminatricks.lisp codewalker.lisp m1-version-3.lisp

; To run the demo do

; (ld "basic-demo.lsp" :ld-pre-eval-print t)

; [the end -- search backwards twice for the barrier to get to the top of Code]
; =============================================================================
