; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; -----------------------------------------------------------------
; Demo of Def-Semantics and Def-Projection

; This is not a book.  To replay these events do:
; (ld "basic-demo.lsp" :ld-pre-eval-print t)

(include-book "codewalker") ; codewalker source
(include-book "m1-version-3") ; stobj version of M1 model
(set-verify-guards-eagerness 0)

(in-package "M1")

; Step 1 of Codewalker Methodology: Develop the canonical forms of the
; independently readable/writeable state components and the lemmas necessary to
; do code proofs in the model.

; We define hyps, which is the ``good state'' invariant for this M1 model, and
; we prove several conventional lemmas allowing us to reason about individual
; state components from the invariant.  This invariant omits discussion of the
; program component of s, so that we can use the same API with different
; programs, as shown later below.

(encapsulate
 nil
 (defun natp-listp (x)
   (if (endp x)
       (equal x nil)
       (and (natp (car x))
            (natp-listp (cdr x)))))

 (defun hyps (s)
   (declare (xargs :stobjs (s)))
   (and (sp s)
        (natp (rd :pc s))
        (< (rd :pc s) (len (rd :program s)))
        (< 16 (len (rd :locals s)))
        (natp-listp (rd :locals s))
        (natp-listp (rd :stack s))))

 (defthm natp-listp-nth
   (implies (and (natp-listp x)
                 (natp i)
                 (< i (len x)))
            (natp (nth i x)))
   :rule-classes (:rewrite :type-prescription))

 (defthm natp-listp-update-nth
   (implies (and (natp i)
                 (< i (len x))
                 (natp (nth i x)))
            (equal (natp-listp (update-nth i v x))
                   (and (natp v)
                        (natp-listp x)))))

 (in-theory (disable natp-listp len nth update-nth))
 )

; Since we're in the M1 package, it is convenient to define
; these macros.

(defmacro def-model-api (&rest x) `(acl2::def-model-api ,@x))
(defmacro def-semantics (&rest x) `(acl2::def-semantics ,@x))
(defmacro def-projection (&rest x) `(acl2::def-projection ,@x))

; Next, we tell Codewalker what the state component accessors/updaters are, and
; their types.

(def-model-api
  :run M1
  :svar S
  :stobjp T
  :hyps ((HYPS S))
  :step STEP
  :get-pc (LAMBDA (S) (RD :PC S))
  :put-pc (LAMBDA (V S) (WR :PC V S))
  :updater-drivers (((UPDATE-NTH I :VALUE :BASE)
                     (NTH I :BASE))
                    ((WR LOC :VALUE :BASE)
                     (RD LOC :BASE)))
  :constructor-drivers nil
  :state-comps-and-types  (((NTH I (RD :LOCALS S)) (NATP (NTH I (RD :LOCALS S))))
                           ((RD :STACK S)          (NATP-LISTP (RD :STACK S)))
                           ((RD :PC S)             (NATP (RD :PC S))))
  :callp  nil
  :ret-pc nil
  :returnp nil
  :clk+ binary-clk+
  :name-print-base nil
  :var-names (((RD :PC S) "PC")
              ((NTH I (RD :LOCALS S)) "R~x0" I)
              ((RD :STACK S) "STK"))
  )

; The unused keyword arguments to def-model-api (those with nil values above)
; mean:

; :constructor-drivers               give state constructor function
;                                     followed by successive accessors
;                                     e.g., ((cons a b)
;                                            (car :base) (cdr :base))
;                                     if used in model
; callp, ret-pc, returnp             the first and last recognize when the
;                                      the pc points to a call or return;
;                                      the middle one gives the location of
;                                      of the return pc after a call.
; name-print-base                    when generating names, e.g., SEM-6
;                                     (general form: SEM-<root-name>-<pc>)
;                                     print pc in this base, 2, 8, 10, 16.

(defconst *program1*
  '((ICONST 1)  ; 0
    (ISTORE 1)  ; 1  reg[1] := 1;
    (ICONST 0)  ; 2
    (ISTORE 2)  ; 3  reg[2] := 0;
    (ICONST 1)  ; 4
    (ISTORE 3)  ; 5  reg[3] := 1;
    (ILOAD 0)   ; 6                         ; <--- loop
    (IFEQ 14)   ; 7  if R0=0, goto 14+7;
    (ILOAD 1)   ; 8
    (ILOAD 0)   ; 9
    (IMUL)      ;10
    (ISTORE 1)  ;11  reg[1] := reg[0] * reg[1];
    (ILOAD 2)   ;12
    (ILOAD 0)   ;13
    (IADD)      ;14
    (ISTORE 2)  ;15  reg[2] := reg[0] + reg[2];
    (ILOAD 0)   ;16
    (ILOAD 3)   ;17
    (ISUB)      ;18
    (ISTORE 0)  ;19  reg[0] := reg[0] - reg[3];
    (GOTO -14)  ;20  goto 20-14;            ; goto loop
    (ILOAD 1)   ;21
    (HALT)))    ;22  halt with factorial on top of stack;

; Note that the program computes the product and the sum of the naturals from
; reg[0] down to 0, leaving the product (aka factorial) in reg[1] and the sum
; in reg[2].  Reg[3] is the constant +1 and the iteration replaces reg[0] by
; reg[0] - reg[3].

; -----------------------------------------------------------------
; Standard block to hide equality with *program1*.

; This block of events introduces an additional constraint on the state: it
; contains *program1*.  We could have just included (equal (rd :program s)
; *program1*) in the state invariant, :hyps, of the API.  But that would mean
; we'd have to repeat a slightly different API if we wanted to verify a
; different program.  So we will use the :hyps+ feature of def-semantics and
; def-projection to stipulate which program we're dealing with.  But we also
; prefer for the value of the ``big'' constant *program1* NOT to appear in our
; proofs or the functions that def-semantics writes.  So we define program1p to
; check that the program is *program1*.  Then we prove what we need to show
; that invariant is maintained.  Then we disable program1p.  

; This is a standard sequence of events to hide a constant.  Note that if
; you're only going to verify one program against an API, you might as well put
; the program into the :hyps of the API.  That can be argued to be
; short-sighted: you never know when you might want to ``re-use'' the API to
; verify another program against the same model and then you'd have to change
; the API.

; To handle a different program with the API above just define program2p in a
; way analogous to that done below, and then do everything below for program2p
; instead of program1p.

(defun program1p (s)
  (declare (xargs :stobjs (s)))
  (equal (rd :program s) *program1*))

(defthm program1p-preserved
  (implies (not (equal key :program))
           (equal (program1p (wr key v s))
                  (program1p s))))

(defthm len-program1p
  (implies (program1p s)
           (equal (len (rd :program s))
                  (len *program1*))))

(defthm resolve-next-inst1
  (implies (program1p s)
           (equal (nth i (rd :program s))
                  (nth i *program1*))))

(in-theory (disable program1p))
; -----------------------------------------------------------------

; If you are trying to follow the implementation-level view of this
; demonstration you should trace each of the interesting steps of the
; def-semantics command.  We advise the student to look only at the top-level
; entry and exit of the trace output generated; ignore the interior calls.

; We advise not tracing things if you want the user-level view.
#||
(trace$ acl2::link-graphs
        acl2::categorize-pcs
        acl2::path-tree-tuples-from-cutpoint-lst
        acl2::call-graph-ordering
        acl2::generate-clock-function-body
        acl2::generate-semantic-function-body
        acl2::disguised-constant-4-tuple-lst
        acl2::modify-hyps-in-defun-pairs
        acl2::generate-correctness-theorem)
||#

; Here is the command that causes Codewalker to explore our *program1* and
; create a semantic function, named SEM-0, since the initial pc is 0.  SEM-0
; will call another newly introduced function, SEM-6, which the semantics of
; the loop starting at pc 6.

(def-semantics
  :init-pc 0
  :focus-regionp nil
  :root-name nil
  :hyps+ ((program1p s))
  :annotations nil
  )

#||
(untrace$)
||#

; Having run def-semantics, you can look at the results.  The command above will
; create 4 defuns, clk-6, clk-0, sem-6, and sem-0, and two defthms, one stating
; the correctness of sem-6 and one the correctness of sem-0.  Here are commands
; that inspect these, and, for the record, the output.

(pcb :x)
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

(pe 'clk-6)
; (DEFUN CLK-6 (S)
;  (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
;  (DECLARE (XARGS
;            :MEASURE
;            (ACL2::DEFUNM-MARKER (ACL2-COUNT (NTH 0 (RD :LOCALS S))))
;            :WELL-FOUNDED-RELATION O<))
;  (DECLARE (XARGS :STOBJS (S)))
;  (PROG2$
;   (ACL2::THROW-NONEXEC-ERROR 'CLK-6 (LIST S))
;   (IF (AND (HYPS S)
;            (PROGRAM1P S)
;            (EQUAL (NTH 3 (RD :LOCALS S)) 1))
;       (IF
;        (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;        3
;        (BINARY-CLK+
;         15
;         (CLK-6
;          (WR
;           :PC 6
;           (WR
;            :LOCALS
;            (UPDATE-NTH 0 (+ (NTH 0 (RD :LOCALS S))
;                             (- (NTH 3 (RD :LOCALS S))))
;                        (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                                         (NTH 1 (RD :LOCALS S)))
;                                    (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                                     (NTH 2 (RD :LOCALS S)))
;                                                (RD :LOCALS S))))
;             S)))))
;        0)))

(pe 'clk-0)
; (DEFUN CLK-0 (S)
;   (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
;   (DECLARE (XARGS :STOBJS (S)))
;   (PROG2$
;    (ACL2::THROW-NONEXEC-ERROR 'CLK-0 (LIST S))
;    (IF (AND (HYPS S) (PROGRAM1P S))
;        (BINARY-CLK+
;         6
;         (CLK-6
;          (WR
;           :PC 6
;           (WR
;            :LOCALS
;            (UPDATE-NTH 1 1
;                        (UPDATE-NTH 2 0 (UPDATE-NTH 3 1 (RD :LOCALS S))))
;            S))))
;        0)))

(pe 'sem-6)
; (DEFUN SEM-6 (S)
;   (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
;   (DECLARE
;    (XARGS
;     :MEASURE
;     (ACL2::DEFUNM-MARKER (ACL2-COUNT (NTH 0 (RD :LOCALS S))))
;     :WELL-FOUNDED-RELATION O<))
;   (DECLARE (XARGS :STOBJS (S)))
;   (PROG2$
;    (ACL2::THROW-NONEXEC-ERROR 'SEM-6 (LIST S))
;    (IF
;     (AND (HYPS S)
;          (PROGRAM1P S)
;          (EQUAL (NTH 3 (RD :LOCALS S)) 1))
;     (IF
;      (EQUAL (NTH 0 (RD :LOCALS S)) 0)
;      (WR :PC 22 (WR :STACK
;                     (PUSH (NTH 1 (RD :LOCALS S))
;                           (RD :STACK S))
;                     S))
;      (SEM-6
;       (WR
;        :PC 6
;        (WR
;         :LOCALS
;         (UPDATE-NTH
;          0 (+ (NTH 0 (RD :LOCALS S))
;               (- (NTH 3 (RD :LOCALS S))))
;          (UPDATE-NTH 1 (* (NTH 0 (RD :LOCALS S))
;                           (NTH 1 (RD :LOCALS S)))
;                      (UPDATE-NTH 2 (+ (NTH 0 (RD :LOCALS S))
;                                       (NTH 2 (RD :LOCALS S)))
;                                  (RD :LOCALS S))))
;         S))))
;     S)))

(pe 'sem-0)
; (DEFUN SEM-0 (S)
;   (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
;   (DECLARE (XARGS :STOBJS (S)))
;   (PROG2$
;    (ACL2::THROW-NONEXEC-ERROR 'SEM-0 (LIST S))
;    (IF
;     (AND (HYPS S) (PROGRAM1P S))
;     (SEM-6
;      (WR
;       :PC 6
;       (WR
;        :LOCALS
;        (UPDATE-NTH 1 1
;                    (UPDATE-NTH 2 0 (UPDATE-NTH 3 1 (RD :LOCALS S))))
;        S)))
;     S)))

(pe 'sem-6-correct)
; (DEFTHM SEM-6-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S) (EQUAL (RD :PC S) 6))
;            (EQUAL (M1 S (CLK-6 S))
;                   (SEM-6 S))))

(pe 'sem-0-correct)
; (DEFTHM SEM-0-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S) (EQUAL (RD :PC S) 0))
;            (EQUAL (M1 S (CLK-0 S))
;                   (SEM-0 S))))

; Now we exercise the projection facilities.  Again, for an implementation-level
; view, trace these functions.

; We advise not tracing things if you want the user-level view.
#||
(trace$ acl2::apply-projector-to-term
        acl2::find-all-state-components-and-types-outside
        acl2::enumerated-projected-body
        acl2::components-and-types-to-actual-expressions-by-call*
        acl2::re-introduce-recursions-and-generalize
        acl2::invariant-on-vformals
        acl2::apply-permutation-map-to-term
        acl2::all-projector-and-other-fnsymb)
||#

(def-projection
  :new-fn FN1-LOOP
  :projector (nth 1 (rd :locals s))
  :old-fn SEM-6
  :hyps+ ((program1p s))
  )

#||
(untrace$)
||#

(pcb :x)
;            9:x(DEF-PROJECTION :NEW-FN FN1-LOOP ...)
;  L             (DEFUN FN1-LOOP (R0 R1 R3) ...)
;                (DEFTHM FN1-LOOP-CORRECT ...)

; The function name ``FN1-LOOP'' was chosen by the user to be memorable.  It
; means to suggest ``the function that computes the final value of R1 starting
; from the loop.''  The function fn1-loop returns the (nth 1 (rd :locals s)) of
; the state s obtained by running sem-6.  Below is the generated definition.
; Note that it needs three arguments, R0, R1, and R3, from s, but nothing else.
; The correctness theorem shows that it does what is claimed -- and
; coincidentally exhibits the correspondence between the formals of fn1-loop
; and the values of certain components in the initial s.

(pe 'fn1-loop)
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

(pe 'fn1-loop-correct)
; (DEFTHM FN1-LOOP-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '1 (RD ':LOCALS (SEM-6 S)))
;                   (FN1-LOOP (NTH '0 (RD ':LOCALS S))
;                             (NTH '1 (RD ':LOCALS S))
;                             (NTH '3 (RD ':LOCALS S))))))

; Now we project the R1 component of SEM-0 and name that fn fn1.
(def-projection
  :new-fn FN1
  :projector (nth 1 (rd :locals s))
  :old-fn SEM-0
  :hyps+ ((program1p s))
  )

(pe 'fn1)
; (DEFUN FN1 (R0)
;   (IF (OR (NOT (INTEGERP R0)) (< R0 0))
;       0
;       (FN1-LOOP R0 1 1)))

(pe 'fn1-correct)
; (DEFTHM FN1-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '1 (RD ':LOCALS (SEM-0 S)))
;                   (FN1 (NTH '0 (RD ':LOCALS S))))))

; We can prove that fn1 is factorial by the easy, conventional method:

(defun ! (n)
  (if (zp n)
      1
      (* n (! (- n 1)))))

(defthm fn1-loop-is-!-gen
  (implies (and (natp r0) (natp r1))
           (equal (fn1-loop r0 r1 1)
                  (* r1 (! r0)))))

(defthm fn1-is-!
  (implies (natp r0)
           (equal (fn1 r0)
                  (! r0))))

; And because of all we know, we can immediately relate it to the
; result of running the code:

(defthm reg[1]-of-code-is-!
  (implies (and (hyps s)
                (program1p s)
                (equal (rd :pc s) 0))
           (equal (nth 1 (rd :locals (m1 s (clk-0 s))))
                  (! (nth 0 (rd :locals s))))))


; We can, also or instead, project R2:

(def-projection
  :new-fn FN2-LOOP
  :projector (NTH 2 (RD :LOCALS S))
  :old-fn SEM-6
  :hyps+ ((program1p s))
  )

(def-projection
  :new-fn FN2
  :projector (NTH 2 (RD :LOCALS S))
  :old-fn SEM-0
  :hyps+ ((program1p s))
  )

(pe 'fn2-loop)
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

(pe 'fn2)
; (DEFUN FN2 (R0)
;   (IF (OR (NOT (INTEGERP R0)) (< R0 0))
;       0
;       (FN2-LOOP R0 0 1)))

(pe 'fn2-correct)
; (DEFTHM FN2-CORRECT
;   (IMPLIES (AND (HYPS S) (PROGRAM1P S))
;            (EQUAL (NTH '2 (RD ':LOCALS (SEM-0 S)))
;                   (FN2 (NTH '0 (RD ':LOCALS S))))))

; And we can prove, via conventional use of ACL2, that FN2 is just
; (/ (* r0 (+ r0 1)) 2), and we can immediately relate it to running
; the *program1* code:

(defthm fn2-loop-is-sum-gen
  (implies (and (natp r0) (natp r2))
           (equal (fn2-loop r0 r2 1)
                  (+ r2 (/ (* r0 (+ r0 1)) 2)))))

(defthm fn2-is-sum
  (implies (natp r0)
           (equal (fn2 r0)
                  (/ (* r0 (+ r0 1)) 2))))

(defthm reg[2]-of-code-is-sum
  (implies (and (hyps s)
                (program1p s)
                (equal (rd :pc s) 0))
           (equal (nth 2 (rd :locals (m1 s (clk-0 s))))
                  (/ (* (nth 0 (rd :locals s)) (+ (nth 0 (rd :locals s)) 1)) 2))))

(quote (the end))



