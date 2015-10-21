; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is extracted from the first part of demo-fact.lisp, so that it can
; be included not only there, but also in demo-fact-partial.lsp.

(in-package "M1")

(include-book "codewalker") ; codewalker source
(include-book "m1-version-3") ; stobj version of M1 model
(set-verify-guards-eagerness 0)

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

 (defun hyps (s)
   (declare (xargs :stobjs (s)))
   (and (sp s)
        (natp (rd :pc s))
        (< (rd :pc s) (len (rd :program s)))
        (< 16 (len (rd :locals s)))
        (integer-listp (rd :locals s))
        (integer-listp (rd :stack s))))

 (defthm nat-listp-nth
   (implies (and (nat-listp x)
                 (natp i)
                 (< i (len x)))
            (natp (nth i x)))
   :rule-classes (:rewrite :type-prescription))

 (defthm nat-listp-update-nth
   (implies (natp (nth i x))
            (equal (nat-listp (update-nth i v x))
                   (and (natp v)
                        (nat-listp x)))))

 (defthm integer-listp-nth
   (implies (and (integer-listp x)
                 (natp i)
                 (< i (len x)))
            (integerp (nth i x)))
   :rule-classes (:rewrite :type-prescription))

 (defthm integer-listp-update-nth
   (implies (integerp (nth i x))
            (equal (integer-listp (update-nth i v x))
                   (and (integerp v)
                        (integer-listp x)))))

 (in-theory (disable nat-listp integer-listp len nth update-nth))
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
  :state-comps-and-types  (((NTH I (RD :LOCALS S)) (INTEGERP (NTH I (RD :LOCALS S))))
                           ((RD :STACK S)          (INTEGER-LISTP (RD :STACK S)))
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
; name-print-base                    when generating names, e.g., SEM-4
;                                     (general form: SEM-<root-name>-<pc>)
;                                     print pc in this base, 2, 8, 10, 16.

(defconst *program1*
  '((ICONST 1)  ; 0
    (ISTORE 1)  ; 1  reg[1] := 1;
    (ICONST 1)  ; 2
    (ISTORE 3)  ; 3  reg[3] := 1;
    (ILOAD 0)   ; 4                         ; <--- loop
    (IFEQ 10)   ; 5  if R0=0, goto 10+5;
    (ILOAD 1)   ; 6
    (ILOAD 0)   ; 7
    (IMUL)      ; 8
    (ISTORE 1)  ; 9  reg[1] := reg[0] * reg[1];
    (ILOAD 0)   ;10
    (ILOAD 3)   ;11
    (ISUB)      ;12
    (ISTORE 0)  ;13  reg[0] := reg[0] - reg[3];
    (GOTO -10)  ;14  goto 14-10;            ; goto loop
    (ILOAD 1)   ;15
    (HALT)))    ;16  halt with factorial on top of stack;

; Note that the program computes the product of the naturals from
; reg[0] down to 0, leaving the product (aka factorial) in reg[1].
; Reg[3] is the constant +1 and the iteration replaces reg[0] by
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
