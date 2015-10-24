; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Adapted by Matt Kaufmann from J Moore's file, basic-demo.lsp.

(in-package "M1")

; -----------------------------------------------------------------
; Demo of Def-Semantics and Def-Projection

; NOTE: See the following included book, demo-fact-preamble, for important
; comments pertaining to this demo.

(include-book "demo-fact-preamble")
(set-verify-guards-eagerness 0) ; local to the book above

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
; will call another newly introduced function, SEM-4, which the semantics of
; the loop starting at pc 4.

(def-semantics
  :init-pc 0
  :focus-regionp nil
  :root-name nil
  :hyps+ ((program1p s)

; The following conditions are probably stronger than needed.

          (nat-listp (rd :locals s))
          (nat-listp (rd :stack s)))
  :annotations nil
  )

#||
(untrace$)
||#

; Having run def-semantics, you can look at the results.  The command above will
; create 4 defuns, clk-4, clk-0, sem-4, and sem-0, and two defthms, one stating
; the correctness of sem-4 and one the correctness of sem-0.  Here are commands
; that inspect these, and, for the record, the output.

#||
M1 !>(pcb :x)
   d      16:x(DEF-SEMANTICS :INIT-PC 0 ...)
               (TABLE ACL2::MEASURE-PATTERNS :LIST ...)
 L d           (DEFUN CLK-4 (S) ...)
               (TABLE ACL2::MEASURE-PATTERNS :LIST ...)
 L d           (DEFUN CLK-0 (S) ...)
 L             (DEFUN SEM-4 (S) ...)
 L             (DEFUN SEM-0 (S) ...)
               (DEFTHM SEM-4-CORRECT ...)
               (IN-THEORY (DISABLE CLK-4))
               (DEFTHM SEM-0-CORRECT ...)
               (IN-THEORY (DISABLE CLK-0))
M1 !>(pe 'clk-4)
   d      16:x(DEF-SEMANTICS :INIT-PC 0 ...)
              \
>L d           (DEFUN
                CLK-4 (S)
                (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
                (DECLARE
                 (XARGS
                    :MEASURE
                    (ACL2::DEFUNM-MARKER (ACL2-COUNT (NTH 0 (RD :LOCALS S))))
                    :WELL-FOUNDED-RELATION O<))
                (DECLARE (XARGS :STOBJS (S)))
                (PROG2$
                 (ACL2::THROW-NONEXEC-ERROR 'CLK-4
                                            (LIST S))
                 (IF
                  (AND (AND (HYPS S) (PROGRAM1P S))
                       (EQUAL (NTH 3 (RD :LOCALS S)) 1))
                  (IF
                   (EQUAL (NTH 0 (RD :LOCALS S)) 0)
                   3
                   (BINARY-CLK+
                    11
                    (CLK-4
                     (WR
                       :PC 4
                       (WR :LOCALS
                           (UPDATE-NTH 0
                                       (+ (NTH 0 (RD :LOCALS S))
                                          (- (NTH 3 (RD :LOCALS S))))
                                       (UPDATE-NTH 1
                                                   (* (NTH 0 (RD :LOCALS S))
                                                      (NTH 1 (RD :LOCALS S)))
                                                   (RD :LOCALS S)))
                           S)))))
                  0)))
M1 !>(pe 'sem-4)
   d      16:x(DEF-SEMANTICS :INIT-PC 0 ...)
              \
>L             (DEFUN
                SEM-4 (S)
                (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
                (DECLARE
                 (XARGS
                    :MEASURE
                    (ACL2::DEFUNM-MARKER (ACL2-COUNT (NTH 0 (RD :LOCALS S))))
                    :WELL-FOUNDED-RELATION O<))
                (DECLARE (XARGS :STOBJS (S)))
                (PROG2$
                 (ACL2::THROW-NONEXEC-ERROR 'SEM-4
                                            (LIST S))
                 (IF
                  (AND (AND (HYPS S) (PROGRAM1P S))
                       (EQUAL (NTH 3 (RD :LOCALS S)) 1))
                  (IF
                   (EQUAL (NTH 0 (RD :LOCALS S)) 0)
                   (WR :PC 16
                       (WR :STACK
                           (PUSH (NTH 1 (RD :LOCALS S))
                                 (RD :STACK S))
                           S))
                   (SEM-4
                    (WR
                       :PC 4
                       (WR :LOCALS
                           (UPDATE-NTH 0
                                       (+ (NTH 0 (RD :LOCALS S))
                                          (- (NTH 3 (RD :LOCALS S))))
                                       (UPDATE-NTH 1
                                                   (* (NTH 0 (RD :LOCALS S))
                                                      (NTH 1 (RD :LOCALS S)))
                                                   (RD :LOCALS S)))
                           S))))
                  S)))
M1 !>(pe 'sem-0)
   d      16:x(DEF-SEMANTICS :INIT-PC 0 ...)
              \
>L             (DEFUN
                SEM-0 (S)
                (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
                (DECLARE (XARGS :STOBJS (S)))
                (PROG2$
                 (ACL2::THROW-NONEXEC-ERROR 'SEM-0
                                            (LIST S))
                 (IF
                  (AND (HYPS S) (PROGRAM1P S))
                  (SEM-4
                     (WR :PC 4
                         (WR :LOCALS
                             (UPDATE-NTH 1 1 (UPDATE-NTH 3 1 (RD :LOCALS S)))
                             S)))
                  S)))
M1 !>(pe 'sem-4-correct)
   d      16:x(DEF-SEMANTICS :INIT-PC 0 ...)
              \
>              (DEFTHM SEM-4-CORRECT
                       (IMPLIES (AND (HYPS S)
                                     (PROGRAM1P S)
                                     (EQUAL (RD :PC S) 4))
                                (EQUAL (M1 S (CLK-4 S)) (SEM-4 S))))
M1 !>(pe 'sem-0-correct)
   d      16:x(DEF-SEMANTICS :INIT-PC 0 ...)
              \
>              (DEFTHM SEM-0-CORRECT
                       (IMPLIES (AND (HYPS S)
                                     (PROGRAM1P S)
                                     (EQUAL (RD :PC S) 0))
                                (EQUAL (M1 S (CLK-0 S)) (SEM-0 S))))
M1 !>
||#

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
  :old-fn SEM-4
  :hyps+ ((program1p s)

; The following conditions are probably stronger than needed.

          (nat-listp (rd :locals s))
          (nat-listp (rd :stack s)))
  )

#||
(untrace$)
||#

#||
M1 !>(pcb :x)
          17:x(DEF-PROJECTION :NEW-FN FN1-LOOP ...)
 L             (DEFUN FN1-LOOP (R0 R1 R3) ...)
               (DEFTHM FN1-LOOP-CORRECT ...)
M1 !>
||#

; The function name ``FN1-LOOP'' was chosen by the user to be memorable.  It
; means to suggest ``the function that computes the final value of R1 starting
; from the loop.''  The function fn1-loop returns the (nth 1 (rd :locals s)) of
; the state s obtained by running sem-4.  Below is the generated definition.
; Note that it needs three arguments, R0, R1, and R3, from s, but nothing else.
; The correctness theorem shows that it does what is claimed -- and
; coincidentally exhibits the correspondence between the formals of fn1-loop
; and the values of certain components in the initial s.

#||
M1 !>(pe 'fn1-loop)
          17:x(DEF-PROJECTION :NEW-FN FN1-LOOP ...)
              \
>L             (DEFUN
                   FN1-LOOP (R0 R1 R3)
                   (DECLARE
                        (XARGS :MEASURE (ACL2::DEFUNM-MARKER (ACL2-COUNT R0))
                               :WELL-FOUNDED-RELATION O<))
                   (COND ((OR (NOT (INTEGERP R3))
                              (< R3 0)
                              (NOT (INTEGERP R0))
                              (< R0 0)
                              (NOT (INTEGERP R1))
                              (< R1 0))
                          0)
                         ((OR (NOT (EQUAL R3 1)) (EQUAL R0 0))
                          R1)
                         (T (FN1-LOOP (+ -1 R0) (* R0 R1) 1))))
M1 !>(pe 'fn1-loop-correct)
          17:x(DEF-PROJECTION :NEW-FN FN1-LOOP ...)
              \
>              (DEFTHM FN1-LOOP-CORRECT
                       (IMPLIES (AND (HYPS S) (PROGRAM1P S))
                                (EQUAL (NTH '1 (RD ':LOCALS (SEM-4 S)))
                                       (FN1-LOOP (NTH '0 (RD ':LOCALS S))
                                                 (NTH '1 (RD ':LOCALS S))
                                                 (NTH '3 (RD ':LOCALS S))))))
M1 !>
||#

; Now we project the R1 component of SEM-0 and name that fn fn1.
(def-projection
  :new-fn FN1
  :projector (nth 1 (rd :locals s))
  :old-fn SEM-0
  :hyps+ ((program1p s)

; The following conditions are probably stronger than needed.

          (nat-listp (rd :locals s))
          (nat-listp (rd :stack s)))
  )

#||
M1 !>(pe 'fn1)
          18:x(DEF-PROJECTION :NEW-FN FN1 ...)
              \
>L             (DEFUN FN1 (R0)
                      (IF (OR (NOT (INTEGERP R0)) (< R0 0))
                          0 (FN1-LOOP R0 1 1)))
M1 !>(pe 'fn1-correct)
          18:x(DEF-PROJECTION :NEW-FN FN1 ...)
              \
>              (DEFTHM FN1-CORRECT
                       (IMPLIES (AND (HYPS S) (PROGRAM1P S))
                                (EQUAL (NTH '1 (RD ':LOCALS (SEM-0 S)))
                                       (FN1 (NTH '0 (RD ':LOCALS S))))))
M1 !>
||#

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
                (nat-listp (rd :locals s))
                (nat-listp (rd :stack s))
                (equal (rd :pc s) 0))
           (equal (nth 1 (rd :locals (m1 s (clk-0 s))))
                  (! (nth 0 (rd :locals s))))))
