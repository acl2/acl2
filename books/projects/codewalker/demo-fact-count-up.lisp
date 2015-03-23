; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Adapted by Matt Kaufmann from J Moore's file, basic-demo.lsp.

(in-package "M1")

; This demo is based on demo-fact.lisp.  See that file for comments.  Here, we
; mostly comment only on what is different about this example.

; Note that this adaptation of basic-demo.lsp has some comments and questions
; from me (Matt Kaufmann), marked with "!!", that might be resolved later as I
; get more familiar with Codewalker and/or Codewalker evolves.

; Unlike demo-fact.lisp, here the loop counts up from 1 to n, where n is the
; input, and terminates when the counter is equal to n.  (We could have made it
; terminate when the counter exceeds n, but what's the fun in that?)
; Termination thus depends on the following loop invariant: the counter is an
; integer less than n.

; -----------------------------------------------------------------
; Demo of Def-Semantics and Def-Projection

(include-book "codewalker") ; codewalker source
(include-book "m1-version-3") ; stobj version of M1 model
(set-verify-guards-eagerness 0)

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

; The algorithm of *program2* is as follows.  As with *program1*, reg[1]
; accumulates the answer.  This time, we initialize it with the input, which is
; the value fo reg[0] throughout the computation.  We also maintain a counter,
; in reg[2], that initially is 1.  On each iteration we multiply reg[1] by the
; input and then increment reg[2], until reg[2] is equal to the input, reg[0].
; Note that we avoid multiplying reg[1] by the input at the end of this
; iteration.

(defconst *program2*
  '((ILOAD 0)   ; 0
    (ISTORE 1)  ; 1  reg[1] := input
    (ICONST 1)  ; 2
    (ISTORE 2)  ; 3  reg[2] := 1
    (ICONST 1)  ; 4
    (ISTORE 3)  ; 5  reg[3] := 1;
    (ILOAD 0)   ; 6                         ; <--- loop
    (ILOAD 2)   ; 7
    (ISUB)      ; 8
    (IFEQ 10)   ; 9  if R2=R0, goto 10+9;
    (ILOAD 2)   ;10
    (ILOAD 1)   ;11
    (IMUL)      ;12
    (ISTORE 1)  ;13  reg[1] := reg[2] * reg[1];
    (ILOAD 2)   ;14
    (ILOAD 3)   ;15
    (IADD)      ;16
    (ISTORE 2)  ;17  reg[2] := reg[2] + reg[3];
    (GOTO -12)  ;18  goto 18-12;           ; goto loop
    (ILOAD 1)   ;19
    (HALT)))    ;20  halt with factorial on top of stack;

; Note that the program computes the product of the naturals from
; 1 up to reg[0], leaving the product (aka factorial) in reg[1].
; Reg[3] is the constant +1 and the iteration replaces reg[2] by
; reg[2] + reg[3].

(defun program2p (s)
  (declare (xargs :stobjs (s)))
  (equal (rd :program s) *program2*))

(defthm program2p-preserved
  (implies (not (equal key :program))
           (equal (program2p (wr key v s))
                  (program2p s))))

(defthm len-program2p
  (implies (program2p s)
           (equal (len (rd :program s))
                  (len *program2*))))

(defthm resolve-next-inst1
  (implies (program2p s)
           (equal (nth i (rd :program s))
                  (nth i *program2*))))

(in-theory (disable program2p))

; We define the invariant we need for the loop.
; !! Perhaps other tools (e.g., Kestrel's CodeHawk) could supply this
; invariant.

(defun-nx loop-pc-p (s)

; Originally I used (< 3 (rd :pc s)) here.  But during clean-up, I realized
; that it's probably much more natural to specify the exact pc upon entering
; the loop.

  (= 6 (rd :pc s)))

(defun-nx inv (s)
  (and (< 0 (nth 0 (rd :locals s))) ; input is positive
       (implies (loop-pc-p s)
                (<= (nth 2 (rd :locals s))
                    (nth 0 (rd :locals s))))))

; For debugging:
; (set-iprint t)

(defun-nx clk-6-measure (s)
  (nfix (if (not (loop-pc-p s))
            (nth 0 (rd :locals s))
          (- (nth 0 (rd :locals s))
             (nth 2 (rd :locals s))))))

; !! The following hint works for the SEM-6 def-projection later in this file
; (thankfully, since there is no :annotations keyword for def-projection), but
; not for the def-semantics form just below -- it still needs its :annotations.

; !! Even if it did work, maybe it's unfortunate that it's not already known to
; Terminatrix.  We discussed the possibility that Terminatrix would come up
; already knowing about more common patterns, including this one; but you (J)
; said that you might need first to modify Terminatrix to avoid exploding in
; its tries of lexicographic combinations.

(defun hint1 (a b c)
  (declare (xargs :measure (nfix (- a b))))
  (if (and (natp a)
           (natp b)
           (<= b a)
           (equal c 1))
      (if (equal a b)
          5
        (hint1 a (+ b c) c)
;       (hint1 a (+ b 1) c)
;       (hint1 a (+ 1 b) c)
        )
    0))

(def-semantics
  :init-pc 0
  :focus-regionp nil
  :root-name nil
; !! I added force to help with debugging, but it's ultimately not necessary
; (neither here, nor in the def-projection for fn1-loop).
  :hyps+ ((program2p s)
          (force (inv s))
          (nat-listp (rd :locals s))
          (nat-listp (rd :stack s)))
  :annotations ((clk-6 (declare (xargs :measure (clk-6-measure s))))
                (sem-6 (declare (xargs :measure (clk-6-measure s)))))
  )

(def-projection
  :new-fn FN1-LOOP
  :projector (nth 1 (rd :locals s))
  :old-fn SEM-6
  :hyps+ ((program2p s)
; The next hyp is needed to avoid error: "We cannot determine the answer term."
; !! Is there a general method for dealing with such an error?  J's answer:
; probably the answer is to supply the fully loop invariant when doing
; def-projection for a loop function, which in this case would include
; (loop-pc-p s).  But J plans to look into doing something about the obscure
; error message, perhaps simply to improve it to suggest coming up with a
; suitable loop invariant (if that is indeed the issue in general with that
; error).
          (loop-pc-p s)
          (force (inv s))
          (nat-listp (rd :locals s))
          (nat-listp (rd :stack s)))
  )

(def-projection
  :new-fn FN1
  :projector (nth 1 (rd :locals s))
  :old-fn SEM-0
; Below we drop (inv s), which is good.  The general principle above sort
; of applies here: we're not in a loop, so there is no need for (inv s).
  :hyps+ ((program2p s)
          (nat-listp (rd :locals s))
          (nat-listp (rd :stack s)))
  )

#||
M1 !>(pe 'fn1)
          22:x(DEF-PROJECTION :NEW-FN FN1 ...)
              \
>L             (DEFUN FN1 (PC R0 R1 R2)
                      (COND ((OR (NOT (INTEGERP R2))
                                 (< R2 0)
                                 (NOT (INTEGERP PC))
                                 (< PC 0)
                                 (NOT (INTEGERP R0))
                                 (< R0 0)
                                 (NOT (INTEGERP R1))
                                 (< R1 0)
                                 (<= 21 PC))
                             0)
                            ((< 0 R0)
                             (COND ((< R0 R2)
                                    (COND ((EQUAL 6 PC) R1)
                                          ((EQUAL R0 1) 1)
                                          (T (FN1-LOOP R0 R0 2 1))))
                                   ((EQUAL R0 1) 1)
                                   (T (FN1-LOOP R0 R0 2 1))))
                            (T R1)))
M1 !>(pe 'fn1-loop)
          21  (DEF-PROJECTION :NEW-FN FN1-LOOP ...)
              \
>L             (DEFUN
                FN1-LOOP (R0 R1 R2 R3)
                (DECLARE
                   (XARGS :MEASURE
                          (ACL2::DEFUNM-MARKER (NFIX (+ (+ 1001 (- R2)) R0)))
                          :WELL-FOUNDED-RELATION O<))
                (COND ((OR (NOT (INTEGERP R3))
                           (< R3 0)
                           (NOT (INTEGERP R0))
                           (< R0 0)
                           (NOT (INTEGERP R2))
                           (< R2 0)
                           (NOT (INTEGERP R1))
                           (< R1 0)
                           (< R0 R2)
                           (<= R0 0))
                       0)
                      ((OR (NOT (EQUAL R3 1)) (EQUAL R0 R2))
                       R1)
                      (T (FN1-LOOP R0 (* R1 R2) (+ 1 R2) 1))))
M1 !>
||#

; We can prove that fn1 is factorial by the easy, conventional method:
; This part requires (minimal) human creativity.

(defun ! (n)
  (if (zp n)
      1
      (* n (! (- n 1)))))

(defthm fn1-loop-is-!-gen
  (implies (and (posp r0) (natp r1) (posp r2) (<= r2 r0))
           (equal (fn1-loop r0 r1 r2 1)
                  (/ (* r1 (! (1- r0)))
                     (! (1- r2))))))

(defthm fn1-is-!
  (implies (and (posp r0) (natp r1) (natp r2) (natp r3))
           (equal (fn1 0 r0 r1 r2)
                  (! r0))))

; Originally I stated fn1-loop-is-!-gen using * instead of /, and made it
; :rule-classes nil since it wasn't a useful rewrite rule for our purposes.  I
; needed :hints in that case, which leads to an idea:

; !! I can imagine generating the following hint automatically with hints
; provided by Codewalker, though ultimately it is the user's responsibility to
; do this (abstract) part of the reasoning.
#||
  :hints (("Goal" :use ((:instance fn1-loop-is-!-gen
                                   (r0 r0)
                                   (r1 r0)
                                   (r2 1)))))
||#

; !! Should something like the following be generated automatically?
; J thinks maybe so.
(in-theory (disable sem-0))

(defthm reg[1]-of-code-is-!
  (implies (and (hyps s)
                (program2p s)
                (nat-listp (rd :locals s))
                (nat-listp (rd :stack s))
                (posp (nth 0 (rd :locals s)))
                (equal (rd :pc s) 0))
           (equal (nth 1 (rd :locals (m1 s (clk-0 s))))
                  (! (nth 0 (rd :locals s))))))
