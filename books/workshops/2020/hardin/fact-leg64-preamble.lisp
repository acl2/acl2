; Copyright (C) 2020 David S. Hardin
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
;                                        ;
; Based on demo-fact-preamble.lisp
; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is extracted from the first part of demo-fact.lisp, so that it can
; be included not only there, but also in demo-fact-partial.lsp.

(in-package "RTL")

(include-book "projects/codewalker/codewalker" :dir :system) ; codewalker source
(include-book "leg64-aux") ; RAC-generated leg64 model
(set-verify-guards-eagerness 0)


; Step 1 of Codewalker Methodology: Develop the canonical forms of the
; independently readable/writeable state components and the lemmas necessary to
; do code proofs in the model.

; We define hyps, which is the ``good state'' invariant for the processor model, and
; we prove several conventional lemmas allowing us to reason about individual
; state components from the invariant.  This invariant omits discussion of the
; program component of s, so that we can use the same API with different
; programs, as shown later below.

(encapsulate
 nil

 (defun hyps (s)
;;   (declare (xargs :stobjs (s)))
   (and (< (ag 'PC s) (len (ag 'CMEM s)))
        ))
)

; Since we're in the RTL package, it is convenient to define
; these macros.

(defmacro def-model-api (&rest x) `(acl2::def-model-api ,@x))
(defmacro def-semantics (&rest x) `(acl2::def-semantics ,@x))
(defmacro def-projection (&rest x) `(acl2::def-projection ,@x))


; Next, we tell Codewalker what the state component accessors/updaters are, and
; their types.

(def-model-api
  :run LEG64STEPN
  :svar S
  :stobjp nil
  :hyps nil ;;((HYPS S))
  :step LEG64STEP
  :get-pc (LAMBDA (S) (ag 'PC S))
  :put-pc (LAMBDA (V S) (as 'PC V S))
  :updater-drivers (((as 'CMEM :VALUE :BASE)
                    (ag 'CMEM :BASE))
                    ;;((as I :VALUE (ag 'CMEM :BASE))
                    ;; (ag I (ag 'CMEM :BASE)))
                    ((as I :VALUE (ag 'REGS :BASE))
                     (ag I (ag 'REGS :BASE)))
                    ((as I :VALUE (ag 'DMEM :BASE))
                     (ag I (ag 'DMEM :BASE)))
                    ((as 'PC :VALUE :BASE) (ag 'PC :BASE))
                    ;;((as 'ERR :VALUE :BASE) (ag 'ERR :BASE))
                    )
  :constructor-drivers nil
  :state-comps-and-types  (((ag I (ag 'REGS S)) (natp (ag I (ag 'REGS S))))
                           ((ag I (ag 'DMEM S)) (natp (ag I (ag 'DMEM S))))
                           ((ag 'CMEM S) (alistp (ag 'CMEM S)))
                           ;;((ag I (ag 'CMEM S)) (natp (ag I (ag 'CMEM S))))
                           ((ag 'PC S)            (NATP (ag 'PC S)))
                           )
  :callp  nil
  :ret-pc nil
  :returnp nil
  :clk+ binary-+
  :name-print-base nil
  :var-names (((ag 'PC S) "PC")
              ((ag 'CMEM S) "CMEM")
              ;;((ag I (ag 'CMEM S)) "CMEM~x0" I)
              ((ag I (ag 'REGS S)) "REGS~x0" I)
              ((ag I (ag 'DMEM S)) "DMEM~x0" I)
              )
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

(defconst *fact-routine*
  '((0 . 117440512)      ;; (CMPI 0 0)      .L3  cmp(r0, 0)
    (1 . 285409280)      ;; (BEQ .L2)            if ==, branch to .L2
    (2 . 184615168)      ;; (MUL 1 1 0)          r1 <- r1 * r0
    (3 . 218103809)      ;; (SUBI 0 0 1)         r0 <- r0 - 1
    (4 . 284884992)      ;; (B .L3)              branch to .L3
    (5 . 67109120)       ;; (ADDI 0 1 0)    .L2  r0 <- r1
    (6 . 33554432)))     ;; (HALT 0 0 0)         halt

; Note that the program computes the product of the naturals from
; reg[0] down to 0, leaving the product (aka factorial), multiplied
; by the initial value of the accumulator reg[1].
; The product in reg[1] is copied to reg[0] at the end of the routine.
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

(defun fact-routine-loadedp (s)
  (equal (ag 'CMEM s) *fact-routine*))

(defthm fact-routine-loadedp-preserved
  (implies (not (equal key 'CMEM))
           (equal (fact-routine-loadedp (as key v s))
                  (fact-routine-loadedp s))))

(defthm len-fact-routinep
  (implies (fact-routine-loadedp s)
           (equal (len (ag 'CMEM s))
                  (len *fact-routine*))))

(defthm resolve-next-inst1
 (implies (fact-routine-loadedp s)
          (equal (ag i (ag 'CMEM s))
                 (ag i *fact-routine*))))

(in-theory (disable fact-routine-loadedp))

;; Measure function for the loop
