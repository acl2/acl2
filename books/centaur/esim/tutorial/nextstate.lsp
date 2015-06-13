; Centaur Hardware Verification Tutorial for ESIM/VL2014
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>
;
; NOTE: The tutorial starts with intro.lisp.

(in-package "ACL2")
(include-book "intro")

; nextstate.lsp

; This file gives some examples of very low-level/primitive ways to extract
; update functions from an ESIM module and work with them.  Most users will
; not want to look at this stuff.  We assume familiarity with using VL to
; translate modules and mostly intend this to be a starting off point...

;; Basic parsing and getting the *top* module defined.
(defmodules *translation*
  (vl2014::make-vl-loadconfig
   :start-files (list "nextstate.v")
   :edition :system-verilog-2012))

(defconst *top-vl*
  (vl2014::vl-find-module "top"
                          (vl2014::vl-design->mods
                           (vl2014::vl-translation->good *translation*))))

;; Inspect the top module if you like
(vl2014::vl-ppcs-module *top-vl*)

;; Get the corresponding ESIM module.
(defconst *top* (vl2014::vl-module->esim *top-vl*))

;; So what exactly is an ESIM module.  Each ESIM module has:
;;
;;   An input "pattern" that captures what the primary inputs are,
;;   An output "pattern" that says what the primary outputs are,
;;   A state "pattern" that explains the internal state in registers.
;;
;; You can read more about patterns in (xdoc 'patterns).  Let's look
;; at these patterns for *top*.  We can get the input pattern with:

(gpl :i *top*)

;; And the output pattern with:

(gpl :o *top*)

;; And the state pattern with the following.  This is much more complex and
;; ugly looking because the state of a module is recursively formed out of the
;; bits of the submodules.

(mod-state *top*)

;; The core functions of ESIM, which are used in STVs, etc., allow us to
;; simulate the ESIM module and obtain, for a single phase, the update
;; functions for all of the bits of the module.  Let's now do a very low-level
;; demo to explain how this works for *top*.
;;
;; The main function we are going to call in this demo is called:
;;
;;   (ESIM-SEXPR-SIMP-NEW-PROBE MOD IN ST) --> (NST OUT INT)
;;
;; This is an internal ESIM function that produces the steady-state expressions
;; for an ESIM module.  This function is normally called from higher-level
;; wrapper functions like ESIM-SEXPR-SIMP-NEW-PROBE-STEPS.  But here we will
;; call it directly, to learn how to work with it.
;;
;; Inputs:
;;   MOD is the ESIM module to simulate, e.g., *top*.
;;   IN is an alist binding the input names to initial 4v-sexprs.
;;   ST is an alist binding the state names to initial 4v-sexprs.
;;
;; Outputs:
;;   NST will be an alist binding state names to their update functions.
;;   OUT will be an alist binding output names to their update functions.
;;   INT will be an alist binding internal names to their update functions.
;;
;; At any rate, the first step to using this function will be to create a
;; suitable IN and ST to provide to it.


;; Our input alist, IN, should bind every input, i.e., every name in

(gpl :i *top*)

;; to a corresponding 4v-sexpr.  If you don't know about 4v-sexprs, you should
;; go read about them now.  They have good documentation and are the basis of
;; ESIM.  In most cases, for the primary inputs to our module, we will usually
;; want to supply either:
;;
;;   - Fresh variables, or
;;   - Particular constants.
;;
;; Let me begin with some stupid code to make fresh variables by just doing
;; some symbol mangling:

(define make-variable (basename &key (phase natp))
  (intern$ (str::cat (stringify basename) ".P" (str::natstr phase))
           "ACL2"))

;; Examples:
(make-variable 'foo :phase 0)
(make-variable 'foo :phase 5)

(define make-variables ((basenames true-listp) &key (phase natp))
  (if (atom basenames)
      nil
    (cons (make-variable (car basenames) :phase phase)
          (make-variables (cdr basenames) :phase phase))))

;; Examples:
(make-variables '(a b c) :phase 0)
(make-variables '(a b c) :phase 7)

;; So now if we wanted to supply fresh variables to our input alist, we could
;; do something like this:

(make-variables (pat-flatten1 (gpl :i *top*)) :phase 0)

;; These variables are valid 4v-sexpr variables (see the documentation for
;; 4v-sexprs for more details.  So, we could make a suitable in-alist by doing
;; something like this:

(defconst *inputs-for-phase0*
  (let ((flat-ins (pat-flatten1 (gpl :i *top*))))
    (pairlis$ flat-ins
              (make-variables flat-ins :phase 0))))

;; We can very similarly construct an initial state for our circuit:

(defconst *initial-state*
  (let ((flat-st (pat-flatten1 (mod-state *top*))))
    (pairlis$ flat-st
              (make-variables flat-st :phase 0))))

;; And now we can run our function to get the next states, etc.  NOTE: the next
;; states we produce are likely to be large, so it's a good idea to turn on some
;; kind of output evisceration here.

(plev-mid)  ;; Don't print too much

(defconsts (*state-after-phase0*     ;; State bits --> 4v-sexprs
            *outputs-after-phase0*   ;; State bits --> 4v-sexprs
            *internal-after-phase0*  ;; State bits --> 4v-sexprs
            )
  (esim-sexpr-simp-new-probe *top*               ;; Module to simulate
                             *inputs-for-phase0* ;; Input name <-- 4v-sexprs
                             *initial-state*     ;; State name <-- 4v-sexprs
                             ))

;; Take a look at the resulting variables.  You'll see they're just alists
;; binding wire names to 4v-sexprs.  Go ahead, take a look at these:

*state-after-phase0*
*outputs-after-phase0*
*internal-after-phase0*


;; OK, so how do we do anything with this.  Let's start by looking at
;; nextstate.v, where we see:
;;
;;    wire [3:0] stage1;
;;    myreg #(4) r1 (stage1, a & b, clk);
;;
;; The wire "stage1" isn't an input or an output, but we'll be able to find its
;; update functions in the internal signals alist.  For example, here is a way
;; to look up the update function for bit 0:

(cdr (assoc '|stage1[0]| *internal-after-phase0*))

;; This returns the following 4v-sexpr:
;;
;; (ITE* (AND |clk.P0|
;;            (NOT |r1!q_inst!bit0!clk_prev[0].P0|))
;;       |r1!q_inst!bit0!d_prev[0].P0|
;;       |r1!q_inst!bit0!q_prev[0].P0|)
;;
;; This looks scary but it actually makes good sense.  Basically it's just an
;; S-expression that says what the next value of stage1[0] is going to be.
;;
;;  - The functions involved in this particular expression are:
;;
;;      ITE* -- an If-Then-Else expression
;;      AND  -- an AND expression
;;      NOT  -- a NOT expression
;;
;;    In general, there aren't many 4v-sexpr functions, and they're all
;;    documented, see (xdoc '4v-operations) to get a feel for them, and see
;;    also (xdoc '4v-sexpr-eval) for the function symbols.
;;
;;  - The variables here are |clk.P0|, which is the clock variable we supplied
;;    during phase 0, and then a bunch of other bits---these awful looking
;;    r1!...  things, which are various initial state bits from within r1.
;;
;; For some intuition about what this is doing, this expression is looking for
;; (posedge clk).  How do we tell whether the clk has a posedge?  Well, we have
;; a posedge if the clock is currently HIGH and it was previously LOW.  The
;; current value of the clock is just |clk.P0|, and the previous value, uh,
;; doesn't exactly make sense, because we're sort of at the beginning of time.


;; Probably, for any kind of RTL-level circuit (not involving latches), you
;; don't want to think about a phase-based model.  Instead, you (might) want to
;; assume that you're going to hold your inputs for a whole cycle, and that the
;; clock will be toggling.  Fortunately, it's easy to get to a kind of
;; cycle-based model.
;;
;; First of all, let's decide on a clocking convention.  I'm going to say, just
;; because it's convenient, that the simulation is going to start with the
;; clock low.  Then, in the next phase, I'll make the clock go high.  So for
;; now, let me throw away all the previous work and start over:

(ubt! '*inputs-for-phase0*)

(defconst *inputs-for-phase0*
  ;; Almost like before, but this time override the clock signal with F.
  (let* ((flat-ins (pat-flatten1 (gpl :i *top*)))
         (main-alist (pairlis$ flat-ins (make-variables flat-ins :phase 0))))
    (cons (cons '|clk| (4vs-f))
          main-alist)))

(defconst *initial-state*
  ;; Like before.
  (let ((flat-st (pat-flatten1 (mod-state *top*))))
    (pairlis$ flat-st
              (make-variables flat-st :phase 0))))

(defconsts (*state-after-phase0*     ;; State bits --> 4v-sexprs
            *outputs-after-phase0*   ;; State bits --> 4v-sexprs
            *internal-after-phase0*  ;; State bits --> 4v-sexprs
            )
  (esim-sexpr-simp-new-probe *top*               ;; Module to simulate
                             *inputs-for-phase0* ;; Input name <-- 4v-sexprs
                             *initial-state*     ;; State name <-- 4v-sexprs
                             ))

;; We can now look at the new signal for stage1[0]:

(cdr (assoc '|stage1[0]| *internal-after-phase0*))

;; And we see that it is now only just:
;;
;;    (BUF |r1!q_inst!bit0!q_prev[0].P0|)
;;
;; In other words, it's going to hold its value from the previous state.  This
;; makes sense, because so far we've only set the clock to LOW, and that
;; certainly won't trigger a posedge.
;;
;; OK, so now let's supply a posedge.  At this point we have a choice to make:
;;
;;   - Do we want to allow the non-clock inputs to change before we let the
;;     clock go high?
;;
;; For an RTL design, it's very likely that the answer is NO, we just want to
;; work with a cycle-level semantics.  But for this example, let's suppose we
;; want this added flexibility.

(defconst *inputs-for-phase1*
  ;; This time we are going to:
  ;;   - Set the clock to TRUE instead of FALSE
  ;;   - Use .P1 variables instead of .P0 variables.
  (let* ((flat-ins (pat-flatten1 (gpl :i *top*)))
         (main-alist (pairlis$ flat-ins (make-variables flat-ins :phase 1))))
    (cons (cons '|clk| (4vs-t))
          main-alist)))

;; Let's now step the circuit.  The crucial thing to note here is that the
;; state produced by phase0 will become the input state for phase1:

(defconsts (*state-after-phase1*     ;; State bits --> 4v-sexprs
            *outputs-after-phase1*   ;; State bits --> 4v-sexprs
            *internal-after-phase1*  ;; State bits --> 4v-sexprs
            )
  (esim-sexpr-simp-new-probe *top*                ;; Module to simulate
                             *inputs-for-phase1*  ;; Input name <-- 4v-sexprs
                             *state-after-phase0* ;; State name <-- 4v-sexprs
                             ))

;; At this point, we've simulated one full cycle.  Moment of truth: what
;; is now in stage1[0]?:

(cdr (assoc '|stage1[0]| *internal-after-phase1*))

;; Answer:   (AND |a[0].P0| |b[0].P0|)
;;
;; Let's consider this for a moment.
;;
;; First off, hooray, we see our input signals instead of previous state stuff.
;; So the register got its posedge and it latched in some values.
;;
;; But now let's look more carefully.  Notice that these are .P0 signals
;; instead of .P1 signals(!!!!)  Why is that?  Does it seem right?  What does
;; it mean?
;;
;; The thing is, edges are really weird.  We sort of want them to happen
;; "between" phases.  But the ESIM timing model doesn't support that.  You
;; can think of ESIM's register timing model as a dumb sort of hack, where
;; changes in the clock signal are sort of assumed to happen "just before"
;; the other inputs in the phase.  For instance:
;;
;;                                  Register "sees" the clock change at
;;                                  the start of phase 1
;;                                  |
;;                                  v
;;                                   _______________   Other inputs to phase2
;;                                  |               |  |
;;    Clock                         |   ^           |  v
;;                   _______________|   .           |_______________ ...
;;                     ^                .           ^
;;                     .                .           Register sees clock go low,
;;                     .                .           starting phase 2
;;                     .                .
;;      Inputs to phase0                Other inputs to phase1 get their values
;;      are holding their               slightly after the clock
;;      values
;;
;; Because of this timing model, the phase1 inputs are going to turn out to be
;; completely irrelevant to our circuit.



;; At this point we might be done.  If you print the *internal-after-phase1*
;; alist, it is long but not too long.  You can see that the stage1 bits are
;; set as you would expect:

 ;; (|stage1[0]| AND |a[0].P0| |b[0].P0|)
 ;; (|stage1[1]| AND |a[1].P0| |b[1].P0|)
 ;; (|stage1[2]| AND |a[2].P0| |b[2].P0|)
 ;; (|stage1[3]| AND |a[3].P0| |b[3].P0|)

;; You can also see that the stage2 bits are the negations of the phase1 bits
;; from the initial state (which makes sense since this is a pipeline).

 ;; (|stage2[0]| NOT |r1!q_inst!bit0!q_prev[0].P0|)
 ;; (|stage2[1]| NOT |r1!q_inst!bit1!q_prev[0].P0|)
 ;; (|stage2[2]| NOT |r1!q_inst!bit2!q_prev[0].P0|)
 ;; (|stage2[3]| NOT |r1!q_inst!bit3!q_prev[0].P0|)

;; And that the stage3 bits are some complicated expressions that involve the
;; other previous bits.  You can use functions like 4v-sexpr-restrict-with-rw
;; to simplify these down and give them other names.

;; If you want to get rid of these initial state bits, since this is basically
;; a pipelined module, you can just run it for enough cycles.  A convenient
;; function for doing this is
;;
;;  ESIM-SEXPR-SIMP-NEW-PROBE-STEPS
;;
;; Which just automates the process of running the module over and over on new
;; inputs.  We might craft suitable inputs like this:

(defun inputs-for-cycle (n)
  (let* ((flat-ins (pat-flatten1 (gpl :i *top*)))
         (main-alist (pairlis$ flat-ins (make-variables flat-ins :phase n)))
         (low-alist  (cons (cons '|clk| (4vs-f)) main-alist))
         (high-alist (cons (cons '|clk| (4vs-t)) main-alist)))
    (list low-alist high-alist)))

(defun inputs-for-n-cycles (n)
  (if (zp n)
      nil
    (let ((n (- n 1)))
      (append (inputs-for-n-cycles n)
              (inputs-for-cycle n)))))

;; It makes lists of inputs in the right order, with clocks toggling low then
;; high:
(inputs-for-n-cycles 4)

;; We can then run the circuit for 8 phases (4 cycles) like this:

(defconsts (*state-after-each-phase*
            *outputs-after-each-phase*
            *internal-after-each-phase*
            )
  (esim-sexpr-simp-new-probe-steps *top*
                                   (inputs-for-n-cycles 4)
                                   *initial-state*))

;; And by the end of all of that, we should be in good shape with all initial
;; state bits taken care of.  For instance, we can look at the outputs after
;; the fourth cycle and see that they're in terms of input variables from the
;; previous cycles, with no initial state bits:

(car (last *outputs-after-each-phase*))

;; We can, of course, evaluate these outputs for some choice of inputs over
;; time.  For instance:

(4v-sexpr-restrict-with-rw-alist
 ;; Reduce the final outputs...
 (car (last *outputs-after-each-phase*))
 ;; Under the assumption that in cycle 1, A was 15 and B was 0.
 (make-fast-alist `((|a[0].P1| . ,(4vs-t))
                    (|a[1].P1| . ,(4vs-t))
                    (|a[2].P1| . ,(4vs-t))
                    (|a[3].P1| . ,(4vs-t))

                    (|b[0].P1| . ,(4vs-t))
                    (|b[1].P1| . ,(4vs-t))
                    (|b[2].P1| . ,(4vs-t))
                    (|b[3].P1| . ,(4vs-t))
                    )))

;;  --> Result is that all outputs are F


(4v-sexpr-restrict-with-rw-alist
 ;; Reduce the final outputs...
 (car (last *outputs-after-each-phase*))
 ;; Under the assumption that in cycle 1, A was 15 and B was 00??.
 (make-fast-alist `((|a[0].P1| . ,(4vs-t))
                    (|a[1].P1| . ,(4vs-t))
                    (|a[2].P1| . ,(4vs-t))
                    (|a[3].P1| . ,(4vs-t))

                    ;; Don't assume anything about b[0] and b[1] during Cycle 1
                    ;;(|b[0].P1| . ,(4vs-t))
                    ;;(|b[1].P1| . ,(4vs-t))
                    (|b[2].P1| . ,(4vs-t))
                    (|b[3].P1| . ,(4vs-t))
                    )))

;; --> Resulting expressions aren't fully reduced, still involve b[0] and b[1]
;; from Cycle 1.



;; This is all very primitive.  STV's are, of course, a much more user-level
;; tool.  VL2014 stores a bunch of information in the E module, e.g., try this:

(gpl :a *top*)

;; These mappings are meant to support translating things from E back up to the
;; Verilog level.  You might especially look at soe of the functions that
;; support STVs, such as the Verilog name lookups and vectorization stuff.

;; Beyond that, there are many tools for manipulating 4v-sexprs, e.g., you can
;; compose them, evaluate them, partially evaluate (restrict) them, etc.  You
;; can also convert them into FAIGs and from there pass them off to tools like
;; SAT solvers.  See the 4v-sexpr library for much more.




