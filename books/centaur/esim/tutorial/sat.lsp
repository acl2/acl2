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


; sat.lsp
;
; This example explains how to use our new AIGNET/SATLINK combination as the
; back-end solver for GL, instead of BDDs, to solve problems from the ALU16
; example from earlier in the tutorial.

(in-package "ACL2")


; -----------------------------------------------------------------------------
;
;                            PRELIMINARY SETUP
;
; -----------------------------------------------------------------------------

; Setup as before (see alu16.lsp for explanation and commentary):

(include-book "intro")
(plev)
(set-slow-alist-action :break)
(set-debugger-enable t)
(break-on-error t)
(value-triple (set-max-mem (* 3 (expt 2 30))))

; There are three additional basic setup steps:

; 1. GL's SATLINK mode is not included by default in the GL books because it
; depends on several trust tags.  These trust tags are necessary for, e.g.,
;
;   (1) writing out files to give to the SAT solver,
;   (2) the logical story for trusting the SAT solver,
;   (3) having hash tables in stobjs (for strashing in AIGNET),
;   (4) various Common Lisp optimizations for AIG/AIGNET operations.
;
; Long story short: we have to load an extra book.

(include-book "centaur/gl/bfr-satlink" :dir :system)

; 2. SATLINK does not directly call the SAT solver using sys-call.  Instead, it
; invokes the solver through a subsidiary BASH process, called TSHELL; for
; details see centaur/misc/tshell.lisp.  This has a number of very nice
; features, for instance:
;
;   (1) it actually works when you have tens of GB allocated, whereas
;       calling sys-call dies with a horrible segfault.
;   (2) it allows you to interrupt the SAT solver in interactive sessions,
;       and then give commands like :go and :q, etc.
;
; For TSHELL to work, we have to start its BASH shell.  You can put this form
; in a value-triple to embed it in books.  The tshell will be started using
; sys-call, so ideally you want to do this early in your session, before you've
; allocated tons of memory, to avoid the setfault problem.

(tshell-ensure)

; 3. Finally, loading the above book merely makes SATLINK mode available as an
; option, but by default GL will still try to use BDDs.  Here is how we can
; tell GL to use AIGNET/SATLINK:

(gl::gl-satlink-mode)

; Note that you can easily switch the GL mode from proof to proof.  If you want
; to go back to BDD mode, just run:

(gl::gl-bdd-mode)

; And to go back to SATLINK mode:

(gl::gl-satlink-mode)

; You can do this however many times you need; they're just reconfiguring some
; attached functions.


; -----------------------------------------------------------------------------
;
;                            SAT SOLVER SETUP
;
; -----------------------------------------------------------------------------

; To follow this tutorial you will need one (or more!) DIMACS-compatible SAT
; solvers installed on your system.
;
; For information on how to get a SAT solver and what solvers we currently
; recommend, please see
;
;     :XDOC SATLINK::SAT-SOLVER-OPTIONS
;
; The particular SAT solver that SATLINK will call, and other options about,
; e.g., what kind of debugging information will be printed, whether temporary
; files should be removed, etc., are governed by a configuration object.  For
; details, see :XDOC satlink::config-p.  GL will use whatever configuration is
; returned by:

(gl::gl-satlink-config)

; Here are some examples of how to define new Satlink configurations.  We'll
; always turn :verbose on here, so we can see the SAT solvers working.

(defun my-glucose-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "glucose"
                        :verbose t
                        :mintime 1/2
                        :remove-temps t))

(defun my-lingeling-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "lingeling"
                        :verbose t
                        :mintime 1/2
                        :remove-temps t))

(defun my-glucose-cert-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "glucose-cert"
                        :verbose t
                        :mintime 1/2
                        :remove-temps t))

; You should be able to easily adapt these examples to call any other SAT
; solver that you would like to use.  When doing so, it's a good idea to run a
; really quick check that your SAT solver configuration seems to be working.
; Satlink includes a check-config command that you can use for this.  For
; example, if the above solvers are installed on your system, you can try
; running:

(include-book "centaur/satlink/check-config" :dir :system)
(satlink::check-config (my-glucose-config))
(satlink::check-config (my-lingeling-config))
(satlink::check-config (my-glucose-cert-config))


; Now, for GL's integration with Satlink, we can switch between these
; configurations (and the default configuration) using defattach.  For
; instance:

(defattach gl::gl-satlink-config my-glucose-config)

; While this attachment is active, GL will call Glucose to carry out the proof.
; If we want to, say, switch to Lingeling for some other particular proof, we
; just set up a new attachment, e.g.,:

(defattach gl::gl-satlink-config my-lingeling-config)

; Or with glucose-cert...

(defattach gl::gl-satlink-config my-glucose-cert-config)

; And so forth.


; -----------------------------------------------------------------------------
;
;                  ENOUGH SETUP, LET'S USE THIS STUFF!
;
; -----------------------------------------------------------------------------

; Basic stuff copied from alu16.lsp to get the Verilog module loaded:

(defmodules *translation*
  (vl2014::make-vl-loadconfig
   :start-files (list "alu16.v")))

(defconst *alu16-vl*
  (vl2014::vl-find-module "alu16"
                      (vl2014::vl-design->mods
                       (vl2014::vl-translation->good *translation*))))

(defconst *alu16*
  (vl2014::vl-module->esim *alu16-vl*))

(defstv test-vector         ;; name for this test vector
  :mod *alu16*              ;; the module this vector pertains to
  :inputs
  '(("opcode" op)           ;; verilog name --> inputs we are going to supply
    ("abus"   a)            ;;                  at each phase
    ("bbus"   b))           ;; we only have one phase, so we'll just supply a
                            ;; variable for each vector (note that we do not
                            ;; yet need to specify anything related to the
                            ;; length of the vectors).

  :outputs                  ;; verilog name --> variable names we will use
  '(("out"    res)))

(defconst *op-plus*    0)
(defconst *op-minus*   1)
(defconst *op-bitand*  2)
(defconst *op-bitor*   3)
(defconst *op-bitxor*  4)
(defconst *op-min*     5)
(defconst *op-count*   6)
(defconst *op-mult*    7)


; Alright.  Now, if you remember from the alu16 tutorial, this proof took about
; 15 seconds to prove using BDDs because we chose a bad variable ordering.
; Fortunately, the variable ordering is basically unimportant for SAT solvers.
; Lingeling and Glucose can both solve this in under .1 seconds, i.e., they're
; competitive with the "good" variable ordering for BDDs.

(def-gl-thm very-badly-done-proof-that-alu16-adds
  :hyp (and (unsigned-byte-p 3 op)
            (unsigned-byte-p 16 a)
            (unsigned-byte-p 16 b)
            (equal op *op-plus*))
  :concl (let* ((in-alist (list (cons 'op op)
                                (cons 'a  a)
                                (cons 'b  b)))
                (out-alist (stv-run (test-vector) in-alist))
                (res       (cdr (assoc 'res out-alist))))
           (equal res (mod (+ a b) (expt 2 16))))
  :g-bindings (gl::auto-bindings (:nat op 3)
                                 (:nat a 16)
                                 (:nat b 16)))


; I'll go ahead and do the rest of the proofs from alu16.lsp

(defmacro alu16-basic-result ()
  `(let* ((in-alist  (test-vector-autoins))
          (out-alist (stv-run (test-vector) in-alist))
          (res       (cdr (assoc 'res out-alist))))
     res))

(defmacro alu16-default-bindings ()
  `(gl::auto-bindings (:nat op 3)
                      (:mix (:nat a 16)
                            (:nat b 16))))

(defmacro alu16-thm (name &key opcode spec (g-bindings '(alu16-default-bindings)))
  `(def-gl-thm ,name
     :hyp (and (test-vector-autohyps)
               (equal op ,opcode))
     :concl (equal (alu16-basic-result) ,spec)
     :g-bindings ,g-bindings))

; I'll do these ones with Glucose:

(defattach gl::gl-satlink-config my-glucose-config)

(alu16-thm another-proof-that-alu16-adds
           :opcode *op-plus*
           :spec (mod (+ a b) (expt 2 16)))

(alu16-thm alu16-minus-correct
           :opcode *op-minus*
           :spec (mod (- a b) (expt 2 16)))

(alu16-thm alu16-bitand-correct
           :opcode *op-bitand*
           :spec (logand a b))

(alu16-thm alu16-bitor-correct
           :opcode *op-bitor*
           :spec (logior a b))

; I'll do these ones with Lingeling:

(defattach gl::gl-satlink-config my-lingeling-config)

(alu16-thm alu16-bitxor-correct
           :opcode *op-bitxor*
           :spec (logxor a b))

(alu16-thm alu16-min-correct
           :opcode *op-min*
           :spec (min a b))


; Now we get to the failed proof for COUNT.
;
; This is more interesting because here we actually have the satisfying
; assignment involved.  Let's try it with Glucose first:

(defattach gl::gl-satlink-config my-glucose-config)

(alu16-thm alu16-count-correct
           :opcode *op-count*
           :spec (logcount a))

; The SAT solver finds a counterexample, which gets checked (by Satlink), then
; translated back through our CNF conversion, AIGNET conversion, and GL
; symbolic simulation into an ordinary ACL2-level GL counterexample:

;; Example 1, counterexample from SAT:
;; Assignment:
;; ((OP 6) (A 1054) (B 0))
;;
;; Running conclusion:
;; STV Raw Inputs: ((OP . 6) (A . 1054) (B . 0)).
;;
;; STV Inputs:
;;   OP:               #ux6
;;   A:                #ux41E
;;   B:                #ux0
;;
;; STV Outputs:
;;   RES:              #ux6
;;
;; Result: NIL

; Pretty slick, eh?  A disadvantage of SAT, compared to BDDs, is that we only
; end up with one, "random" counterexample.  With BDDs, we can get sort of
; "mostly 0" and "mostly 1" counterexamples that can be a lot nicer to debug.
; This is just sort of fundamental to how SAT works.

; Let's try the same thing with Lingeling.

(defattach gl::gl-satlink-config my-lingeling-config)

(alu16-thm alu16-count-correct
           :opcode *op-count*
           :spec (logcount a))

; Lingling finds a different counterexample:

;; Example 1, counterexample from SAT:
;; Assignment:
;; ((OP 6) (A 42673) (B 0))
;;
;; Running conclusion:
;; STV Raw Inputs: ((OP . 6) (A . 42673) (B . 0)).
;;
;; STV Inputs:
;;   OP:               #ux6
;;   A:                #uxA6B1
;;   B:                #ux0
;;
;; STV Outputs:
;;   RES:              #ux7
;;
;; Result: NIL




; And that just leaves the multiplier proof.
;
; Compared to BDDs, a nice property of SAT is that it tends to use considerably
; less memory.  And, at any rate, the memory that the solver is going to use is
; separate from the memory that ACL2 uses, so there's really no need to mess
; with memory sizes here or to increase the size of the HONS tables.

(defattach gl::gl-satlink-config my-glucose-config)

; Historically, VL generated multipliers in a different way, and this proof was
; much harder.  In the old scheme, I tried this on Glucose 2.1 and Lingeling,
; and on my machine Glucose finished the proof in 8680 seconds, which was
; considerably slower than BDDs, but used very little memory; Lingeling was
; unable to finish the proof within 24 hours.
;
; Today, VL generates a multiplier that matches the GL multiplier, so this
; proof is instantaneous (and trivial) on any SAT solver:

(alu16-thm alu16-mult-correct
           :opcode *op-mult*
           :spec (logand (* a b) (1- (expt 2 16))))

; However, this is still a very hard proof, because the multiplier
; implementations don't line up.

(alu16-thm alu16-reverse-mult-correct
           :opcode *op-mult*
           :spec (logand (* b a) (1- (expt 2 16))))

