; Centaur Hardware Verification Tutorial
; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
;
; NOTE: The tutorial starts with intro.lisp.



; alu16.lsp
;
; This is the first example in the tutorial.  We are going to try to verify a
; basic 16-bit ALU module that implements 8 opcodes.  We will discover that
; there is a bug in its COUNT operation.
;
; This is a .lsp file instead of a .lisp file because we have several
; non-embeddable events.  But you could take them out, or put them in
; value-triple forms, or similar in order to turn this into a proper book that
; can be certified by ACL2 as usual.  (Usually our proof scripts are
; certifiable books, so we can just use cert.pl to run them.)

(in-package "ACL2")



; -----------------------------------------------------------------------------
;
;                            PRELIMINARY SETUP
;
; -----------------------------------------------------------------------------

; This include-book loads all the libraries we're going to use.  This takes
; quite awhile.  In practice, we often build an ACL2 image that has these
; libraries pre-loaded, and use that image to carry out our proofs; see :DOC
; SAVE-EXEC for more information about how to save images.

(include-book "intro")

; This will allow us to use the waveform debugging features
(install-vcd-dump)

; The PLEV (print level) tool lets you control how much output ACL2 prints when
; it tries to print an object.  It is very important to be able to control the
; print level when you want to inspect things like translations, hardware
; modules, symbolic test vectors, etc.  Without (plev) ACL2 can end up just
; printing millions of lines of output at you.  See :XDOC PLEV for more
; information.
(plev)

; Debugger configuration.  These are optional commands that we generally use to
; enable the interactive debugger.  It's often very useful to get backtraces
; with :b when you interrupt.  On the other hand, this configuration can be
; very irritating when you are doing ordinary ACL2 proofs, especially the
; break-on-error command!
(set-slow-alist-action :break)
(set-debugger-enable t)
(break-on-error t)

; Memory configuration.  The set-max-mem command sort of gives the Lisp a soft
; hint as to when to GC.  For this example we don't need very much memory, so
; lets set up a 3 GB threshold.  Putting this in a value-triple makes it an
; embeddable event.
(value-triple (set-max-mem (* 3 (expt 2 30))))



; -----------------------------------------------------------------------------
;
;                        LOADING THE ALU16 MODULE
;
; -----------------------------------------------------------------------------

; The file alu16.v contains a very simple ALU module that we will verify.
;
; Our first task is to build a model of this Verilog code.  A convenient way to
; do this is with VL's DEFMODULES command.  This command has many options
; (e.g., for search paths, include dirs, etc.), which you can read about via
; :XDOC DEFMODULES.  Since we just want to read a single file and don't need to
; load libraries, etc., our use is very simple:

(defmodules *translation*
  :start-files (list "alu16.v"))

; This *translation* object is a data structure that contains all sorts of
; things.  It has "simplified VL modules" that were derived from the Verilog
; code, warnings, a list of `defines that were encountered, the actual source
; code that was read from each file, etc.
;
; If you ask ACL2 to print *translation*, you will see that several parts of it
; are hidden.  This is because of the (plev) command we issued above, and it is
; really a very good thing.  If you disable plev, e.g., by typing (plev-max),
; and ask ACL2 to print *translation*, then you will end up with over 100,000
; lines of output, and it will probably take over a minute.  PLEV protects you
; from this kind of thing.
;
; The DEFMODULES command prints some commentary as it runs.  One of the things
; it says is:
;
;    Finished parsing 1 files; found 1 modules.
;    Beginning simplification of 1 modules.
;    Successfully simplified 30 module(s).
;    Failed to simplify 0 modules.
;
; How can DEFMODULES have "successfully simplified 30 modules" when it only
; parsed a single module?  The answer is that VL's simplification process will
; generate several supporting modules.  We can pretty-print the list of
; simplified modules with the following command.  PPCS stands for "pretty print
; with comments to string."

(vl::vl-ppcs-modulelist (vl::vl-translation->mods *translation*))

; Here, you will find modules with names like VL_1_BIT_AND, VL_1_BIT_OR, etc.,
; until we finally get to the alu16 module.
;
; You'll also see that the alu16 module printed back to us here looks quite
; different than the module we wrote in alu16.v.  Many temporary wires have
; been introduced and the assignments and expressions have all been replaced by
; instances of these supporting modules.  This is the "simplification" that VL
; has done to rewrite the module into a small fragment of Verilog.




; Since the supporting modules are not very interesting, let's just consider
; alu16.  The following command just looks up the simplified version of "alu16"
; from *translation*, and names it *alu16-vl*.

(defconst *alu16-vl*
  (vl::vl-find-module "alu16" (vl::vl-translation->mods *translation*)))


; This *alu16-vl* object is a "VL Module."  VL modules are the internal, parsed
; representation of Verilog modules that VL uses; see :XDOC VL::VL-MODULE-P for
; more details.  We won't look at this object in much detail, but one thing we
; can do is pretty-print it:

(vl::vl-ppcs-module *alu16-vl*)

; We can also see a list of any warnings that are associated with this
; particular module (omitting any warnings for its submodules).  The warning it
; prints is a "minor" warning and really is not a problem, since in this case
; the LHS is expected to play a role in the expression's size.  The warning
; could be suppressed in various ways, e.g., we could add a 16'b0 to the sum.

(vl::vl-warnings-to-string (vl::vl-module->warnings *alu16-vl*))



; -----------------------------------------------------------------------------
;
;                         RUNNING THE ALU16 MODULE
;
; -----------------------------------------------------------------------------

; The *translation* object above includes an E module representation for each
; module.  E is a simple, bit-level, hierarchical hardware description
; language.  It is our main internal representation of hardware modules.  We
; can symbolically simulate E modules using ESIM.
;
; We can extract the E module associated with *alu16-vl* as follows:

(defconst *alu16*
  (vl::vl-module->esim *alu16-vl*))


; There are many ways to run an E module.  One of the nicest ways is to use a
; Symbolic Test Vector (STV).  STVs allow you to work at the Verilog level,
; i.e., provide inputs for whole busses rather than single bits, describe
; multi-phase simulations, and generate debugging waveforms.  They also hide
; pretty much all of the details of how ESIM works.


; Since our ALU16 module is purely combinational, we do not need many of the
; features that STVs offer (e.g., being able to run the module for several
; cycles).  But we will use them anyway, because they are easy and convenient.
; In this case, our STV is just:

(defstv *test-vector*       ;; name for this test vector
  :mod *alu16*              ;; the module this vector pertains to
  :inputs
  '(("opcode" op)           ;; verilog name --> inputs we are going to supply
    ("abus"   a)            ;;                  at each phase
    ("bbus"   b))           ;; we only have one phase, so we'll just supply a
                            ;; variable for each vector.

  :outputs                  ;; verilog name --> variable names we will use
  '(("out"    res)))


; With this STV defined, we can try running it on concrete inputs.  But we will
; need to supply the right opcodes.  For this tutorial, we'll just manually
; recreate the list of opcodes that are in alu16.v.
;
; If we were doing a more serious verification project, we could extract the
; `defines from the Verilog automatically.  The *translation* object records
; the defines that were encountered; see also :XDOC VL::VL-DEFINES-P.

(defconst *op-plus*    0)
(defconst *op-minus*   1)
(defconst *op-bitand*  2)
(defconst *op-bitor*   3)
(defconst *op-bitxor*  4)
(defconst *op-min*     5)
(defconst *op-count*   6)
(defconst *op-mult*    7)

; We can use STV-RUN to run the test vector on particular input alists.  The
; input alists need to give values for the input variables of the vector, i.e.,
; OP, A, and B.

(stv-run *test-vector*
         `((op . ,*op-plus*)
           (a  . 5)
           (b  . 3)))

; As you can see, the output is provided as an ALIST of values for the STV's
; output variables.  In this case we see that RES has value 8, so the circuit
; added 5 and 3 correctly.
;
; By default STV-RUN prints lots of debugging info.  We'll see below that this
; is very useful in theorems.  But when we're just doing concrete runs, this
; output can be irritating.  You can turn it off by adding :quiet t, like this:

(stv-run *test-vector*
         `((op . ,*op-mult*)
           (a  . 5)
           (b  . 3))
         :quiet t)

; If you have installed GTKWave and configured your PATH so that you can run
; it by typing "gtkwave", then you can also generate a waveform:

(stv-debug *test-vector*
           `((op . ,*op-min*)
             (a  . 5)
             (b  . 3)))

; Note that you can also supply X values, and that X values can propagate
; through the circuit.  For instance, this produces the result X:

(stv-run *test-vector*
         `((op . ,*op-plus*)
           (a  . X)
           (b  . 3)))

; But an X doesn't always flow through the circuit.  For instance, the COUNT
; operation pays no attention to its B bus, so you can send an X in, and still
; it will count the 8 bits of A:

(stv-run *test-vector*
         `((op . ,*op-count*)
           (a  . #xFF00)
           (b  . X)))

; Leaving out an input is equivalent to setting it to X:

(stv-run *test-vector*
         `((op . ,*op-count*)
           (a  . #xFF00)))



; -----------------------------------------------------------------------------
;
;                     PROVING SOME CORRECTNESS PROPERTIES
;
; -----------------------------------------------------------------------------

; Now let's do some proofs to show that ALU16 carries out its operations
; correctly.  We'll make use of an auxilliary function for recognizing n-bit
; natural numbers "vectors":

(defun vecp (n x)
  (and (natp x)
       (<= 0 x)
       (< x (expt 2 n))))

; We are going to use GL to do these proofs.  You can read an introduction to
; GL in the following paper:
;
;   Sol Swords and Jared Davis.  Bit-Blasting ACL2 Theorems.  ACL2 Workshop
;   2011.  November, 2011.  EPTCS 70.  Pages 84--102.
;     http://eptcs.org/content.cgi?ACL22011



; Here is a proof that ALU16 adds correctly modulo 2^16 when it is given the
; PLUS opcode.  To illustrate a few things you need to be aware of, I have done
; this proof in an especially bad way, and because of this it takes almost 15
; seconds on my computer!

(def-gl-thm very-badly-done-proof-that-alu16-adds

  ;; Hypothesis: OP, A, and B are bit-vectors of the appropriate sizes, and
  ;; furthermore OP is the PLUS opcode.
  :hyp (and (vecp 3 op)
            (vecp 16 a)
            (vecp 16 b)
            (equal op *op-plus*))

  ;; Conclusion: Suppose we construct an IN-ALIST from OP, A, and B, and run
  ;; the test-vector using these inputs.  Then the result RES must be exactly
  ;; equal to the sum of A and B, modulo 2^16.
  :concl (let* ((in-alist (list (cons 'op op)
                                (cons 'a  a)
                                (cons 'b  b)))
                (out-alist (stv-run *test-vector* in-alist))
                (res       (cdr (assoc 'res out-alist))))
           (equal res (mod (+ a b) (expt 2 16))))

  ;; G-bindings are needed by GL to know how to represent OP, A, and B.  The
  ;; AUTO-BINDINGS feature nicely allows you to assign successive indices to
  ;; fixed width signed (:int) and unsigned (:nat) variables.  We'll just use
  ;; appropriately sized OP, A, and B variables.
  :g-bindings (gl::auto-bindings (:nat op 3)
                                 (:nat a 16)
                                 (:nat b 16)))



; Now, 15 seconds is a lot of time for a proof of such a simple circuit.  We
; can get much better performance by interleaving the bits of A and B.  This
; proof finishes in under a tenth of a second.  As a general rule, you need to
; be careful to pick a good BDD order.  See the GL paper for more discussion.

(def-gl-thm better-proof-that-alu16-adds

  ;; Same as above.
  :hyp (and (vecp 3 op)
            (vecp 16 a)
            (vecp 16 b)
            (equal op *op-plus*))

  ;; Same as above.
  :concl (let* ((in-alist (list (cons 'op op)
                                (cons 'a  a)
                                (cons 'b  b)))
                (out-alist (stv-run *test-vector* in-alist))
                (res       (cdr (assoc 'res out-alist))))
           (equal res (mod (+ a b) (expt 2 16))))

  ;; Interleave the bits of A and B, since they're going to be added together.
  :g-bindings (gl::auto-bindings (:nat op 3)
                                 (:mix (:nat a 16)
                                       (:nat b 16))))



; At this point we'd like to verify the rest of the operations.  The proofs
; share so much in common that macros become very useful:


(defmacro alu16-type-hyps ()
  `(and (vecp 3 op)
        (vecp 16 a)
        (vecp 16 b)))

(defmacro alu16-default-bindings ()
  `(gl::auto-bindings (:nat op 3)
                      (:mix (:nat a 16)
                            (:nat b 16))))

(defmacro alu16-basic-result ()
  `(let* ((in-alist (list (cons 'op op)
                          (cons 'a  a)
                          (cons 'b  b)))
          (out-alist (stv-run *test-vector* in-alist))
          (res       (cdr (assoc 'res out-alist))))
     res))

(defmacro alu16-thm (name &key opcode spec (g-bindings '(alu16-default-bindings)))
  `(def-gl-thm ,name
     :hyp (and (alu16-type-hyps)
               (equal op ,opcode))
     :concl (equal (alu16-basic-result) ,spec)
     :g-bindings ,g-bindings))


; With this little bit of macro support, the proof of ALU16 adding can be
; written quite concisely:

(alu16-thm another-proof-that-alu16-adds
           :opcode *op-plus*
           :spec (mod (+ a b) (expt 2 16)))


; Now let's use the same macro to finish out some of the other operations:

(alu16-thm alu16-minus-correct
           :opcode *op-minus*
           :spec (mod (- a b) (expt 2 16)))

(alu16-thm alu16-bitand-correct
           :opcode *op-bitand*
           :spec (logand a b))

(alu16-thm alu16-bitor-correct
           :opcode *op-bitor*
           :spec (logior a b))

(alu16-thm alu16-bitxor-correct
           :opcode *op-bitxor*
           :spec (logxor a b))

(alu16-thm alu16-min-correct
           :opcode *op-min*
           :spec (min a b))



; -----------------------------------------------------------------------------
;
;                     A FAILED PROOF, AND A HARD PROOF
;
; -----------------------------------------------------------------------------


; Now we get down to COUNT.  And the COUNT opcode has a bug.  When we try to
; prove it correct, we are given three counter-examples.

(alu16-thm alu16-count-correct
           :opcode *op-count*
           :spec (logcount a))

; This is where the debugging messages in the STV-RUN command come in really
; handy.  In this case we see the output:
;
;     Running conclusion:
;     STV Raw Inputs: ((OP . 6) (A . 128) (B . 0)).
;
;     STV Inputs:
;       OP:               #x6
;       A:                #x80
;       B:                #x0
;
;     STV Outputs:
;       RES:              #x0
;
;     Result: NIL

; You can now easily copy/paste this "STV Raw Inputs" alist and give it to
; stv-debug:

(stv-debug *test-vector*
           '((OP . 6) (A . 62963) (B . 31362)))

; This will bring up GTKWave or some other waveform viewer and let you explore
; the counterexample.  GTKWave has some really nice features, e.g., it can
; write out a "save" file that you can then reload to bring you back to how you
; were viewing the circuit.  Presumably, this exploration will eventually lead
; you to the problematic definition of ans_count.
;
; There are lots of things you can do to make debugging better.  A nice start
; is to also have your theorem macro print out the expected spec values.  For
; instance, we could change our theorem macro as follows:

(defmacro fancier-alu16-thm (name &key opcode spec (g-bindings '(alu16-default-bindings)))
  `(def-gl-thm ,name
     :hyp (and (alu16-type-hyps)
               (equal op ,opcode))
     :concl (b* ((impl (alu16-basic-result))
                 (spec ,spec))
              (cw "Spec: ~s0~%" (hexify spec))
              (equal impl spec))
     :g-bindings ,g-bindings))

; Now if we try to run:

(fancier-alu16-thm alu16-count-correct
                   :opcode *op-count*
                   :spec (logcount a))

; We'll get to see both the implementation's result and the specification's
; expectation...
;
;    STV Outputs:
;      RES:              #x0
;
;    Spec: #x1

; As your spec gets more elaborate, you can include important intermediate
; values, etc., to make debugging easier.  I suppose you could even get it
; to launch the waveform viewer automatically, if that's what you wanted.


; The last operation is multiplication.
;
; The alu16 circuit is especially unrealistic in that it just writes a
; multiplication operator to carry out the multiplication.  In practice
; you would not want to just synthesize a multiplier.
;
; Multipliers are especially hard for automatic bit-level tools like BDD
; packages.  Their BDDs are known to grow exponentially.  At any rate, this is
; a much harder problem than the previous operators.
;
; You generally have to do something clever to verify multipliers.  Since
; this one is only 16x16, we can power through it using GL, if we have enough
; memory and patience.  On a machine with 64 GB of memory, we can finish the
; proof in about 2,700 seconds after a couple of tweaks:

(set-max-mem (* 40 (expt 2 30)))  ;; Use up to 40 GB of memory before GC'ing
(hons-resize :addr-ht 400000000)  ;; Pre-reserve space for 400 million honses

(alu16-thm alu16-mult-correct
           :opcode *op-mult*
           :spec (logand (* a b) (1- (expt 2 16))))

; Obviously even this 16-bit multiplier is at the edge of what is reasonable
; using our BDD package with this particular ordering.  In general, when you
; start to hit a performance problem, you will have to find a better tool, or
; do something clever to simplify or split up the proof.
