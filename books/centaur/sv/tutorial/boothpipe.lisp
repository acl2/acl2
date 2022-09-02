; SV Hardware Verification Tutorial
; Copyright (C) 2012-2015 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sol.swords@intel.com


; boothpipe.lisp
;
; This tutorial shows a way to carry out a proof about a hardware module that
; is too hard (or at least, takes a long time) to as a single, atomic
; def-gl-thm using our current automatic tools.
;
; We target a contrived 32-bit multiplier circuit (boothpipe.v) that intuitively
; has two components: a booth-encoding component that computes partial
; products, and an adder component that adds these partial products,
; appropriately shifted, to get the answer.  We will prove that this circuit
; multiplies.
;
; The general idea here is that we would like to decompose the proof into two
; lemmas, each of which is far more tractable for bit-level tools to attack.
; In particular, we will separately prove lemmas along the lines of:
;
;   (1) the partial-product part is correct, and then
;   (2) the adding part is correct.
;
; We'll then stitch these lemmas together using an ordinary ACL2-style proof.
; (This ACL2 proof is not especially interesting; you can see the separate file
; booth-support.lisp if you want the details.)

(in-package "SV")
(include-book "../top")
(include-book "support")
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "oslib/ls" :dir :system)
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(include-book "booth-support")
(local (include-book "centaur/fgl/top" :dir :system))
(local (include-book "centaur/aignet/transforms" :dir :system))


; (depends-on "boothpipe.v")
; cert_param: (uses-glucose)
(value-triple (acl2::set-max-mem (* 3 (expt 2 30))))
(value-triple (acl2::tshell-ensure))

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (f-get-global 'acl2::parallel-execution-enabled state)
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))

(local (include-book "booth-support"))

; Setup.  This should be familiar if you've looked at, e.g., the alu16
; tutorial.

(local (include-book "centaur/vl/loader/top" :dir :system))

(defconsts (*boothpipe* state)
  (b* (((mv loadres state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files (list "boothpipe.v"))))
       (design (vl::vl-loadresult->design loadres))
       ((mv ?err svdesign ?good ?bad)
        (vl::cwtime (vl::vl-design->svex-design "boothpipe" design (vl::make-vl-simpconfig)))))
    (and err
         (er hard? 'boothpipe "Error: ~@0~%Warnings: ~s1~%" err
             (vl::vl-reportcard-to-string (vl::vl-design-reportcard bad))))
    (mv svdesign state)))

(def-saved-event boothpipe-run
  (defsvtv$ boothpipe-run
    ;; Set up our run of the module.
    :design *boothpipe*
    :cycle-phases (list (sv::make-svtv-cyclephase :constants '(("clk" . 0))
                                                  :inputs-free t
                                                  :outputs-captured t)
                        (sv::make-svtv-cyclephase :constants '(("clk" . 1))))
    :phases ((:label c0
              :inputs
              (("en"              en :hold t)
               ("a"               a)
               ("b"               b)))
             (:label c1
              :outputs
              (("minusb"          minusb)))
             (:label c2
              :overrides
              (("pp01_c2[35:18]" pp0 :cond pp0-ovr :output pp0)
               ("pp01_c2[17:0]"  pp1 :cond pp1-ovr :output pp1)
               ("pp23_c2[35:18]" pp2 :cond pp2-ovr :output pp2)
               ("pp23_c2[17:0]"  pp3 :cond pp3-ovr :output pp3)
               ("pp45_c2[35:18]" pp4 :cond pp4-ovr :output pp4)
               ("pp45_c2[17:0]"  pp5 :cond pp5-ovr :output pp5)
               ("pp67_c2[35:18]" pp6 :cond pp6-ovr :output pp6)
               ("pp67_c2[17:0]"  pp7 :cond pp7-ovr :output pp7)))
             (:label c3
              :outputs
              (("o"              o))))
    :parents (decomposition-proofs) ;; xdoc stuff, not needed
    ))

(def-saved-event boothpipe-data
  (def-svtv-data-export boothpipe-data))

(def-saved-event boothpipe-run-override-thms
  (defsection boothpipe-run-override-thms
    (local (include-book "centaur/sv/svtv/svtv-fsm-override-fgl-theory" :dir :system))
    (def-svtv-override-thms boothpipe-run boothpipe-data)))



(local
 (assert!
  ;; Make sure it can multiply 3*5.
  (b* ((in-alist  (list (cons 'a 3)
                        (cons 'b 5)
                        (cons 'en 1)))
       (out-alist (svtv-run (boothpipe-run) in-alist))
       (result    (cdr (assoc 'o out-alist))))
    (equal result 15))))

#||
(svtv-debug (boothpipe-direct)
            (list (cons 'a 3)
                  (cons 'b 5)
                  (cons 'en 1)))
||#


; You could now try to directly prove that this circuit multiplies, using
; something like this.  But this is very unlikely to work, and would require
; huge amounts of time and memory.

#||
   (def-gl-thm boothpipe-correct-direct
     :hyp (boothpipe-run-autohyps)
     :concl (b* ((in-alist  (boothpipe-run-autoins))
                 (out-alist (stv-run (boothpipe-run) in-alist))
                 (o         (cdr (assoc 'o out-alist))))
              (equal o (* a b)))
     :g-bindings (stv-easy-bindings (boothpipe-run)
                                    '((:mix a b))))
||#


; So instead of trying to prove it directly, we'll try to do something smarter.
; First we'll use the :overrides feature of STVs to allow us to "cut" the
; circuit.  To draw a picture of what we're going to do, this is what our
; original module looks like:
;
;  Inputs                              Outputs
;         __________________________
;        |    ___           ___     |
;   A ---+-->|pps|-- pp0 ->|add|    |
;        |   |   |-- ... ->|   |----+---> O            Original Circuit
;   B ---+-->|   |-- pp7 ->|   |    |
;        |   |___|         |___|    |
;        |__________________________|
;
; But we're actually going to work with a new, "decomposed" circuit, that looks
; like this:
;
; Inputs                               Outputs
;         __________________________
;        |                  ___     |
;  pp0 --+---------------->|add|    |
;  ... --+---------------->|   |----+---> O
;  pp7 --+---------------->|   |    |
;        |    ___          |___|    |                  Decomposed Circuit
;   A ---+-->|pps|------------------+---> pp0
;        |   |   |------------------+---> ...
;   B ---+-->|   |------------------+---> pp7
;        |   |___|                  |
;        |__________________________|
;
; This decomposed circuit lets us
;
;   (1) capture as additional outputs the values of the partial products (so we
;       can prove the partial product computation is correct), and
;
;   (2) insert fresh variables to use as the partial product signals for the
;       addition (so we can prove the addition part is correct).
;
; The basic way to perform this "cut" of the circuit is to use the :overrides
; feature of an STV.
;


; We'll now prove, separately, our two main lemmas, about the decomposed
; circuit.

(def-saved-event svtv-generalized-thm-defaults
  (progn (local (table sv::svtv-generalized-thm-defaults :svtv 'boothpipe-run))
         (local (table sv::svtv-generalized-thm-defaults :unsigned-byte-hyps t))
         (local (table sv::svtv-generalized-thm-defaults :input-var-bindings '((en 1))))))



(def-saved-event boothpipe-pp-correct
   ;; Main Lemma 1.  Partial Products Part is Correct.
   ;; This is a very easy proof for Glucose, taking about 1.5 seconds.
 (def-svtv-generalized-thm boothpipe-pp-correct
   :input-vars (a b)
   :output-vars (pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7)
   :concl (and (equal pp0 (boothpipe-pp-spec 16 0 a b))
               (equal pp1 (boothpipe-pp-spec 16 1 a b))
               (equal pp2 (boothpipe-pp-spec 16 2 a b))
               (equal pp3 (boothpipe-pp-spec 16 3 a b))
               (equal pp4 (boothpipe-pp-spec 16 4 a b))
               (equal pp5 (boothpipe-pp-spec 16 5 a b))
               (equal pp6 (boothpipe-pp-spec 16 6 a b))
               (equal pp7 (boothpipe-pp-spec 16 7 a b)))))


(defun find-form (start-of-form x)
  (if (atom x)
      nil
    (if (prefixp start-of-form x)
        x
      (or (find-form start-of-form (car x))
          (find-form start-of-form (cdr x))))))

(make-event
 ;; Save the def-fgl-thm and final defthm forms from boothpipe-pp-correct.
 (b* (((er make-event)
       (acl2::macroexpand1 (cdr (assoc 'boothpipe-pp-correct (table-alist 'saved-forms-table (w state))))
                           'find-boothpipe-pp-correct-fgl
                           state))
      (form (cadr make-event))
      ((er (cons ?stobjs-out (list ?eval-err form ?replaced-state)))
       (trans-eval-default-warning form 'find-boothpipe-pp-correct-fgl state t))
      ((when eval-err)
       (er soft 'find-boothpipe-pp-correct-fgl "~@0" eval-err))
      (fgl-form (find-form '(fgl::def-fgl-thm boothpipe-pp-correct-override-lemma) form))
      (final-thm-form (find-form '(defthm boothpipe-pp-correct) form)))
   (value `(progn (table saved-forms-table 'boothpipe-pp-correct-fgl ',fgl-form)
                  (table saved-forms-table 'boothpipe-pp-correct-final-thm ',final-thm-form)))))


;; Main Lemma 2.  Addition Part is Correct.

(def-saved-event boothpipe-sum-correct
 (def-svtv-generalized-thm boothpipe-sum-correct
   :override-vars (pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7)
   :output-vars (o)
   :concl (b* ((- (cw "o: ~s0~%" (str::hexify o)))
               (res (loghead 32
                             (+ (ash (logext 18 pp0) #x0)
                                (ash (logext 18 pp1) #x2)
                                (ash (logext 18 pp2) #x4)
                                (ash (logext 18 pp3) #x6)
                                (ash (logext 18 pp4) #x8)
                                (ash (logext 18 pp5) #xa)
                                (ash (logext 18 pp6) #xc)
                                (ash (logext 18 pp7) #xe))))
               (- (cw "res: ~s0~%" (str::hexify res))))
            (equal o res))))

(make-event
 ;; Save the def-fgl-thm and final defthm forms from boothpipe-sum-correct.
 (b* (((er make-event)
       (acl2::macroexpand1 (cdr (assoc 'boothpipe-sum-correct (table-alist 'saved-forms-table (w state))))
                           'find-boothpipe-sum-correct-fgl
                           state))
      (form (cadr make-event))
      ((er (cons ?stobjs-out (list ?eval-err form ?replaced-state)))
       (trans-eval-default-warning form 'find-boothpipe-sum-correct-fgl state t))
      ((when eval-err)
       (er soft 'find-boothpipe-sum-correct-fgl "~@0" eval-err))
      (fgl-form (find-form '(fgl::def-fgl-thm boothpipe-sum-correct-override-lemma) form))
      (final-thm-form (find-form '(defthm boothpipe-sum-correct) form)))
   (value `(progn (table saved-forms-table 'boothpipe-sum-correct-fgl ',fgl-form)
                  (table saved-forms-table 'boothpipe-sum-correct-final-thm ',final-thm-form)))))



; Now we'll use an ordinary ACL2 proof to show that these ACL2 "specifications"
; for the partial-products and sum can be chained together to actually carry
; out a multiply.
;
; We relegate most of the groundwork here over to booth-support.lisp.  These
; lemmas here about hide/unhide actually slow down the proof below, but cause
; it to show (in the ACL2 proof output) explicitly how booth-sum-impl is
; expanded into the sum of partial-products that we need below in
; booth-sum-of-products-correct.

;; (local (defund unhide (x) x))

;; (local (defthm unhide-hide
;;          (equal (unhide (hide x)) x)
;;          :hints (("goal" :in-theory (enable unhide)
;;                   :expand ((:free (x) (hide x)))))))


(local (in-theory (disable ash logext)))

(local (defthm booth-sum-impl-redef
         (equal (booth-sum-impl n i a b sz)
                (IF (ZP N)
                    0
                    (+ (ASH (LOGEXT (+ 2 SZ)
                                    (BOOTHPIPE-PP-SPEC SZ I A B))
                            (* 2 I))
                       (BOOTH-SUM-IMPL (1- N)
                                       (+ 1 I)
                                       A B SZ))))
         :hints(("Goal" :in-theory (e/d (booth-sum-impl))))))

(def-saved-event booth-sum-of-products-correct
 (defthm booth-sum-of-products-correct
   (implies (AND (NATP A)
                 (NATP B)
                 (< A (EXPT 2 16))
                 (< B (EXPT 2 16)))
            (let ((pp0 (boothpipe-pp-spec 16 #x0 a b))
                  (pp1 (boothpipe-pp-spec 16 #x1 a b))
                  (pp2 (boothpipe-pp-spec 16 #x2 a b))
                  (pp3 (boothpipe-pp-spec 16 #x3 a b))
                  (pp4 (boothpipe-pp-spec 16 #x4 a b))
                  (pp5 (boothpipe-pp-spec 16 #x5 a b))
                  (pp6 (boothpipe-pp-spec 16 #x6 a b))
                  (pp7 (boothpipe-pp-spec 16 #x7 a b)))
              (equal (+ (ash (logext 18 pp0) #x0)
                        (ash (logext 18 pp1) #x2)
                        (ash (logext 18 pp2) #x4)
                        (ash (logext 18 pp3) #x6)
                        (ash (logext 18 pp4) #x8)
                        (ash (logext 18 pp5) #xa)
                        (ash (logext 18 pp6) #xc)
                        (ash (logext 18 pp7) #xe))
                     (* (logext 16 a)
                        (logext 16 b)))))
   :hints (("goal" :use ((:instance booth-sum-impl-is-multiply
                                    (n 8) (sz 16)))
            :in-theory (e/d ()
                            (booth-sum-impl-is-multiply
                             ash
                             logext
                             logapp
                             loghead
                             signed-byte-p
                             boothpipe-pp-spec))))))

; And here is the main ACL2 lemma to show booth-encoding/addition really do a
; multiply.  Note that this is just an ACL2 theorem, it has nothing to do with
; the circuits above.

(local (defthm boothpipe-pp-spec-bound
         (unsigned-byte-p 18 (boothpipe-pp-spec 16 i a b))
         :hints(("Goal" :in-theory (e/d (boothpipe-pp-spec)
                                        (logext
                                         loghead
                                         logbitp))))))



;; (local (in-theory (disable boothpipe-decomp-is-boothpipe-via-GL)))

; All that remains is to chain the above facts together.  Fortunately, the
; theorem resulting from each def-svtv-generalized-thm form is one that can
; easily be composed with other such theorems.  Boothpipe-pp-correct shows that
; the partial products are computed correctly; boothpipe-sum-correct shows that
; the partial products are correctly summed, and booth-sum-of-products-correct
; shows that the composition of the partial product computation and summing
; produces the signed 16-bit multiply.  The composition of these is just an
; ordinary ACL2 theorem (by rewriting), but we can write it succinctly as
; another def-svtv-generalized-thm form (using the :no-lemmas option to skip the
; FGL step.)

(in-theory (disable loghead logext unsigned-byte-p))

;; This is the most general form of the theorem. Note the ugly hyp #4 -- really
;; this just says that the PP override test variables should be unbound, or set to 0 or X.
(def-saved-event boothpipe-correct-gen
  (def-svtv-generalized-thm boothpipe-correct-gen
    :input-vars (a b)
    :output-vars (o)
    :concl (equal o (loghead 32 (* (logext 16 a)
                                   (logext 16 b))))
    :no-lemmas t
    :hints(("Goal" :in-theory (e/d () ((boothpipe-run-pipeline-override-triples)))))))

(make-event
 ;; Save the final defthm form from boothpipe-correct-gen.
 (b* (((er make-event)
       (acl2::macroexpand1 (cdr (assoc 'boothpipe-correct-gen (table-alist 'saved-forms-table (w state))))
                           'find-boothpipe-correct-gen-final
                           state))
      (form (cadr make-event))
      ((er (cons ?stobjs-out (list ?eval-err form ?replaced-state)))
       (trans-eval-default-warning form 'find-boothpipe-correct-gen-final state t))
      ((when eval-err)
       (er soft 'find-boothpipe-correct-gen-final "~@0" eval-err))
      (final-thm-form (find-form '(defthm boothpipe-correct-gen) form)))
   (value `(table saved-forms-table 'boothpipe-correct-gen-final-thm ',final-thm-form))))


;; A maybe clearer but less general form:
(def-saved-event boothpipe-correct
  (defthm boothpipe-correct
    (implies (and (unsigned-byte-p 16 a)
                  (unsigned-byte-p 16 b))
             (b* ((in-alist (list `(a . ,a)
                                  `(b . ,b)
                                  `(en . 1)))
                  (out-alist (svtv-run (boothpipe-run) in-alist))
                  (o         (svex-env-lookup 'o out-alist)))
               (equal o (loghead 32 (* (logext 16 a) (logext 16 b))))))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup-of-cons
                                    4vec-p-when-integerp
                                    svex-env-lookup-use-exec
                                    svex-env-keys-no-1s-p-of-variable-free-term
                                    hons-intersection-force-execute
                                    svex-env-keys-no-1s-p-of-cons)
                                   ((svex-env-lookup)
                                    (boothpipe-run-pipeline-override-triples)))))))




(deftutorial decomposition-proofs
  :parents (sv-tutorial)
  :short "Proof by decomposing and re-composing a hardware model"
  :long #{"""

<p>Part of the @(see sv-tutorial). Previous section: @(see
proofs-with-stvs).</p>


<p>Certain kinds of hardware models aren't amenable to direct verification by
bit-blasting because the function computed is too hard for SAT solvers/BDD
packages.  Multipliers, most significantly, fall into this category --
expressing a multiplier function as BDDs always results in exponential memory
usage, and they are notoriously difficult for SAT solvers to handle as well.  A
standard trick for verifying a multiplier is to split the design into two or
more parts, specifying separately how each of the parts should behave; prove
 (by bit-blasting or automatic methods) that each of the parts matches its
specification, and prove (by traditional theorem-proving methods) that the
composition of the spec functions is equivalent to the spec for the whole
module.</p>

<p>The file "boothpipe.lisp" where this documentation topic is defined
contains an example to show how to do this with SVEX.  In this topic we will
discuss a few critical parts of the process, but for a more complete picture
see that file and the comments in it.</p>

<h4>STV Setup for Decomposition</h4>

<p>In the boothpipe example, the intermediate signals to split the pipeline on
are the partial products @('pp0')...@('pp7').  We'll have one SVTV that says
how to run the whole module, whether we're decomposing on the partial products
or not.  For each of the partial products, this SVTV will both conditionally overrides the signal and provides an output signal that producess the un-overridden value:</p>

@(`(:code ($ boothpipe-run))`)

<p>Each entry in the @(':overrides') listed in the @('c2') phase gives the
override value variable, override condition variable, and output variable for
one of the partial products.  For example, the first entry:
@({
 ("pp01_c2[35:18]" pp0 :cond pp0-ovr :output pp0)
 })
says @('pp01_c2[35:18]') is overriden with the value of input variable @('pp0')
when corresponding bits of input variable @('pp0-ovr') are set to 1.
Additionally, output variable @('pp0') is assigned the un-overridden value of
@('pp01_c2[35:18]').  Since input variables and output variables of SVTVs are
treated as separate namespaces, it is OK (and somewhat conventional) for the
override value (input) variable and corresponding output variable for the same
signal to be the same.</p>

<h4>Composing the Proof</h4>

<p>The basic steps for completing the top-level proof we want are as
follows:</p>

<ol>
<li>Prove that the partial products are correctly computed.</li>
<li>Prove that summation of the partial products is correctly computed.</li>
<li>Prove that the correct summation of the correctly-computed partial products produces a multiply.</li>
<li>Put steps 1 through 3 together to prove that the output of the circuit is a multiply.</li>
</ol>

<p>Steps 1 and 2 can be done via bit-blasting proofs as discussed in the
previous section of the tutorial (@(see proofs-with-stvs)).  However, since we
are using conditional overrides there are a couple of extra steps involved in
making it so they can be composed together, which we'll discuss next. Step 3 is
simply an ACL2 arithmetic proof, and step 4 is also done with regular ACL2
rewriting.</p>


<h4>Conditional Override Elimination</h4>

<p>In Step 2, proving that the summation of the parital products is correct, we
want to override the partial products of the SVTV with free variables and show
that the output computed is a function of those variables.  However, ultimately
we want to know what happens in the SVTV when these signals are not
overridden. To do this we use some facts that may be automatically proven about
the SVTV to show that this fact about the run with the partial products
overridden implies a similar fact about a run where the partial products are
instead sampled as outputs.  The steps for this are as follows.</p>

<p>First, prove the automatic theorems about the SVTV:</p>
@(`(:code ($ boothpipe-data))`)
@(`(:code ($ boothpipe-run-override-thms))`)

<p>Now we can use the @(see def-svtv-generalized-thm) utility to prove our two
steps. First, we set some defaults that will be used for all
@('def-svtv-generalized-thm') invocations in this book: these forms say which
SVTV we're using, to assume by default that all input and override variables
used are appropriate-sized unsigned bytes, and to assume the enable signal is
1.</p>

@(`(:code ($ svtv-generalized-thm-defaults))`)

<p>We can start by proving the partial product computation correct:</p>
@(`(:code ($ boothpipe-pp-correct))`)

<p>This form expands to an encapsulate that first proves the following lemma
using FGL -- a typical bit-blasting proof similar to those in @(see
proofs-with-stvs):</p>

@(`(:code ($ boothpipe-pp-correct-fgl))`)

<p>This lemma is used to prove a much more general result:</p>

@(`(:code ($ boothpipe-pp-correct-final-thm))`)

<p>Notes: First, @('svassocs') is a @(see b*) binder that binds the variables listed
to @('svex-env-lookup')s of the bound object -- e.g.,</p>
@({
 (b* (((svassocs a b en) env) ...) ...)
 })
<p>expands to approximately</p>
@({
 (let* ((a (svex-env-lookup 'a env))
        (b (svex-env-lookup 'b env))
        (en (svex-env-lookup 'en env))
        ...)
   ...)
 })

<p>Second, there is a special hypothesis:</p>
@({
 (SVEX-ENV-KEYS-NO-1S-P (SVAR-OVERRIDE-TRIPLELIST->TESTVARS
                          (BOOTHPIPE-RUN-PIPELINE-OVERRIDE-TRIPLES)) ENV)
 })

<p>This says that in the environment, there are no conditional override test
variables set to 1s -- i.e., no signals defined as conditional overrides are
actually overridden.</p>

<p>Third, note that @('boothpipe-pp-correct') is much more generally
applicable as a set of rewrite rules than
@('boothipe-pp-correct-override-lemma') or any usual bitblasting theorem of the
form discussed in @(see proofs-with-stvs).  The second argument to
@('svtv-run') in this theorem is just a variable @('env') with some hypotheses
about it, whereas in a typical bitblasting theorem it would be expressed as an
alist of a specific shape with some symbolic values bound to concrete keys.
This is what allows this theorem to be composed with others much more easily.
The lemmas proved in the @('def-svtv-override-thms') form allow the FGL lemma
to be generalized into this form.</p>



<p>Next we can similarly prove the sum of partial products correct:</p>
@(`(:code ($ boothpipe-sum-correct))`)

<p>Here, the FGL lemma has an additional wrinkle in that it overrides the
partial products:</p>
@(`(:code ($ boothpipe-sum-correct-fgl))`)

<p>The final theorem proved by the @('def-svtv-generalized-thm') form, however,
eliminates these overrides.  It again has the @('svex-env-keys-no-1s-p')
hypothesis, and instead extracts the partial products from the outputs of the
@('svtv-run'). That is, instead of a theorem \"If you run the SVTV with PPs
overridden, output @('o') is related to the override values\" we instead have a
theorem \"If you run the SVTV with no overrides, output @('o') is related to
the values of the PPs.\" This again is much easier to compose, because we can
easily describe an @('svtv-run') which satisfies the hypotheses of both
@('boothpipe-pp-correct') and @('boothpipe-sum-correct') simultaneously.</p>

<p>We now have two rewrite rules that will be useful in our final theorem: one
expresses the final output @('o') of the SVTV as the sum of the @('pp')
outputs, and the other expresses the @('pp') outputs of the SVTV as the correct
Booth partial products for the inputs @('a') and @('b').  We want to use these
to show that @('o') is the multiplication of @('a') and @('b'). So we first
need a theorem showing that the sum of the Booth partial products is
multiplication.  Note that this has nothing to do with the hardware design;
it's purely an ACL2 arithmetic theorem:</p>

@(`(:code ($ booth-sum-of-products-correct))`)

<p>This can now be used to prove our top-level theorem.  We can do this with
another @('def-svtv-generalized-thm') form, this time with the @(':no-lemmas t')
argument, which directs it to prove the generalized theorem directly with ACL2
rather than first proving an FGL lemma:</p>

@(`(:code ($ boothpipe-correct-gen))`)

<p>The theorem resulting from this form:</p>

@(`(:code ($ boothpipe-correct-gen-final-thm))`)

<p>This is, again, a quite general theorem.  However, as a matter of taste it
might be pleasant to see a more specific version of this theorem that avoids
these complicated hypotheses, which could lead to worries that the theorem is
vacuous (i.e. there is no @('env') satisfying the hypotheses).  The following
theorem essentially specifies a class of environment that does satisfy the
hypotheses:</p>

@(`(:code ($ boothpipe-correct))`)

"""})

(make-event
 (cons 'progn (recreate-saved-forms-table (table-alist 'saved-forms-table (w state)))))
