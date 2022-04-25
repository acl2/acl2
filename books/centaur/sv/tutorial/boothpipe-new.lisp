; SV Hardware Verification Tutorial
; Copyright (C) 2012-2015 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
(local (include-book "centaur/fgl/top" :dir :system))
(local (include-book "centaur/aignet/transforms" :dir :system))

;; (local (include-book "centaur/esim/stv/stv-decomp-proofs-even-better" :dir :system))
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

(include-book "../svtv/debug")
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
    :labels         '(c0   c1 c1  c2 c2 c3 c3)
    :inputs '(("en"   en)
              ("clk"  0   ~)
              ("a"    a   _)
              ("b"    b   _))
    :overrides '(("pp01_c2[35:18]"    _   _   _   _   (pp0 pp0-ovr)  _)
                 ("pp01_c2[17:0]"     _   _   _   _   (pp1 pp1-ovr)  _)
                 ("pp23_c2[35:18]"    _   _   _   _   (pp2 pp2-ovr)  _)
                 ("pp23_c2[17:0]"     _   _   _   _   (pp3 pp3-ovr)  _)
                 ("pp45_c2[35:18]"    _   _   _   _   (pp4 pp4-ovr)  _)
                 ("pp45_c2[17:0]"     _   _   _   _   (pp5 pp5-ovr)  _)
                 ("pp67_c2[35:18]"    _   _   _   _   (pp6 pp6-ovr)  _)
                 ("pp67_c2[17:0]"     _   _   _   _   (pp7 pp7-ovr)  _))
    :internals '(("minusb" _   _   minusb)
                 ("pp01_c2[35:18]"    _   _   _   _   pp0)
                 ("pp01_c2[17:0]"     _   _   _   _   pp1)
                 ("pp23_c2[35:18]"    _   _   _   _   pp2)
                 ("pp23_c2[17:0]"     _   _   _   _   pp3)
                 ("pp45_c2[35:18]"    _   _   _   _   pp4)
                 ("pp45_c2[17:0]"     _   _   _   _   pp5)
                 ("pp67_c2[35:18]"    _   _   _   _   pp6)
                 ("pp67_c2[17:0]"     _   _   _   _   pp7))
    :outputs '(("o"   _   _   _   _   _   _   o))
    :parents (decomposition-proofs) ;; xdoc stuff, not needed
    ))

(def-saved-event boothpipe-data
  (def-svtv-data-export boothpipe-data))

(def-saved-event boothpipe-run-override-thms
  (defsection boothpipe-run-override-thms
    (local (include-book "centaur/sv/svtv/svtv-fsm-override-fgl-theory" :dir :system))
    (def-svtv-override-thms boothpipe-run boothpipe-data)))

;; (def-saved-event boothpipe-pipeline-thm
;;   (def-pipeline-thm boothpipe-direct))



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
;
; BUT THERE IS A VERY IMPORTANT MODELING NOTE!!!
;
; Overrides work by basically rewriting the E module into a new E module.  So
; this new stv, boothpipe-decomp, does not necessarily have any well-founded
; connection to the actual, original Verilog module.
;
; In other words, anything we prove about boothpipe-decomp is a proof about this
; new, cut module.  So we don't want this boothpipe-decomp STV to have any part
; in our final theorem.  Instead, we want to prove something that is only in
; terms of our original circuit, boothpipe-run!
;
; However, boothpipe-decomp will be very useful for getting to this final
; theorem, as we'll now see.
;
;
; To emphasize that our final theorem has nothing to do with boothpipe-decomp,
; we make the whole STV local.

;; (local (gl::gl-satlink-mode))

;; (local
;;  (fgl::def-fgl-rewrite svex-env-lookup-gl
;;    (equal (svex-env-lookup x env)
;;           (4vec-fix (cdr (hons-get (svar-fix x) (make-fast-alist env)))))
;;    :hints(("Goal" :in-theory (enable svex-env-lookup)))))


(local
   ;; Main Lemma 1.  Partial Products Part is Correct.
   ;; This is a very easy proof for Glucose, taking about 1.5 seconds.
   ;; The stuff done with the output alist is confusing but is what we want for composition.
 (def-svtv-override-fact boothpipe-pp-correct
   :svtv boothpipe-run
   :input-vars (a b)
   :input-var-bindings ((en 1))
   :output-vars (pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7)
   :hyp (and (unsigned-byte-p 16 a)
             (unsigned-byte-p 16 b))
   :concl (and (equal pp0 (boothpipe-pp-spec 16 0 a b))
               (equal pp1 (boothpipe-pp-spec 16 1 a b))
               (equal pp2 (boothpipe-pp-spec 16 2 a b))
               (equal pp3 (boothpipe-pp-spec 16 3 a b))
               (equal pp4 (boothpipe-pp-spec 16 4 a b))
               (equal pp5 (boothpipe-pp-spec 16 5 a b))
               (equal pp6 (boothpipe-pp-spec 16 6 a b))
               (equal pp7 (boothpipe-pp-spec 16 7 a b)))))



; We'll now prove, separately, our two main lemmas, about the decomposed
; circuit.  We'll attack these using SAT.  This should be familiar if you've
; already seen sat.lsp.



;; Main Lemma 2.  Addition Part is Correct.

(local
 (def-svtv-override-fact boothpipe-sum-correct
   :svtv boothpipe-run
   :input-var-bindings ((en 1))
   :override-vars (pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7)
   :output-vars (o)
   :hyp (and (unsigned-byte-p 18 pp0)
             (unsigned-byte-p 18 pp1)
             (unsigned-byte-p 18 pp2)
             (unsigned-byte-p 18 pp3)
             (unsigned-byte-p 18 pp4)
             (unsigned-byte-p 18 pp5)
             (unsigned-byte-p 18 pp6)
             (unsigned-byte-p 18 pp7))
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

(local
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


; So far, we have lemmas that show our decomposed circuit computes the right
; things, and that these two computations actually carry out a multiply.  But
; we don't WANT a theorem about our decomposed circuit; we want a theorem about
; our original circuit.
;
; So now we're going to show that, properly wired up, our decomposed circuit is
; just doing what the original circuit does.  It's easiest to explain this with
; a picture.  Recall the picture of our decomposed circuit:
;
;         __________________________
;        |                  ___     |
;  pp0 --+---------------->|add|    |
;  ... --+---------------->|   |----+---> O
;  pp7 --+---------------->|   |    |
;        |    ___          |___|    |
;   A ---+-->|pps|------------------+---> pp0
;        |   |   |------------------+---> ...
;   B ---+-->|   |------------------+---> pp7
;        |   |___|                  |
;        |__________________________|
;
; We're now going to show that if we wire the "cut" back together like this:
;
;    +==================================================+
;    ||+----------------------------------------------+||
;    |||                                              |||
;    |||         __________________________           |||
;    |||        |                  ___     |          |||
;    ||+- pp0 --+---------------->|add|    |          |||
;    |+-- ... --+---------------->|   |----+---> O    |||
;    +--- pp7 --+---------------->|   |    |          |||
;               |    ___          |___|    |          |||
;          A ---+-->|pps|------------------+---> pp0 -+||
;               |   |   |------------------+---> ... --+|
;          B ---+-->|   |------------------+---> pp7 ---+
;               |   |___|                  |
;               |__________________________|
;
; Then what you end up with is the original circuit,
;
;         __________________________
;        |    ___           ___     |
;   A ---+-->|pps|-- pp0 ->|add|    |
;        |   |   |-- ... ->|   |----+---> O            Original Circuit
;   B ---+-->|   |-- pp7 ->|   |    |
;        |   |___|         |___|    |
;        |__________________________|
;
; We used to do this using GL, but we now use a specialized theory for
; performing these sorts of proofs, developed in the book
; stv-decomp-proofs.lisp. (See above include-book for file location.)


; Deciding whether to use GL or the specialized theory to perform the
; composition proof is a judgement call.  Sometimes using GL takes too much
; time, even though the two circuits being compared "should" be almost the
; same.  In this case, the specialized theory should likely be used.  However,
; if the decomposition/rewiring is such that the 4v-sexpr representations of
; the circuits are completely different, but they still happen to be logically
; equivalent, then GL should be used.  GL is necessary in this case, because
; GL does not depend on the circuits being equal after sexpr rewriting.

;; (defthm assoc-in-svex-alist-eval
;;   (implies k
;;            (equal (assoc k (svex-alist-eval al env))
;;                   (and (assoc k  (svex-alist-fix al))
;;                        (cons k (svex-eval (cdr (assoc k  (svex-alist-fix al))) env)))))
;;   :hints(("Goal" :in-theory (enable svex-alist-eval
;;                                     svex-alist-fix))))


#|

; BOZO: Using specific inputs instead of the autoins macros causes a 15-way
; case-split.  Using specific hyps insteada of autohyps furthers that case
; split to be 272-way.  Also, the proof doesn't go through.

; If you are using the approach found in this book in your own proofs, you
; should probably just use autoins and autohyps (or fix the cause).


|#


;; (local (in-theory (disable boothpipe-decomp-is-boothpipe-via-GL)))

; All that remains is to chain the above facts together.
;
;   1. By this last GL lemma, we know how to express the result of
;      boothpipe-run in terms of the two-phase computation that
;      boothpipe-decomp carries out.
;
;   2. By our two main GL lemmas about boothpipe-decomp, we have ugly
;      ACL2 definitions of the partial-product/sum computations that
;      the decomposed module can do.
;
;   3. By our ACL2 lemma booth-sum-of-products-correct, we know that
;      together these ACL2 computations are just a multiply.
;
; Hence the whole thing does a multiply.  This chaining-together is just an
; ordinary (non-GL) ACL2 theorem:

;; (local (defthm boothpipe-run-autohyps-implies-step1-autohyps
;;          (implies (boothpipe-run-autohyps)
;;                   (boothpipe-step1-autohyps))
;;          :hints(("Goal" :in-theory (enable boothpipe-run-autohyps
;;                                            boothpipe-step1-autohyps)))))

;; (local
;;  (make-event
;;   `(defthm svex-env-boundp-of-step1
;;      (equal (svex-env-boundp key (svtv-run (boothpipe-step1) env
;;                                            :skip nil :include nil
;;                                            :boolvars t :simplify nil :quiet nil :readable t :allvars nil))
;;             (consp (member-equal (svar-fix key) ',(svex-alist-keys (svtv->outexprs (boothpipe-step1))))))
;;      :hints(("Goal" :in-theory (enable (boothpipe-step1) svex-env-boundp svtv-run))))))

(in-theory (disable loghead logext unsigned-byte-p))

;; This is the most general form of the theorem. Note the ugly hyp #4 -- really
;; this just says that the PP override test variables should be unbound, or set to 0 or X.
(defthm boothpipe-correct-gen
  (b* (((svassocs a b en) in-alist)
       (out-alist (svtv-run (boothpipe-run) in-alist))
       (o (svex-env-lookup 'o out-alist)))
    (implies (and (unsigned-byte-p 16 a)
                  (unsigned-byte-p 16 b)
                  (equal en 1)
                  (svex-env-keys-no-1s-p
                   (svar-override-triplelist->testvars (boothpipe-run-pipeline-override-triples))
                   in-alist))
             (equal o (loghead 32 (* (logext 16 a)
                                     (logext 16 b))))))
  :hints(("Goal" :in-theory (e/d () ((boothpipe-run-pipeline-override-triples))))))


;; A maybe clearer but less general form:
(defthm boothpipe-correct
  (implies (and (unsigned-byte-p 16 a)
                (unsigned-byte-p 16 b))
           (b* ((in-alist `((a . ,a) (b . ,b) (en . 1)))
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
                                  (boothpipe-run-pipeline-override-triples))))))


