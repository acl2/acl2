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
; Original author: Sol Swords <sswords@centtech.com>
;                  Jared Davis <jared@centtech.com>


; boothmul.lisp
;
; This tutorial shows a way to carry out a proof about a hardware module that
; is too hard (or at least, takes a long time) to as a single, atomic
; def-gl-thm using our current automatic tools.
;
; We target a contrived 32-bit multiplier circuit (boothmul.v) that intuitively
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

(in-package "ACL2")
(include-book "intro")
(include-book "centaur/gl/bfr-satlink" :dir :system)
(local (include-book "booth-support"))
(local (include-book "centaur/esim/stv/stv-decomp-proofs" :dir :system))
; (depends-on "boothmul.v")
; cert_param: (hons-only)
; cert_param: (uses-glucose)
; cert_param: (ccl-only)
(value-triple (set-max-mem (* 3 (expt 2 30))))
(value-triple (tshell-ensure))

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (and (hons-enabledp state)
          (f-get-global 'parallel-execution-enabled state))
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))


; Setup.  This should be familiar if you've looked at, e.g., the alu16
; tutorial.

(defmodules *boothmul-translation*
  ;; Translate the Verilog
  (vl::make-vl-loadconfig
   :start-files (list "boothmul.v")))

(defconst *boothmul*
  ;; Get the E module
  (b* ((mods  (vl::vl-translation->mods *boothmul-translation*))
       (boothmul (vl::vl-find-module "boothmul" mods))
       ((unless boothmul)
        (er hard? '*boothmul* "Failed to translate boothmul?"))
       (esim  (vl::vl-module->esim boothmul))
       ((unless (good-esim-modulep esim))
        (er hard? '*boothmul* "Failed to produce a good esim module")))
    esim))

(defstv boothmul-direct
  ;; Set up our run of the E module.
  :mod *boothmul*
  :inputs '(("a"   a)
            ("b"   b))
  :outputs '(("o"    o))
  :parents (esim-tutorial) ;; xdoc stuff, not needed
  )

(local
 (assert!
  ;; Make sure it can multiply 3*5.
  (b* ((in-alist  (list (cons 'a 3)
                        (cons 'b 5)))
       (out-alist (stv-run (boothmul-direct) in-alist))
       (result    (cdr (assoc 'o out-alist))))
    (equal result 15))))

; You could now try to directly prove that this circuit multiplies, using
; something like this.  But this is very unlikely to work, and would require
; huge amounts of time and memory.

#||
   (def-gl-thm boothmul-correct-direct
     :hyp (boothmul-direct-autohyps)
     :concl (b* ((in-alist  (boothmul-direct-autoins))
                 (out-alist (stv-run (boothmul-direct) in-alist))
                 (o         (cdr (assoc 'o out-alist))))
              (equal o (* a b)))
     :g-bindings (stv-easy-bindings (boothmul-direct)
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
; this new stv, boothmul-decomp, does not necessarily have any well-founded
; connection to the actual, original Verilog module.
;
; In other words, anything we prove about boothmul-decomp is a proof about this
; new, cut module.  So we don't want this boothmul-decomp STV to have any part
; in our final theorem.  Instead, we want to prove something that is only in
; terms of our original circuit, boothmul-direct!
;
; However, boothmul-decomp will be very useful for getting to this final
; theorem, as we'll now see.
;
;
; To emphasize that our final theorem has nothing to do with boothmul-decomp,
; we make the whole STV local.

(local
 (defstv boothmul-decomp
   :mod *boothmul*
   :inputs '(("a"   a)
             ("b"   b))
   :outputs '(("o"    o))
   :internals '(("minusb" minusb)
                ("temp_1" temp1))
   :overrides '(("pp0" pp0)
                ("pp1" pp1)
                ("pp2" pp2)
                ("pp3" pp3)
                ("pp4" pp4)
                ("pp5" pp5)
                ("pp6" pp6)
                ("pp7" pp7))
   :parents (esim-tutorial) ;; xdoc stuff, not needed
   ))



; We'll now prove, separately, our two main lemmas, about the decomposed
; circuit.  We'll attack these using SAT.  This should be familiar if you've
; already seen sat.lsp.

(local (gl::gl-satlink-mode))

(local
 (progn
   (defun my-glucose-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach gl::gl-satlink-config my-glucose-config)))

(local
 (def-gl-thm boothmul-pp-correct
   ;; Main Lemma 1.  Partial Products Part is Correct.
   ;; This is a very easy proof for Glucose, taking about 1.5 seconds
   :hyp (boothmul-decomp-autohyps)
   :concl (b* ((in-alist  (boothmul-decomp-autoins))
               (out-alist (stv-run (boothmul-decomp) in-alist)))
            (and (equal (cdr (assoc 'pp0 out-alist)) (boothmul-pp-spec 16 #x0 a b))
                 (equal (cdr (assoc 'pp1 out-alist)) (boothmul-pp-spec 16 #x1 a b))
                 (equal (cdr (assoc 'pp2 out-alist)) (boothmul-pp-spec 16 #x2 a b))
                 (equal (cdr (assoc 'pp3 out-alist)) (boothmul-pp-spec 16 #x3 a b))
                 (equal (cdr (assoc 'pp4 out-alist)) (boothmul-pp-spec 16 #x4 a b))
                 (equal (cdr (assoc 'pp5 out-alist)) (boothmul-pp-spec 16 #x5 a b))
                 (equal (cdr (assoc 'pp6 out-alist)) (boothmul-pp-spec 16 #x6 a b))
                 (equal (cdr (assoc 'pp7 out-alist)) (boothmul-pp-spec 16 #x7 a b))
                 ))
   :g-bindings (boothmul-decomp-autobinds)))

(local
 ;; This is trivially proved by instantiating boothmul-pp-correct.  But we need
 ;; to know this specifically later on when we want to show that the
 ;; composition of the two steps is equivalent to the whole run.
 (defthm boothmul-pps-types
   (implies (boothmul-decomp-autohyps)
            (b* ((in-alist  (boothmul-decomp-autoins))
                 (out-alist (stv-run (boothmul-decomp) in-alist)))
              (and (natp (cdr (assoc 'pp0 out-alist)))
                   (natp (cdr (assoc 'pp1 out-alist)))
                   (natp (cdr (assoc 'pp2 out-alist)))
                   (natp (cdr (assoc 'pp3 out-alist)))
                   (natp (cdr (assoc 'pp4 out-alist)))
                   (natp (cdr (assoc 'pp5 out-alist)))
                   (natp (cdr (assoc 'pp6 out-alist)))
                   (natp (cdr (assoc 'pp7 out-alist))))))
   :hints (("goal" :use boothmul-pp-correct
            :in-theory '((:t boothmul-pp-spec)
                         natp-compound-recognizer)))))

(local
 (def-gl-thm boothmul-sum-correct
   ;; Main Lemma 2.  Addition Part is Correct.
   ;; This is also easy for Glucose, taking about 13 seconds.
   :hyp (boothmul-decomp-autohyps)
   :concl (b* ((in-alist  (boothmul-decomp-autoins))
               (out-alist (stv-run (boothmul-decomp) in-alist))
               (o (cdr (assoc 'o out-alist)))
               (- (cw "o: ~s0~%" (str::hexify o)))
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
            (equal o res))
   :g-bindings (boothmul-decomp-autobinds)))


; Now we'll use an ordinary ACL2 proof to show that these ACL2 "specifications"
; for the partial-products and sum can be chained together to actually carry
; out a multiply.
;
; We relegate most of the groundwork here over to booth-support.lisp.  These
; lemmas here about hide/unhide actually slow down the proof below, but cause
; it to show (in the ACL2 proof output) explicitly how booth-sum-impl is
; expanded into the sum of partial-products that we need below in
; booth-sum-of-products-correct.

(local (defund unhide (x) x))

(local (defthm unhide-hide
         (equal (unhide (hide x)) x)
         :hints (("goal" :in-theory (enable unhide)
                  :expand ((:free (x) (hide x)))))))

(local (defthm booth-sum-impl-redef
         (equal (booth-sum-impl n i a b sz)
                (IF (ZP N)
                    0
                    (+ (ASH (LOGEXT (+ 2 SZ)
                                    (BOOTHMUL-PP-SPEC SZ I A B))
                            (* 2 I))
                       (unhide (hide (BOOTH-SUM-IMPL (1- N)
                                                     (+ 1 I)
                                                     A B SZ))))))
         :hints(("Goal" :in-theory (enable booth-sum-impl)))))

; And here is the main ACL2 lemma to show booth-encoding/addition really do a
; multiply.  Note that this is just an ACL2 theorem, it has nothing to do with
; the circuits above.

(local
 (defthm booth-sum-of-products-correct
   (implies (AND (NATP A)
                 (NATP B)
                 (< A (EXPT 2 16))
                 (< B (EXPT 2 16)))
            (let ((pp0 (boothmul-pp-spec 16 #x0 a b))
                  (pp1 (boothmul-pp-spec 16 #x1 a b))
                  (pp2 (boothmul-pp-spec 16 #x2 a b))
                  (pp3 (boothmul-pp-spec 16 #x3 a b))
                  (pp4 (boothmul-pp-spec 16 #x4 a b))
                  (pp5 (boothmul-pp-spec 16 #x5 a b))
                  (pp6 (boothmul-pp-spec 16 #x6 a b))
                  (pp7 (boothmul-pp-spec 16 #x7 a b)))
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
                             signed-byte-p
                             boothmul-pp-spec))))))


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


(local
 (defthm boothmul-decomp-is-boothmul
   (implies (boothmul-decomp-autohyps)
            (b* ( ;; Run the decomposed circuit to get the partial products
                 (in-alist1  (boothmul-decomp-autoins))
                 (out-alist1 (stv-run (boothmul-decomp) in-alist1))

                 ;; Grab the resulting partial products out.
                 ((assocs pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7) out-alist1)

                 ;; Run the decomposed circuit again, sticking the partial
                 ;; products back in on the inputs.  (This is a rather subtle use
                 ;; of the autoins macro, which uses the bindings for pp0...pp7
                 ;; above.)
                 (in-alist2 (boothmul-decomp-autoins))
                 (out-alist2 (stv-run (boothmul-decomp) in-alist2))

                 ;; Separately, run the original circuit.
                 (orig-in-alist  (boothmul-direct-autoins))
                 (orig-out-alist (stv-run (boothmul-direct) orig-in-alist)))

              (equal
               ;; The final answer from running the decomposed circuit the second
               ;; time, after feeding its partial products back into itself.
               (cdr (assoc 'o out-alist2))

               ;; The answer from running the original circuit.
               (cdr (assoc 'o orig-out-alist)))))
   :hints (("goal"
            ;; Need to know that the intermediate values are non-X:
            :use ((:instance boothmul-pps-types))
            :in-theory (stv-decomp-theory))
           (and stable-under-simplificationp
                '(:in-theory (union-theories (stv-decomp-theory)
                                             '(pairlis$-of-cons
                                               pairlis$-when-atom)))))))

; For reference, here is the same decomposition lemma, but proven using GL
; instead of the specialized theory:

(local
 (def-gl-thm boothmul-decomp-is-boothmul-via-GL
   :hyp (boothmul-decomp-autohyps)
   :concl (b* ((in-alist1 (boothmul-decomp-autoins))
               (out-alist1 (stv-run (boothmul-decomp) in-alist1))

               ((assocs pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7) out-alist1)
               (in-alist2 (boothmul-decomp-autoins))
               (out-alist2 (stv-run (boothmul-decomp) in-alist2))

               (orig-in-alist (boothmul-direct-autoins))
               (orig-out-alist (stv-run (boothmul-direct) orig-in-alist)))

            (equal (cdr (assoc 'o out-alist2))
                   (cdr (assoc 'o orig-out-alist))))
   :g-bindings (boothmul-decomp-autobinds)))

(local (in-theory (disable boothmul-decomp-is-boothmul-via-GL)))

; All that remains is to chain the above facts together.
;
;   1. By this last GL lemma, we know how to express the result of
;      boothmul-direct in terms of the two-phase computation that
;      boothmul-decomp carries out.
;
;   2. By our two main GL lemmas about boothmul-decomp, we have ugly
;      ACL2 definitions of the partial-product/sum computations that
;      the decomposed module can do.
;
;   3. By our ACL2 lemma booth-sum-of-products-correct, we know that
;      together these ACL2 computations are just a multiply.
;
; Hence the whole thing does a multiply.  This chaining-together is just an
; ordinary (non-GL) ACL2 theorem:

(local (defthm boothmul-pp-spec-bound
         (< (boothmul-pp-spec 16 i a b) (expt 2 18))
         :hints(("Goal" :in-theory (enable boothmul-pp-spec)))
         :rule-classes :linear))

(defthm boothmul-correct
  (implies (boothmul-direct-autohyps)
           (b* ((in-alist  (boothmul-direct-autoins))
                (out-alist (stv-run (boothmul-direct) in-alist))
                (o         (cdr (assoc 'o out-alist))))
             (equal o (loghead 32 (* (logext 16 a) (logext 16 b))))))
  :hints (("goal" :in-theory (disable stv-run
                                      (boothmul-direct) boothmul-direct
                                      (boothmul-decomp) boothmul-decomp
                                      boothmul-decomp-is-boothmul
                                      ash-of-n-0
                                      right-shift-to-logtail)
           :use ((:instance boothmul-decomp-is-boothmul
                            (pp0 0)
                            (pp1 0)
                            (pp2 0)
                            (pp3 0)
                            (pp4 0)
                            (pp5 0)
                            (pp6 0)
                            (pp7 0))))))


