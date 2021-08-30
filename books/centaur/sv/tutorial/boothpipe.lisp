; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2012-2015 Centaur Technology
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
;                   Sol Swords <sswords@centtech.com>


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
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "support")
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "oslib/ls" :dir :system)

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
(local (include-book "centaur/aig/g-aig-eval" :dir :system))
(local (include-book "booth-support"))
(local (gl::def-gl-clause-processor boothpipe-glcp))

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

(def-saved-event boothpipe-direct-stv
  (defsvtv boothpipe-direct
    ;; Set up our run of the E module.
    :design *boothpipe*
    :labels         '(c0   c1 c1  c2 c2 c3 c3)
    :inputs '(("en"   en)
              ("clk"  0   ~)
              ("a"    a   _)
              ("b"    b   _))
    :outputs '(("o"   _   _   _   _   _   _   o))
    :parents (decomposition-proofs) ;; xdoc stuff, not needed
    ))

(local
 (assert!
  ;; Make sure it can multiply 3*5.
  (b* ((in-alist  (list (cons 'a 3)
                        (cons 'b 5)
                        (cons 'en 1)))
       (out-alist (svtv-run (boothpipe-direct) in-alist))
       (result    (cdr (assoc 'o out-alist))))
    (equal result 15))))

#||
(svtv-debug (boothpipe-direct)
            (list (cons 'a 3)
                  (cons 'b 5)
                  (cons 'en 1)))
||#

(def-saved-event boothpipe-step1-stv
  (defsvtv boothpipe-step1
    :design *boothpipe*
    :inputs '(("en"         en)
              ("clk"        0   ~)
              ("a"          a   _)
              ("b"          b   _))
    :internals '(("minusb" _   _   minusb)
                 ("pp01_c2[35:18]"    _   _   _   _   pp0)
                 ("pp01_c2[17:0]"     _   _   _   _   pp1)
                 ("pp23_c2[35:18]"    _   _   _   _   pp2)
                 ("pp23_c2[17:0]"     _   _   _   _   pp3)
                 ("pp45_c2[35:18]"    _   _   _   _   pp4)
                 ("pp45_c2[17:0]"     _   _   _   _   pp5)
                 ("pp67_c2[35:18]"    _   _   _   _   pp6)
                 ("pp67_c2[17:0]"     _   _   _   _   pp7))
    :parents (decomposition-proofs) ;; xdoc stuff, not needed
    ))

; You could now try to directly prove that this circuit multiplies, using
; something like this.  But this is very unlikely to work, and would require
; huge amounts of time and memory.

#||
   (def-gl-thm boothpipe-correct-direct
     :hyp (boothpipe-direct-autohyps)
     :concl (b* ((in-alist  (boothpipe-direct-autoins))
                 (out-alist (stv-run (boothpipe-direct) in-alist))
                 (o         (cdr (assoc 'o out-alist))))
              (equal o (* a b)))
     :g-bindings (stv-easy-bindings (boothpipe-direct)
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
; terms of our original circuit, boothpipe-direct!
;
; However, boothpipe-decomp will be very useful for getting to this final
; theorem, as we'll now see.
;
;
; To emphasize that our final theorem has nothing to do with boothpipe-decomp,
; we make the whole STV local.

(def-saved-event boothpipe-step2-stv
  (defsvtv boothpipe-step2
    :design *boothpipe*
    :inputs '(("en"         en)
              ("clk"        0   ~))
    :overrides '(("pp01_c2[35:18]"    _   _   _   _   pp0)
                 ("pp01_c2[17:0]"     _   _   _   _   pp1)
                 ("pp23_c2[35:18]"    _   _   _   _   pp2)
                 ("pp23_c2[17:0]"     _   _   _   _   pp3)
                 ("pp45_c2[35:18]"    _   _   _   _   pp4)
                 ("pp45_c2[17:0]"     _   _   _   _   pp5)
                 ("pp67_c2[35:18]"    _   _   _   _   pp6)
                 ("pp67_c2[17:0]"     _   _   _   _   pp7))
    :outputs   '(("o"                 _   _   _   _   _   _   o))
    :parents (decomposition-proofs) ;; xdoc stuff, not needed
    ))


(local (gl::gl-satlink-mode))

#||

(svtv-debug (boothpipe-step2)
            (list (cons 'en 1)
                  (cons 'pp0 10)
                  (cons 'pp1  0)
                  (cons 'pp2 10)
                  (cons 'pp3 10)
                  (cons 'pp4  0)
                  (cons 'pp5 10)
                  (cons 'pp6  0)
                  (cons 'pp7 10)))


(defsvtv boothpipe-ovtest
  :design *boothpipe*
  :inputs '(("en" en)
            ("a" a _)
            ("b" b _)
            ("clk" 0 ~))
  :overrides '(("minusb" _ _ minusb))
  :internals '(("minusb" _ _ minusb)
               ("pp0"    _ _ pp0)))


||#

(local
 (progn
   (defun my-glucose-config ()
     (declare (xargs :guard t))
     (satlink::make-config :cmdline "glucose -model"
                           :verbose t
                           :mintime 1/2
                           :remove-temps t))

   (defattach gl::gl-satlink-config my-glucose-config)))

(local
 (def-saved-event recomposition-proof
   (defthm boothpipe-decomp-is-boothpipe
     (implies (boothpipe-direct-autohyps :en en :a a :b b)
              (b* ( ;; Run the first part of the circuit to get the partial products
                   (in-alist1  (boothpipe-step1-autoins
                                :en en :a a :b b))
                   (out-alist1 (svtv-run (boothpipe-step1) in-alist1))

                   ;; Get the results from the output and stick them into an
                   ;; input alist for step2.  Some control signals from the
                   ;; original input alist also are needed.
                   (in-alist2 (boothpipe-step2-alist-autoins (append out-alist1 in-alist1)))

                   ;; Run the second part of the circuit on the results from the
                   ;; first part, summing the partial products.
                   (out-alist2 (svtv-run (boothpipe-step2) in-alist2))

                   ;; Separately, run the original circuit.
                   (orig-in-alist  (boothpipe-direct-autoins))
                   (orig-out-alist (svtv-run (boothpipe-direct) orig-in-alist)))

                (equal
                 ;; The final answer from running the decomposed circuit the second
                 ;; time, after feeding its partial products back into itself.
                 (cdr (assoc 'o out-alist2))

                 ;; The answer from running the original circuit.
                 (cdr (assoc 'o orig-out-alist)))))
     :hints((svdecomp-hints :hyp (boothpipe-direct-autohyps)
                            :g-bindings (boothpipe-direct-autobinds))))))

(local
 (gl::def-gl-thm boothpipe-pp-correct
   ;; Main Lemma 1.  Partial Products Part is Correct.
   ;; This is a very easy proof for Glucose, taking about 1.5 seconds.
   ;; The stuff done with the output alist is confusing but is what we want for composition.
   :hyp (boothpipe-step1-autohyps)
   :concl (b* ((in-alist  (boothpipe-step1-autoins))
               (out-alist (svtv-run (boothpipe-step1) in-alist)))
            (implies (eql en 1)
                     (and (equal (cdr (assoc 'pp0 out-alist)) (boothpipe-pp-spec 16 #x0 a b))
                          (equal (cdr (assoc 'pp1 out-alist)) (boothpipe-pp-spec 16 #x1 a b))
                          (equal (cdr (assoc 'pp2 out-alist)) (boothpipe-pp-spec 16 #x2 a b))
                          (equal (cdr (assoc 'pp3 out-alist)) (boothpipe-pp-spec 16 #x3 a b))
                          (equal (cdr (assoc 'pp4 out-alist)) (boothpipe-pp-spec 16 #x4 a b))
                          (equal (cdr (assoc 'pp5 out-alist)) (boothpipe-pp-spec 16 #x5 a b))
                          (equal (cdr (assoc 'pp6 out-alist)) (boothpipe-pp-spec 16 #x6 a b))
                          (equal (cdr (assoc 'pp7 out-alist)) (boothpipe-pp-spec 16 #x7 a b))
                          (boothpipe-step2-alist-autohyps (append out-alist in-alist))
                          )))
   :g-bindings (boothpipe-step1-autobinds)))





; We'll now prove, separately, our two main lemmas, about the decomposed
; circuit.  We'll attack these using SAT.  This should be familiar if you've
; already seen sat.lsp.



;; Main Lemma 2.  Addition Part is Correct.

(local
 (gl::def-gl-thm boothpipe-sum-correct
   ;; Note: For decompositions with more intermediate terms, it could be good
   ;; to prove this, but then use its result to prove a form of it using
   ;; alist-autoins and alist-autohyps.  With this version, to prove the final
   ;; theorem below we need to enable boothpipe-step2-autohyps and prove that
   ;; the requirements are true of the outputs from step 1, which could be
   ;; expensive if there are more intermediate results.

   ;; This takes about 13 seconds for Glucose.
   :hyp (boothpipe-step2-autohyps)
   :concl (b* ((in-alist  (boothpipe-step2-autoins))
               (out-alist (svtv-run (boothpipe-step2) in-alist))
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
            (implies (eql 1 en)
                     (equal o res)))
   :g-bindings (boothpipe-step2-autobinds)))




;; (local
;;  ;; This is trivially proved by instantiating boothpipe-pp-correct.  But we need
;;  ;; to know this specifically later on when we want to show that the
;;  ;; composition of the two steps is equivalent to the whole run.
;;  (defthm boothpipe-pps-types ;; BOZO fix me
;;    (b* ((pp0 (BOOTHPIPE-PP-SPEC 16 0 A B))
;;         (pp1 (BOOTHPIPE-PP-SPEC 16 1 A B))
;;         (pp2 (BOOTHPIPE-PP-SPEC 16 2 A B))
;;         (pp3 (BOOTHPIPE-PP-SPEC 16 3 A B))
;;         (pp4 (BOOTHPIPE-PP-SPEC 16 4 A B))
;;         (pp5 (BOOTHPIPE-PP-SPEC 16 5 A B))
;;         (pp6 (BOOTHPIPE-PP-SPEC 16 6 A B))
;;         (pp7 (BOOTHPIPE-PP-SPEC 16 7 A B)))
;;      (implies (unsigned-byte-p 1 en)
;;               (boothpipe-step2-alist-autohyps)))
;;    :hints (("goal" :use boothpipe-pp-correct
;;             :in-theory '((:t boothpipe-pp-spec)
;;                          boothpipe-step2-autohyps-fn
;;                          boothpipe-pp-spec
;;                          natp-compound-recognizer
;;                          unsigned-byte-p-loghead)))))



;; This is the version referenced in the comment above.
(local
 (defthmd boothpipe-sum-correct-alternate-form
   (implies (boothpipe-step2-alist-autohyps inalist)
            (b* ((in-alist  (boothpipe-step2-alist-autoins inalist))
                 ((assocs pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 en) inalist)
                 (out-alist (svtv-run (boothpipe-step2) in-alist))
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
              (implies (eql 1 en)
                       (equal o res))))
   :hints (("goal" :in-theory '(boothpipe-step2-alist-autoins
                                boothpipe-step2-alist-autohyps
                                boothpipe-sum-correct)))))

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
;      boothpipe-direct in terms of the two-phase computation that
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

(local (defthm boothpipe-direct-autohyps-implies-step1-autohyps
         (implies (boothpipe-direct-autohyps)
                  (boothpipe-step1-autohyps))
         :hints(("Goal" :in-theory (enable boothpipe-direct-autohyps
                                           boothpipe-step1-autohyps)))))

(defthm boothpipe-correct
  (implies (and (boothpipe-direct-autohyps)
                (eql en 1))
           (b* ((in-alist  (boothpipe-direct-autoins))
                (out-alist (svtv-run (boothpipe-direct) in-alist))
                (o         (cdr (assoc 'o out-alist))))
             (equal o (loghead 32 (* (logext 16 a) (logext 16 b))))))
  :hints (("goal" :in-theory (e/d (assoc-of-append)
                                  (svtv-run
                                   (boothpipe-direct) boothpipe-direct
                                   (boothpipe-step1) boothpipe-step1
                                   (boothpipe-step2) boothpipe-step2
                                   boothpipe-decomp-is-boothpipe
                                   unsigned-byte-p
                                   logext loghead ash
                                   boothpipe-step2-autoins-fn
                                   boothpipe-step1-autoins-fn))
           :use ((:instance boothpipe-decomp-is-boothpipe)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (boothpipe-direct-autohyps
                                  boothpipe-step2-alist-autoins
                                  boothpipe-step2-alist-autohyps
                                  boothpipe-step2-autohyps
                                  assoc-of-append)
                                 (svtv-run
                                  (boothpipe-direct) boothpipe-direct
                                  (boothpipe-step1) boothpipe-step1
                                  (boothpipe-step2) boothpipe-step2
                                  unsigned-byte-p
                                  boothpipe-decomp-is-boothpipe
                                  logext loghead ash))))))






(deftutorial decomposition-proofs
  :parents (sv-tutorial)
  :short "Proof by decomposing and re-composing a hardware model"
  :long "

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

<p>The file \"boothpipe.lisp\" where this documentation topic is defined
contains an example to show how to do this with SVEX.  In this topic we will
discuss a few critical parts of the process, but for a more complete picture
see that file and the comments in it.</p>

<h4>STV Setup for Decomposition</h4>

<p>In the boothpipe example, the intermediate signals to split the pipeline on
are the partial products @('pp0')...@('pp7').  We'll have one STV that says how
to run the whole module, and about which we'll prove the final theorem -- we'll
call this the Direct model.  We'll additionally define one STV that extracts
the partial products given the circuit inputs -- Part 1 -- and one STV that
takes the partial products as inputs and gets the outputs -- Part 2.</p>

<p><see topic='@(url boothpipe-direct)'>Direct</see>:</p>
@(`(:code ($ boothpipe-direct-stv))`)
<p><see topic='@(url boothpipe-step1)'>Part 1</see>:</p>
@(`(:code ($ boothpipe-step1-stv))`)
<p><see topic='@(url boothpipe-step2)'>Part 2</see>:</p>
@(`(:code ($ boothpipe-step2-stv))`)

<h4>Composing the Proof</h4>

<p>The basic steps for completing the top-level proof we want are as
follows:</p>

<ol>
<li>Prove that Part 1 meets its spec.</li>
<li>Prove that Part 2 meets its spec.</li>
<li>Prove that the composition of the Part 1 and Part 2 hardware models are
equivalent to the Direct model.</li>
<li>Prove that the composition of the spec for Part 1 and the spec for Part 2
equals the top-level spec.</li>
<li>Put steps 1 through 4 together to prove that the Direct model meets the
top-level spec.</li>
</ol>

<p>Steps 1 and 2 can be done via bit-blasting proofs as discussed in the
previous section of the tutorial (@(see proofs-with-stvs)).  Steps 4 and 5 are
done using traditional theorem proving.  So here we'll focus on Step 3, for
which the svex package provides some automation.</p>

<h4>Hardware Recomposition Proof Automation</h4>

<p>The hardware recomposition proof for the boothpipe example is shown
below:</p>

@(`(:code ($ recomposition-proof))`)

<p>In this theorem, we show that running Step 1 followed by Step 2 results in
the same result as running the whole model (Direct).  The steps followed by the
@('b*') form work as follows: First we create an input alist for Step 1 with
the autoins function; this gathers our theorem variables @('en'), @('a'), and
@('b') into an alist to pass to @('svtv-run').  Then we run Step 1 to get
@('out-alist1').  To create the input to Step 2, we need some output signals
from Step 1 along with some input signals that are common to both steps (namely
@('en')), so we append @('out-alist1') and @('in-alist1') and extract
@('in-alist2') from that union, then run Step 2 to get @('out-alist2').
Finally, we run the Direct model and compare its output to that of
@('out-alist2').</p>

<p>The computed hint @('svdecomp-hints') used to prove this theorem is
documented in @(see svex-decomp).  In most cases, it suffices to give the hint
form the two keyword arguments provided: @(':hyp') and @(':bindings'), which
usually should be the autohyps and autobindings for the whole (Direct) model.
Also, it is generally best to be in SAT mode rather than BDD mode for this type
of proof; good performance of this proof relies on the fact that it is
comparing two very similar formulas -- this is very helpful for SAT, but
doesn't matter for BDDs, which will just build the (expensive) representations
for both entire formulas and compare them.</p>

")

(make-event
 (cons 'progn (recreate-saved-forms-table (table-alist 'saved-forms-table (w state)))))
