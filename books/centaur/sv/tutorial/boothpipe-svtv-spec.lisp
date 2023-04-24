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

;; (def-saved-event boothpipe-run-refinement
;;   (def-svtv-refinement boothpipe-run boothpipe-data))

;; (def-saved-event boothpipe-run-ideal
;;   (def-svtv-refinement boothpipe-run boothpipe-data :ideal boothpipe-run-ideal))

(def-saved-event boothpipe-spec
  (def-svtv-refinement boothpipe-run boothpipe-data :svtv-spec boothpipe-spec))



(local
 (assert!
  ;; Make sure it can multiply 3*5.
  (b* ((in-alist  (list (cons 'a 3)
                        (cons 'b 5)
                        (cons 'en 1)))
       (out-alist (svtv-run (boothpipe-run) in-alist))
       (result    (cdr (assoc 'o out-alist))))
    (equal result 15))))

;; (local
;;  (assert!
;;   ;; Make sure boothpipe-ideal-exec produces the same answer.
;;   (b* ((in-alist  (list (cons 'a 3)
;;                         (cons 'b 5)
;;                         (cons 'en 1)))
;;        (out-alist (boothpipe-ideal-exec in-alist '(o)))
;;        (result    (cdr (assoc 'o out-alist))))
;;     (equal result 15))))

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
         (local (table sv::svtv-generalized-thm-defaults :svtv-spec 'boothpipe-spec))
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
      (- (cw "form: ~x0~%" form))
      ((er (cons ?stobjs-out (list ?eval-err form ?replaced-state)))
       (trans-eval-default-warning form 'find-boothpipe-pp-correct-fgl state t))
      ((when eval-err)
       (er soft 'find-boothpipe-pp-correct-fgl "~@0" eval-err))
      (- (cw "form: ~x0~%" form))
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
   (implies (AND (unsigned-byte-p 16 a)
                 (unsigned-byte-p 16 b))
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
    :no-lemmas t))

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
                  (out-alist (svtv-spec-run (boothpipe-spec) in-alist))
                  (o         (svex-env-lookup 'o out-alist)))
               (equal o (loghead 32 (* (logext 16 a) (logext 16 b))))))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup-of-cons
                                    4vec-p-when-integerp
                                    hons-intersection-force-execute)
                                   ((svex-env-lookup)))))))

(def-saved-event boothpipe-correct-svtv
  (defthm boothpipe-correct-svtv
    (implies (and (unsigned-byte-p 16 a)
                  (unsigned-byte-p 16 b))
             (b* ((in-alist (list `(a . ,a)
                                  `(b . ,b)
                                  `(en . 1)))
                  (out-alist (svtv-run (boothpipe-run) in-alist))
                  (o         (svex-env-lookup 'o out-alist)))
               (equal o (loghead 32 (* (logext 16 a) (logext 16 b))))))
    :hints(("Goal" :in-theory (e/d (SVTV-RUN-OF-BOOTHPIPE-RUN-IS-SVTV-SPEC-RUN-OF-BOOTHPIPE-SPEC))))))


