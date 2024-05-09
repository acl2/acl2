;;;
;;;  INTEL CONFIDENTIAL
;;;
;;;  Copyright 2022 Intel Corporation All Rights Reserved.
;;;
;;;  The source code contained or described herein and all documents related
;;;  to the source code ("Material") are owned by Intel Corporation or its
;;;  suppliers or licensors. Title to the Material remains with Intel
;;;  Corporation or its suppliers and licensors. The Material contains trade
;;;  secrets and proprietary and confidential information of Intel or its
;;;  suppliers and licensors. The Material is protected by worldwide copyright
;;;  and trade secret laws and treaty provisions. No part of the Material may
;;;  be used, copied, reproduced, modified, published, uploaded, posted,
;;;  transmitted, distributed, or disclosed in any way without Intel's prior
;;;  express written permission.
;;;
;;;  No license under any patent, copyright, trade secret or other intellectual
;;;  property right is granted to or conferred upon you by disclosure or
;;;  delivery of the Materials, either expressly, by implication, inducement,
;;;  estoppel or otherwise. Any license under such intellectual property rights
;;;  must be express and approved by Intel in writing.
;;;
;;;================================================================================================

(in-package "SRTDIV")

(include-book "build/ifdef" :dir :system)

;;;;; NOTE: See the README -- this IFDEF covers the entire file and makes it
;;;;; certify as an empty book by default.  Setting this environment variable
;;;;; means you've downloaded the divider implementation as described in the
;;;;; README so that we can do the proofs.
(acl2::ifdef "SRTDIV_HAS_IMPLEMENTATION"

(include-book "centaur/sv/svtv/svtv-generalize" :dir :system)
(include-book "centaur/sv/svtv/svtv-stobj-defsvtv" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(local (include-book "centaur/fgl/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :Dir :system))
(local (include-book "centaur/bitops/integer-length" :Dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :Dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (include-book "centaur/bitops/width-find-rule" :dir :system))
(local (include-book "centaur/aignet/transforms" :dir :System))
(local (include-book "centaur/ipasir/ipasir-backend" :dir :system))
(value-triple (acl2::tshell-ensure))

;;;;; This file contains a proof of correctness for the quotient and remainder
;;;;; computed by a simple 32-bit radix-4 nonrestoring SRT divider.

;;;;; Tutorial-style commments are preceded by five semicolons throughout.


;;;;; Arithmetic lemmas -- nothing too interesting
(defsection-progn local-lemmas
  (local (in-theory (disable unsigned-byte-p
                             signed-byte-p
                             (tau-system)
                             acl2::hons-dups-p)))

  (local (defthm unsigned-byte-p-by-integer-length
           (implies (and (natp x)
                         (<= (integer-length x) n)
                         (natp n))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

  (local (defthm logext-of-loghead
           (implies (<= (pos-fix m) (nfix n))
                    (equal (logext m (loghead n x))
                           (logext m x)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (fty::bitp-when-unsigned-byte-p-1
                                            sv::our-logext-identity
                                            acl2::logext-identity
                                            acl2::loghead-identity))))))

  (local (defthm signed-byte-p-when-unsigned-byte-p
           (implies (and (equal w (1- m))
                         (bind-free (bitops::width-find-rule-bind-free 'unsigned-byte-p w x mfc state)
                                    (bitops::w2))
                         (unsigned-byte-p bitops::w2 x)
                         (integerp m)
                         (<= (+ 1 bitops::w2) m))
                    (signed-byte-p m x))
           :hints(("Goal" :in-theory (e/d (signed-byte-p unsigned-byte-p)
                                          (acl2::expt-is-weakly-increasing-for-base>1))
                   :use ((:instance ACL2::EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                          (r 2) (i bitops::w2) (j (+ -1 m))))
                   :do-not-induct t))))

  (local
   (defthm unsigned-byte-p-of-mod
     (implies (and (unsigned-byte-p n x)
                   (natp y))
              (unsigned-byte-p n (mod x y)))
     :hints(("Goal" :in-theory (enable mod unsigned-byte-p))))))


;; turn off FGL accumulated-persistence so we don't print so much
(local (table fgl::fgl-config-table :prof-enabledp nil))


;;;;; Parse the design using VL
(encapsulate nil
  (local (include-book "centaur/vl/loader/top" :dir :system))
  (local (include-book "oslib/top" :dir :system))
  (local (include-book "std/io/read-file-lines" :dir :system))


  (defconsts (*srt-vl-design* state)
    (b* (((mv (vl::vl-loadresult res) state)
          (vl::vl-load (vl::make-vl-loadconfig
                        :start-files '("SRT-4-DIVISION/src/srt4/srt_4_div.v"
                                       "SRT-4-DIVISION/src/srt4/radix4_table.v"
                                       "SRT-4-DIVISION/src/srt4/pre_processing.v"
                                       "SRT-4-DIVISION/src/srt4/on_the_fly_conversion.v")))))
      (vl::cw-unformatted (vl::vl-reportcard-to-string (vl::vl-design-reportcard res.design) :elide nil))
      (mv res.design state))))



;;;;; Transform the VL design to an SV design and define our SVTV.
(encapsulate nil
  (local (include-book "centaur/sv/vl/top" :dir :system))

  (defconsts (*srt-svex-design*
              *srt-simplified-good*
              *srt-simplified-bad*)
    (b* (((mv errmsg svex-design good bad)
          (vl::vl-design->sv-design "srt_4_div" *srt-vl-design*
                                    (vl::make-vl-simpconfig))))
      (cw "Reportcard for good mods:~%")
      (vl::cw-unformatted (vl::vl-reportcard-to-string (vl::vl-design-reportcard good)))
      (cw "Reportcard for bad mods:~%")
      (vl::cw-unformatted (vl::vl-reportcard-to-string (vl::vl-design-reportcard bad)))
      (and errmsg
           (raise "~@0~%" errmsg))
      (mv (hons-copy svex-design) good bad)))

  (sv::defsvtv$ srt-run
    :design *srt-svex-design*
    :phases
    `((:label reset
      ;;;;; Set up the clock (toggling every phase) and trigger reset (active low signal)
      :inputs (("clk" 0 :toggle 1)
               ("rst_n" 0 :hold 2)))
     (:label post-reset
      :delay 2
      ;;;;; Turn off reset (forevermore)
      :inputs (("rst_n" 1 :hold t)
               ("start" 0)))
     (:label start
      :delay 2
      ;;;;; Start the operation and provide the data inputs
      :inputs (("start" 1)
               ("dividend" dividend)
               ("divisor"  divisor))
      ;;;;; Set up a couple of conditional override/output triples as potential
      ;;;;; decomposition cutpoints
      :overrides (("iterations" iters :cond iters-ovr :output iters)
                  ("recovery" recov :cond recov-ovr :output recov)))
     (:label div0
      :delay 2
      ;; counter = 0, iterations = 2
      :inputs (("start" 0 :hold t))
      ;;;;; More potential decomposition cutpoints.  We'll primarily end up
      ;;;;; using just the divisor_reg and w_reg signals for this but it
      ;;;;; doesn't hurt to have more for visibility and control.
      :overrides (("divisor_reg" norm-div :cond norm-div-ovr :output norm-div)
                  ("w_reg" w0 :cond w0-ovr :output w0)
                  ("q_table" guess0 :cond guess0-ovr :output guess0)
                  ("u3.q_reg" q0 :cond q0-ovr :output q0)
                  ("u3.qm_reg" qm0 :cond qm0-ovr :output qm0)))
     ;;;;; Produce similar overrides for the following 16 cycles, numbering the
     ;;;;; signal names.
     ,@(loop$ for i from 1 to 16 collect
             (flet ((suffix (sym n)
                            (intern-in-package-of-symbol (concatenate 'string (symbol-name sym) (coerce (explode-atom n 10) 'string))
                                                         'a-symbol-from-this-package))
                    (suffix-ovr (sym n)
                                (intern-in-package-of-symbol (concatenate 'string (symbol-name sym) (coerce (explode-atom n 10) 'string) "-OVR")
                                                             'a-symbol-from-this-package)))
                   (let ((w (suffix 'w i))
                         (w-ovr (suffix-ovr 'w i))
                         (guess (suffix 'guess i))
                         (guess-ovr (suffix-ovr 'guess i))
                         (q (suffix 'q i))
                         (q-ovr (suffix-ovr 'q i))
                         (qm (suffix 'qm i))
                         (qm-ovr (suffix-ovr 'qm i))
                         (finish (suffix 'finish i)))
                     `(:label ,(suffix 'div i)
                       :delay 2
                       :outputs (("divfinish" ,finish))
                       ;; counter = i
                       :overrides (("w_reg" ,w :cond ,w-ovr :output ,w)
                                   ("q_table" ,guess :cond ,guess-ovr :output ,guess)
                                   ("u3.q_reg" ,q :cond ,q-ovr :output ,q)
                                   ("u3.qm_reg" ,qm :cond ,qm-ovr :output ,qm))))))
     (:label finish
      ;;;;; Get the outputs.
      :outputs (("reminder" remainder)
                ("quotient" quotient)
                ("divfinish" finish)
                ("diverror" error))
      :overrides (("w_reg" w17 :cond w17-ovr :output w17)
                  ("u3.q_reg" q17 :cond q17-ovr :output q17)
                  ("u3.qm_reg" qm17 :cond qm17-ovr :output qm17))))

    :define-macros nil)


  ;;;;; Testbench to run the divider and check the resulting quotient/remainder
  ;;;;; against ACL2's built in floor and mod.
  (define check-srt ((dividend natp) (divisor natp))
    (b* (((sv::svassocs (impl-quo 'quotient) (impl-rem 'remainder) (impl-err 'error))
          (sv::svtv-run (srt-run) `((dividend . ,dividend)
                                    (divisor . ,divisor))))
         ((when (eql divisor 0))
          (or (equal impl-err 1)
              (cw "failed to error on div by zero~%")))
         (spec-quo (floor dividend divisor))
         (spec-rem (mod   dividend divisor)))
      (or (and (equal impl-quo spec-quo)
               (equal impl-rem spec-rem)
               (equal impl-err 0))
          (cw "failed: ~s0 / ~s1~%/ spec: ~s2~%  impl: ~s3~%%% spec: ~s4~%  impl: ~s5~%"
              (str::hexify dividend) (str::hexify divisor)
              (str::hexify spec-quo) (str::hexify impl-quo)
              (str::hexify spec-rem) (str::hexify impl-rem)))))


  (assert-event (check-srt #ux8000_0000 #ux4000_0000))

  (assert-event (check-srt #ux5000_0000 #ux3E00_0000))
  (assert-event (check-srt #uxDEAD_0000 #ux0000_0005))
  (assert-event (check-srt #uxDEAD_0000 #ux0000_0003))
  (assert-event (check-srt #uxDEAD_0000 #ux0000_0001))

  ;;;;; Export the contents of the svtv-data stobj.  This is a prerequisite for
  ;;;;; the def-svtv-refinement event below.
  (sv::def-svtv-data-export srt-data))
       


;;;;; Prove the override transparency property for the overrides in srt-run.
;;;;; This lets us use def-svtv-generalized-thm to do symbolic simulation with
;;;;; overrides and derive theorems without overrides.
(sv::def-svtv-refinement srt-run srt-data)


;;;;; Set up defaults for def-svtv-generalized-thm -- the SVTV we're
;;;;; using, and that we should always assume input/override variables are
;;;;; unsigned-bytes.

(local (table sv::svtv-generalized-thm-defaults :svtv 'srt-run))
(local (table sv::svtv-generalized-thm-defaults :unsigned-byte-hyps t))

;;;;; First few internal signals we need to specify: normalized divisor,
;;;;; iteration number, recovery shift amount, and w0, the adjusted dividend.


;;;;; Definition for the normed divisor internal signal
(define srt-div-norm-div ((divisor integerp))
  :returns (norm natp :rule-classes :type-prescription)
  (b* ((divisor (loghead 32 divisor)))
    (ash divisor (- 33 (integer-length divisor))))
  ///
  (defret integer-length-of-<fn>
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (integer-length norm) 33)))

  (defret width-of-<fn>
    (unsigned-byte-p 33 norm))

  (defret <fn>-of-loghead
    (implies (<= 32 (nfix n))
             (Equal (srt-div-norm-div (loghead n divisor))
                    norm))))

;;;;; Prove that the internal signal NORM-DIV equals our spec function,
;;;;; srt-div-norm-div.  No overrides here.
(sv::def-svtv-generalized-thm srt-div-norm-div-formula
  :input-vars (divisor dividend)
  :output-vars (norm-div)
  :hyp (not (equal divisor 0))
  :concl (equal norm-div (srt-div-norm-div divisor)))


;;;;; Iteration count spec
(define srt-div-iters ((divisor integerp))
  :returns (iters posp :rule-classes :type-prescription)
  (b* ((divisor (loghead 32 divisor)))
    (floor (- 35 (integer-length divisor)) 2))
  ///
  (defret <fn>-of-loghead
    (implies (<= 32 (nfix n))
             (Equal (srt-div-iters (loghead n divisor))
                    iters)))

  (defret <fn>-bounds
    (<= iters 17)
    :rule-classes :linear)

  (defret <fn>-width
    (unsigned-byte-p 5 iters)
    :hints(("Goal" :in-theory (e/d (unsigned-byte-p) (<fn>))))))

;;;;; Iteration count signal ITERS equals spec
(sv::def-svtv-generalized-thm srt-div-iters-formula
  :input-vars (divisor)
  :output-vars (iters)
  :hyp (not (Equal divisor 0))
  :concl (equal iters (srt-div-iters divisor)))

;;;;; RECOV equals integer-length of the divisor
(sv::def-svtv-generalized-thm srt-div-recov-formula
  :input-vars (divisor)
  :output-vars (recov)
  :concl (equal recov
                (integer-length divisor)))

;;;;; Spec for W0, original partial remainder (shift of the dividend)
(define srt-div-w0 ((dividend integerp)
                    (divisor integerp))
  :returns (w0 natp :rule-classes :type-prescription)
  (b* ((dividend (loghead 32 dividend))
       (divisor (loghead 32 divisor)))
    (ash dividend (mod (- 35 (integer-length divisor)) 2)))
  ///
  (defret width-of-<fn>
    (unsigned-byte-p 33 w0))
  
  (defret <fn>-of-loghead
    (implies (<= 32 (nfix n))
             (and (Equal (srt-div-w0 (loghead n dividend) divisor)
                         w0)
                  (Equal (srt-div-w0 dividend (loghead n divisor))
                         w0)))))


;;;;; Initial partial remainder equals spec
(sv::def-svtv-generalized-thm srt-div-w0-formula
  :input-vars (divisor dividend)
  :output-vars (w0)
  :hyp (not (Equal divisor 0))
  :concl (equal w0
                (srt-div-w0 dividend divisor)))



;;;;; Each iteration, a quotient digit is picked between -2 and 2. We don't
;;;;; care exactly how the digit is picked, but we need to know that the digit
;;;;; is close enough, i.e. that the resulting next partial remainder is still
;;;;; in bounds.  What bounds do we need?

;;;;; Suppose partial remainder wi is the least allowable number in the range,
;;;;; and therefore we choose as our quotient guess -2, the least possible.  We
;;;;; need the next partial remainder,
;;;;; wi+1 = 4*(wi - (-2)*div), to also be in bounds, that is, greater than or
;;;;; equal to wi.  That is:
;;;;;    wi <= 4*(wi - div*(-2))  --> wi >= -8/3*div
;;;;; This is the lower bound we need for partial remainders.

;;;;; Similarly if we assume wi is the greatest allowable value and we choose
;;;;; quotient guess 2 (the greatest possible), we have a similar situation:
;;;;; wi >= wi+1 = 4*(wi - 2*div) --> wi <= 8/3*div.

;;;;; This function just checks that the partial remainder is within these
;;;;; bounds given the normed divisor.
(define srt-div-remainder-in-bounds ((w integerp)
                                     (div integerp))
  (b* ((w (logext 36 w)))
    (and (<= (* -8 div) (* 3 w))
         (<= (* 3 w) (* 8 div))))
  ///
  (defthm srt-div-remainder-in-bounds-of-logext
    (equal (srt-div-remainder-in-bounds (logext 36 w) div)
           (srt-div-remainder-in-bounds w div)))

  (defthm srt-div-remainder-in-bounds-of-loghead
    (equal (srt-div-remainder-in-bounds (loghead 36 w) div)
           (srt-div-remainder-in-bounds w div)))

  (defthm srt-div-remainder-in-bounds-of-ash-loghead
    (equal (srt-div-remainder-in-bounds (ash (loghead 36 w) 2) div)
           (srt-div-remainder-in-bounds (ash w 2) div))
    :hints (("goal" :use ((:instance srt-div-remainder-in-bounds-of-loghead
                           (w (ash w 2)))
                          (:instance srt-div-remainder-in-bounds-of-loghead
                           (w (ash (loghead 36 w) 2))))
             :in-theory (e/d (bitops::loghead-of-ash)
                             (srt-div-remainder-in-bounds-of-loghead
                              srt-div-remainder-in-bounds)))))

  (fgl::def-fgl-thm srt-div-remainder-in-bounds-of-initial
    (implies (and (unsigned-byte-p 32 dividend)
                  (unsigned-byte-p 36 div)
                  (equal (integer-length div) 33)
                  (bitp sh))
             (srt-div-remainder-in-bounds (ash dividend sh) div)))

  (fgl::def-fgl-thm srt-div-remainder-in-bounds-of-initial-1
    (implies (and (unsigned-byte-p 33 w)
                  (unsigned-byte-p 33 div)
                  (equal (integer-length div) 33))
             (srt-div-remainder-in-bounds w div))))



;;;;; Functional "spec" for the quotient digit guess at each iteration --
;;;;; basically we're just defining this as "what the hardware does, for
;;;;; iteration 0".  Then we prove the properties we need about it without
;;;;; saying exactly how it's implemented.  This is just the magnitude of the
;;;;; guess; the sign of the partial remainder determines its sign.
(define srt-div-guess-mag ((w integerp)
                           (div integerp))
  ;; Note: the dividend and divisor only matter insofar as they are not zero.
  ;; We set them to 1 here and prove below that the exact value is irrelevant.
  :returns (guess)
  (sv::svex-env-lookup 'guess0
                       (sv::svtv-run (srt-run)
                                     `((w0 . ,(loghead 36 w))
                                       (norm-div . ,(loghead 35 div))
                                       (w0-ovr . -1)
                                       (norm-div-ovr . -1)
                                       (divisor . 1)
                                       (dividend . 1))
                                     :include '(guess0)))
  ///

  (local
   (sv::def-svtv-generalized-thm srt-div-guess-mag-independent
     :input-vars (divisor dividend)
     :spec-override-vars (w0 norm-div)
     :output-vars (guess0)
     :hyp (and (not (equal 0 divisor))
               (not (equal 0 dividend)))
     :concl (and (equal guess0 (srt-div-guess-mag w0 norm-div))
                 (unsigned-byte-p 2 guess0)
                 (<= guess0 2))))

  (defret unsigned-byte-p-of-<fn>
    (unsigned-byte-p 2 guess)
    :hints (("goal" :use ((:instance srt-div-guess-mag-independent
                           (env `((w0 . ,(loghead 36 w))
                                  (norm-div . ,(loghead 35 div))
                                  (w0-ovr . -1)
                                  (norm-div-ovr . -1)
                                  (divisor . 1)
                                  (dividend . 1)))))
             :in-theory (e/d (sv::svex-env-lookup-of-cons
                              sv::4vec-p-when-integerp)
                             (srt-div-guess-mag-independent
                              (sv::svex-env-lookup))))))

  (defret integerp-of-<fn>
    (natp guess)
    :hints (("goal" :use ((:instance srt-div-guess-mag-independent
                           (env `((w0 . ,(loghead 36 w))
                                  (norm-div . ,(loghead 35 div))
                                  (w0-ovr . -1)
                                  (norm-div-ovr . -1)
                                  (divisor . 1)
                                  (dividend . 1)))))
             :in-theory (e/d (sv::svex-env-lookup-of-cons
                              sv::4vec-p-when-integerp)
                             (srt-div-guess-mag-independent
                              (sv::svex-env-lookup)))))
    :rule-classes :type-prescription)

  (defret bound-of-<fn>
    (<= guess 2)
    :hints (("goal" :use ((:instance srt-div-guess-mag-independent
                           (env `((w0 . ,(loghead 36 w))
                                  (norm-div . ,(loghead 35 div))
                                  (w0-ovr . -1)
                                  (norm-div-ovr . -1)
                                  (divisor . 1)
                                  (dividend . 1)))))
             :in-theory (e/d (sv::svex-env-lookup-of-cons
                              sv::4vec-p-when-integerp)
                             (srt-div-guess-mag-independent
                              (sv::svex-env-lookup)))))
    :rule-classes :linear)

  (defthm srt-div-guess-mag-of-loghead-w
    (equal (srt-div-guess-mag (loghead 36 w0) div)
           (srt-div-guess-mag w0 div)))

  (defthm srt-div-guess-mag-of-logext-w
    (equal (srt-div-guess-mag (logext 36 w0) div)
           (srt-div-guess-mag w0 div)))

  (defthm srt-div-guess-mag-of-loghead-div
    (equal (srt-div-guess-mag w0 (loghead 36 div))
           (srt-div-guess-mag w0 div))))


;;;;; Full quotient digit -- magnitude adjusted by sign of the partial
;;;;; remainder
(define srt-div-guess  ((w0 integerp)
                        (div integerp))
  :returns (guess integerp :rule-classes :type-prescription)
  (b* ((mag (srt-div-guess-mag w0 div)))
    (if (< (logext 36 w0) 0)
        (- mag)
      mag))
  ///
  ;; (local (defthmd logbitp-is-sign-when-signed-byte-p
  ;;          (implies (and (natp n)
  ;;                        (signed-byte-p (+ 1 n) x))
  ;;                   (equal (logbitp n x)
  ;;                          (< x 0)))
  ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs)))))
  
  ;; (defretd srt-div-guess-redef
  ;;   (implies (signed-byte-p 36 w0)
  ;;            (equal (srt-div-guess w0 div)
  ;;                   (b* ((mag (srt-div-guess-mag w0 div)))
  ;;                     (if (< w0 0)
  ;;                         (- mag)
  ;;                       mag))))
  ;;   :hints(("Goal" :in-theory (enable logbitp-is-sign-when-signed-byte-p))))
  
  (defret srt-div-guess-bounds
    (and (<= -2 guess)
         (<= guess 2))
    :rule-classes :linear)

  ;;;;; Proving the property we need of srt-div-guess.  Because of the way FGL
  ;;;;; processes multiplication, it is quite a bit faster to prove this lemma
  ;;;;; first, which just does (div*sign)*mag instead of div*(sign*mag).
  (local
   (fgl::def-fgl-thm srt-div-guess-accuracy-lemma
     (implies (and (unsigned-byte-p 36 div)
                   (equal (integer-length div) 33)
                   (unsigned-byte-p 36 w)
                   (srt-div-remainder-in-bounds w div))
              (b* ((guess (srt-div-guess-mag w div))
                   (prod (* (if (< (logext 36 w) 0) (- div) div) guess))
                   (next (- (logext 36 w) prod))
                   (next-sh (ash next 2)))
                (cw "div:    ~s0~%" (str::hexify div))
                (cw "w:     ~s0~%" (str::hexify (logext 36 w)))
                (cw "div*8:  ~s0~%" (str::hexify (* 8 div)))
                (cw "w*3:   ~s0~%" (str::hexify (* 3 (logext 36 w))))
                (cw "guess:  ~x0~%" guess)
                (cw "prod:   ~s0~%" (str::hexify prod))
                (cw "next:   ~s0~%" (str::hexify next))
                (cw "next*3: ~s0~%" (str::hexify next*3))
                (cw "div*2:  ~s0~%" (str::hexify (* 2 div)))
                (and (signed-byte-p 36 next-sh)
                     (srt-div-remainder-in-bounds next-sh div))))))

  ;;;;; Guess accuracy theorem: if the current partial remainder is in bounds,
  ;;;;; then the next partial remainder (computed using this guess) is in bounds.
  (defthm srt-div-guess-accuracy
    (implies (and (unsigned-byte-p 36 div)
                  (equal (integer-length div) 33)
                  (unsigned-byte-p 36 w)
                  (srt-div-remainder-in-bounds w div))
             (b* ((guess (srt-div-guess w div))
                  (prod (* div guess))
                  (next (- (logext 36 w) prod))
                  (next-sh (ash next 2)))
                (and (signed-byte-p 36 next-sh)
                     (srt-div-remainder-in-bounds next-sh div))))
    :hints (("goal" :use srt-div-guess-accuracy-lemma)))

  (defthm srt-div-guess-of-loghead-w
    (equal (srt-div-guess (loghead 36 w0) div)
           (srt-div-guess w0 div)))

  (defthm srt-div-guess-of-logext-w
    (equal (srt-div-guess (logext 36 w0) div)
           (srt-div-guess w0 div)))

  (defthm srt-div-guess-of-loghead-div
    (equal (srt-div-guess w0 (loghead 36 div))
           (srt-div-guess w0 div))))




;;;;; The next partial remainder is created by subtracting the normed divisor *
;;;;; quotient digit guess from the current partial remainder, then shifting
;;;;; the result by 2.
(define srt-div-next-partial-remainder ((w integerp)
                                        (div integerp))
  :returns (next-w integerp :rule-classes :type-prescription)
  (b* ((w (logext 36 w)))
    (ash (- w
            (* (lifix div) (srt-div-guess w div)))
         2))
  ///
  (fgl::def-fgl-rewrite srt-div-next-partial-remainder-fgl
    (equal (srt-div-next-partial-remainder w div)
           (b* ((w (logext 36 w))
                (mag (srt-div-guess-mag w div))
                (div (ifix div)))
             (ash (+ w (* (if (< w 0) div (- div)) mag)) 2)))
    :hints(("Goal" :in-theory (enable srt-div-guess))))


  (defret <fn>-of-loghead-w
    (implies (<= 36 (nfix n))
             (equal (srt-div-next-partial-remainder (loghead n w) div)
                    (srt-div-next-partial-remainder w div))))

  ;;;;; A corollary of the sqrt-div-guess-accuracy: if the current partial
  ;;;;; remainder is in bounds, then the next partial remainder is in bounds.
  (defret <fn>-bounds-relative
    (implies (and (equal (integer-length div) 33)
                  (natp div)
                  (srt-div-remainder-in-bounds w div))
             (and (signed-byte-p 36 next-w)
                  (srt-div-remainder-in-bounds next-w div)))
    :hints (("goal" :use ((:instance srt-div-guess-accuracy
                           (w (loghead 36 w)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable bitops::ash-is-expt-*-x)))))

  ;;;;; Absolute bounds on the partial remainder, a consequence of the previous
  ;;;;; theorem instantiated with the greatest possible divisor.
  (defret <fn>-bounds-absolute
    (implies (and (equal (integer-length div) 33) ;; < x^33
                  (natp div)
                  (srt-div-remainder-in-bounds w div))
             (and (<= (truncate (- (expt 2 36)) 3) next-w)
                  (<= next-w (truncate (expt 2 36) 3))))
    :hints (("goal" :use ((:instance <fn>-bounds-relative)
                          (:instance bitops::integer-length-expt-upper-bound-n
                           (n div)))
             :in-theory (e/d (srt-div-remainder-in-bounds)
                             (<fn>-bounds-relative
                              <fn>
                              bitops::integer-length-expt-upper-bound-n)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (bitops::ash-is-expt-*-x)))))
    :rule-classes :linear)

  ;;;;; Width of the partial remainder --- important that it fits in the given bit width.
  (defret signed-byte-p-of-<fn>
    (implies (and (equal (integer-length div) 33) ;; < x^33
                  (natp div)
                  (srt-div-remainder-in-bounds w div))
             (signed-byte-p 36 next-w))
    :hints(("Goal" :in-theory (e/d (signed-byte-p)
                                   (<fn>)))))

  ;;;;; Bottom two bits are zero since it was left-shifted.  Only important
  ;;;;; because when fixing up the final remainder, it gets shifted back out.
  (defret loghead-2-of-<fn>
    (equal (loghead 2 next-w) 0)))

;;;;; Now show that the hardware computes the expected partial remainders.  W1
;;;;; = (srt-div-next-partial-remainder w0 div) (although zero- rather than
;;;;; sign-extended). Note this is the first theorem proved with overrides.
;;;;; This event first proves a lemma with FGL where the listed variables (w0,
;;;;; div, iters) are overridden and the conclusion proved in that circumstance
;;;;; (using svtv-run of srt-run).  Then the SRT-RUN-REFINES-SRT-RUN property
;;;;; is used to prove that this conclusion holds without
;;;;; overrides, taking (w0, div, iters) to be the lookups of those variables
;;;;; in the outputs of the run.
(sv::def-svtv-generalized-thm srt-div-w1-formula
  :input-vars (divisor dividend)
  :override-vars (w0 norm-div iters)
  :output-vars (w1)
  :hyp (and (not (Equal divisor 0))
            (equal (integer-length norm-div) 33)
            (unsigned-byte-p 33 w0)
            (not (equal iters 1)))
  :concl (b* ((spec (loghead 36 (srt-div-next-partial-remainder w0 norm-div))))
           (cw "spec: ~s0~%" (str::hexify spec))
           (cw "w0: ~s0~%" (str::hexify w0))
           (cw "w0 sh: ~s0~%" (str::hexify (ash w0 2)))
           (equal w1 spec)))

(sv::def-svtv-generalized-thm srt-div-w1-if-last
  :input-vars (divisor dividend)
  :override-vars (w0 norm-div iters)
  :output-vars (w1)
  :hyp (and (not (Equal divisor 0))
            (equal (integer-length norm-div) 33)
            (unsigned-byte-p 33 w0)
            (eql iters 1))
  :concl (b* ((spec (loghead 36 (logtail 2 (srt-div-next-partial-remainder w0 norm-div)))))
           (cw "spec: ~s0~%" (str::hexify spec))
           (cw "w0: ~s0~%" (str::hexify w0))
           (cw "w0 sh: ~s0~%" (str::hexify (ash w0 2)))
           (equal w1 spec)))

;;;;; Unlike at other iterations, the above two theorems cover the possible
;;;;; cases for w1 -- iters is either 1 or greater unless divisor is 0.  We'll
;;;;; handle the divisor=0 case specially later.


(local (defthm signed-byte-p-36-when-38
         (implies (signed-byte-p 36 x)
                  (signed-byte-p 38 x))))

;;;;; Full function for W1 (as long as divisor != 0) -- just composition of
;;;;; srt-div-next-partial-remainder with w0 and norm-div
(define srt-div-w1 ((dividend integerp)
                    (divisor integerp))
  :returns (w1 integerp :rule-classes :type-prescription)
  (b* ((w0 (srt-div-w0 dividend divisor))
       (div (srt-div-norm-div divisor))
       (iters (srt-div-iters divisor))
       (next-prem (srt-div-next-partial-remainder w0 div)))
    (if (eql iters 1)
        (logtail 2 next-prem)
      next-prem))
  ///
  (defret width-of-<fn>
    (implies (and (not (equal 0 (loghead 32 divisor))))
             (signed-byte-p 36 w1)))
  
  (defret <fn>-of-loghead
    (implies (<= 32 (nfix n))
             (and (Equal (srt-div-w1 (loghead n dividend) divisor)
                         w1)
                  (Equal (srt-div-w1 dividend (loghead n divisor))
                         w1))))

  (defret remainder-in-bounds-of-<fn>
    (implies (and (not (equal 0 (loghead 32 divisor)))
                  (<= 2 (srt-div-iters divisor)))
             (srt-div-remainder-in-bounds w1 (srt-div-norm-div divisor))))

  
  (local (defthm ash-logtail-when-loghead-0
           (implies (and (equal (loghead n x) 0)
                         (natp n))
                    (equal (ash (logtail n x) n) (ifix x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::equal-logcons-strong)))))
  
  (defret remainder-in-bounds-of-<fn>-last
    (implies (and (not (equal 0 (loghead 32 divisor)))
                  (equal (srt-div-iters divisor) 1))
             (srt-div-remainder-in-bounds (ash w1 2) (srt-div-norm-div divisor)))))

;;;;; w1 = srt-div-w1.
;;;;; Note: This is our first theorem proved by composition! It uses the
;;;;; generality of srt-div-w1-formula along with srt-div-w0-formula and
;;;;; srt-div-norm-div-formula to show w1 = srt-div-w1 (zero-extended).  No FGL
;;;;; use for this theorem, just regular ACL2 rewriting.
(sv::def-svtv-generalized-thm srt-div-w1-redef
  :input-vars (divisor dividend)
  :output-vars (w1)
  :hyp (and (not (Equal divisor 0))
            ;; (equal (srt-div-iters divisor) 2)
            )
  :concl (equal w1 (loghead 36 (srt-div-w1 dividend divisor)))
  :no-lemmas t
  :hints(("Goal" :in-theory (enable srt-div-w1
                                    bitops::unsigned-byte-p-by-find-rule))))



;;;;; From W2 on we'll now define the full function recursively.  We add a
;;;;; rewrite rule normalizing srt-div-w1 to this function as well.
(define srt-div-wN ((n natp)
                    (dividend integerp)
                    (divisor integerp))
  :returns (wn integerp :rule-classes :type-prescription)
  (b* (((when (zp n)) (srt-div-w0 dividend divisor))
       (div (srt-div-norm-div divisor))
       (iters (srt-div-iters divisor))
       (prev (srt-div-wN (1- n) dividend divisor))
       ((when (> n iters)) prev)
       ((when (eql n iters))
        (logtail 2 (srt-div-next-partial-remainder prev div))))
    (srt-div-next-partial-remainder prev div))
  ///
  

  (defret remainder-in-bounds-of-<fn>
    (implies (and (not (equal 0 (loghead 32 divisor)))
                  (< (nfix n) (srt-div-iters divisor)))
             (srt-div-remainder-in-bounds wn (srt-div-norm-div divisor))))
  
  (defret width-of-<fn>
    (implies (and (not (equal 0 (loghead 32 divisor))))
             (signed-byte-p 36 wn)))

  (defret width-of-<fn>-last
    (implies (and (not (equal 0 (loghead 32 divisor)))
                  (<= (srt-div-iters divisor) (nfix n)))
             (signed-byte-p 34 wn))
    :hints (("goal" :induct t
             :expand (<call>
                      (srt-div-wn (srt-div-iters divisor) dividend divisor)))))
  
  (defret <fn>-of-loghead
    (implies (<= 32 (nfix k))
             (and (Equal (srt-div-wn n (loghead k dividend) divisor)
                         wn)
                  (Equal (srt-div-wn n dividend (loghead k divisor))
                         wn))))
  
  (local (defthm ash-logtail-when-loghead-0
           (implies (and (equal (loghead n x) 0)
                         (natp n))
                    (equal (ash (logtail n x) n) (ifix x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              bitops::equal-logcons-strong)))))

  (defret remainder-in-bounds-of-<fn>-finished
    (implies (and (not (equal 0 (loghead 32 divisor)))
                  (<= (srt-div-iters divisor) (nfix n)))
             (srt-div-remainder-in-bounds (ash wn 2) (srt-div-norm-div divisor)))
    :hints (("goal" :induct t
             :expand (<call>
                      (srt-div-wn (srt-div-iters divisor) dividend divisor)))))

  (defthm srt-div-w1-in-terms-of-wn
    (equal (srt-div-w1 dividend divisor)
           (srt-div-wn 1 dividend divisor))
    :hints(("Goal" :in-theory (enable srt-div-w1)
            :expand ((srt-div-wn 1 dividend divisor))))))





;;;;; Second partial remainder.  This is just the same formula as W1 again.
(sv::def-svtv-generalized-thm srt-div-w2-formula
  :input-vars (divisor dividend)
  :override-vars (w1 norm-div iters)
  :output-vars (w2 guess1)
  :hyp (and (not (Equal divisor 0))
            (equal (integer-length norm-div) 33)
            (srt-div-remainder-in-bounds w1 norm-div)
            (> iters 2))
  :concl (b* ((?guess guess1)
              (spec (loghead 36 (srt-div-next-partial-remainder w1 norm-div))))
           (cw "spec: ~s0~%" (str::hexify spec))
           (cw "w1: ~s0~%" (str::hexify w1))
           (cw "w1 sh: ~s0~%" (str::hexify (ash w1 2)))
           (cw "add: ~s0~%" (str::hexify (ash (* (if (logbitp 35 w1) 1 -1) norm-div guess1) 2)))
           (equal w2 spec)))

;;;;; When this is the last iteration (iters=2), the
;;;;; partial remainder isn't shifted by 2; we model this by reversing the
;;;;; shift after the the usual spec does the shift.
(sv::def-svtv-generalized-thm srt-div-w2-when-last
  :input-vars (divisor dividend)
  :override-vars (w1 norm-div iters)
  :output-vars (w2 guess1)
  :hyp (and (not (Equal divisor 0))
            (equal (integer-length norm-div) 33)
            (srt-div-remainder-in-bounds w1 norm-div)
            (equal iters 2))
  :concl (b* ((?guess guess1)
              (spec (loghead 36 (logtail 2 (srt-div-next-partial-remainder w1 norm-div)))))
           (cw "spec: ~s0~%" (str::hexify spec))
           (cw "w1: ~s0~%" (str::hexify w1))
           (cw "w1 sh: ~s0~%" (str::hexify (ash w1 2)))
           (cw "add: ~s0~%" (str::hexify (ash (* (if (logbitp 35 w1) 1 -1) norm-div guess1) 2)))
           (equal w2 spec)))

;;;;; When we are past the last iteration (in this case iters=1), the partial
;;;;; remainder is just preserved.
(sv::def-svtv-generalized-thm srt-div-w2-past-last
  :input-vars (divisor dividend)
  :override-vars (w1 norm-div iters)
  :output-vars (w2 guess1)
  :hyp (and (not (Equal divisor 0))
            (< iters 2)
            (not (equal iters 0)))
  :concl (b* ((?guess guess1)
              (spec w1))
           (cw "spec: ~s0~%" (str::hexify spec))
           (cw "w1: ~s0~%" (str::hexify w1))
           (cw "w1 sh: ~s0~%" (str::hexify (ash w1 2)))
           (cw "add: ~s0~%" (str::hexify (ash (* (if (logbitp 35 w1) 1 -1) norm-div guess1) 2)))
           (equal w2 w1)))



;;;;; w2 = srt-div-wn 2, again proved by composition rather than FGL.
(sv::def-svtv-generalized-thm srt-div-w2-redef
  :input-vars (divisor dividend)
  :output-vars (w2)
  :hyp (not (Equal divisor 0))
  :concl (equal w2 (loghead 36 (srt-div-wn 2 dividend divisor)))
  :no-lemmas t
  :hints(("Goal" :in-theory (enable bitops::unsigned-byte-p-by-find-rule)
          :expand ((:free (dividend divisor) (srt-div-wn 2 dividend divisor))))))


;;;;; Now we repeat this for all the rest of the iterations.  We'll do this with a macro so we don't have to write it all out.


(defconst *srt-div-wn-template*
  '(progn
 ;;;;; Nth partial remainder.  This is just the same formula as W1 again.
     (sv::def-svtv-generalized-thm srt-div-w<N>-formula
       :input-vars (divisor dividend)
       :override-vars (w<N-1> norm-div iters)
       :output-vars (w<N> guess<N-1>)
       :hyp (and (not (Equal divisor 0))
                 (equal (integer-length norm-div) 33)
                 (srt-div-remainder-in-bounds w<N-1> norm-div)
                 (> iters <N>))
       :concl (b* ((?guess guess<N-1>)
                   (spec (loghead 36 (srt-div-next-partial-remainder w<N-1> norm-div))))
                (cw "spec: ~s0~%" (str::hexify spec))
                (cw "w<N-1>: ~s0~%" (str::hexify w<N-1>))
                (cw "w<N-1> sh: ~s0~%" (str::hexify (ash w<N-1> 2)))
                (cw "add: ~s0~%" (str::hexify (ash (* (if (logbitp 35 w<N-1>) 1 -1) norm-div guess<N-1>) 2)))
                (equal w<N> spec)))

;;;;; When this is the last iteration, the
;;;;; partial remainder isn't shifted by 2; we model this by reversing the
;;;;; shift after the the usual spec does the shift.
     (sv::def-svtv-generalized-thm srt-div-w<N>-when-last
       :input-vars (divisor dividend)
       :override-vars (w<N-1> norm-div iters)
       :output-vars (w<N> guess<N-1>)
       :hyp (and (not (Equal divisor 0))
                 (equal (integer-length norm-div) 33)
                 (srt-div-remainder-in-bounds w<N-1> norm-div)
                 (equal iters <N>))
       :concl (b* ((?guess guess<N-1>)
                   (spec (loghead 36 (logtail 2 (srt-div-next-partial-remainder w<N-1> norm-div)))))
                (cw "spec: ~s0~%" (str::hexify spec))
                (cw "w<N-1>: ~s0~%" (str::hexify w<N-1>))
                (cw "w<N-1> sh: ~s0~%" (str::hexify (ash w<N-1> 2)))
                (cw "add: ~s0~%" (str::hexify (ash (* (if (logbitp 35 w<N-1>) 1 -1) norm-div guess<N-1>) 2)))
                (equal w<N> spec)))

;;;;; When we are past the last iteration, the partial
;;;;; remainder is just preserved.
     (sv::def-svtv-generalized-thm srt-div-w<N>-past-last
       :input-vars (divisor dividend)
       :override-vars (w<N-1> norm-div iters)
       :output-vars (w<N> guess<N-1>)
       :hyp (and (not (Equal divisor 0))
                 (< iters <N>)
                 (not (equal iters 0)))
       :concl (b* ((?guess guess<N-1>)
                   (spec w<N-1>))
                (cw "spec: ~s0~%" (str::hexify spec))
                (cw "w<N-1>: ~s0~%" (str::hexify w<N-1>))
                (cw "w<N-1> sh: ~s0~%" (str::hexify (ash w<N-1> 2)))
                (cw "add: ~s0~%" (str::hexify (ash (* (if (logbitp 35 w<N-1>) 1 -1) norm-div guess<N-1>) 2)))
                (equal w<N> w<N-1>)))



;;;;; w<N> = srt-div-wn N, again proved by composition rather than FGL.
     (sv::def-svtv-generalized-thm srt-div-w<N>-redef
       :input-vars (divisor dividend)
       :output-vars (w<N>)
       :hyp (not (Equal divisor 0))
       :concl (equal w<N> (loghead 36 (srt-div-wn <N> dividend divisor)))
       :no-lemmas t
       :hints(("Goal" :in-theory (enable bitops::unsigned-byte-p-by-find-rule)
               :expand ((:free (dividend divisor) (srt-div-wn <N> dividend divisor))))))))

(defmacro def-srt-div-wn (n)
  (acl2::template-subst *srt-div-wn-template*
                        :str-alist `(("<N>" . ,(str::natstr n))
                                     ("<N-1>" . ,(str::natstr (1- n))))
                        :atom-alist `((<N> . ,n)
                                      (<N-1> . ,(1- n)))
                        :pkg-sym 'this-package))


;;;;; Prove all the rest of the wN signals equal srt-div-wn.  The final result
;;;;; is W17 equals (srt-div-wn 17 dividend divisor) as long as divisor != 0.
(make-event
 `(progn . ,(loop$ for i from 3 to 17 collect `(def-srt-div-wn ,i))))









;;;;; Postprocessing the remainder happens in two steps: first, if the final
;;;;; remainder is negative, that means it's actually the remainder from 1+(the
;;;;; real quotient), so we need to add the normed divisor back in to get the
;;;;; real remainder.  Second, we need to right-shift the remainder to
;;;;; compensate for the initial left-shift of the divisor.

;;;;; This does the correction for possible negative remainder.
(define srt-div-remainder-correction ((w integerp)
                                      (div integerp))
  :returns (remainder integerp :rule-classes :type-prescription)
  (b* ((w (logext 36 w)))
    (if (< w 0)
        (+ w (lifix div))
      w))
  ///
  (defthmd srt-div-remainder-in-bounds-implies-less-than-div
    (implies (and (srt-div-remainder-in-bounds (ash w 2) div)
                  (signed-byte-p 34 w)
                  (posp div))
             (and (< w div)
                  (< (- div) w)))
    :hints(("Goal" :in-theory (enable srt-div-remainder-in-bounds))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::ash-is-expt-*-x)))))
  
  (defret <fn>-is-remainder
    (implies (and (equal (integer-length div) 33)
                  (natp div)
                  (signed-byte-p 34 w)
                  (srt-div-remainder-in-bounds (ash w 2) div)
                  (integerp q)
                  (natp dividend)
                  (equal w (- dividend (* q div))))
             (equal (srt-div-remainder-correction w div)
                    (mod dividend div)))
    :hints(("goal"
            :use ((:instance acl2::floor-unique
                   (num dividend) (div div)
                   (quot (if (< (- dividend (* q div)) 0) (+ -1 q) q)))
                  (:instance srt-div-remainder-in-bounds-implies-less-than-div)))))

  (defret <fn>-bounds
    (implies (and (equal (integer-length div) 33)
                  (natp div)
                  (signed-byte-p 34 w)
                  (srt-div-remainder-in-bounds (ash w 2) div))
             (and (<= 0 (srt-div-remainder-correction w div))
                  (< (srt-div-remainder-correction w div) div)))
    :hints(("Goal" :in-theory (enable srt-div-remainder-in-bounds))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::ash-is-expt-*-x))))
    :rule-classes :linear)

  (defret <fn>-of-loghead-w
    (implies (<= 36 (nfix n))
             (equal (srt-div-remainder-correction (loghead n w) div)
                    remainder))))

;;;;; This does the final un-shift of the remainder.
(define srt-div-remainder-shift ((rem integerp)
                                 (divisor integerp))
  :returns (remainder integerp :rule-classes :type-prescription)
  (b* ((divisor (loghead 32 divisor)))
    (logtail (- 33 (integer-length divisor)) rem)))
       
;;;;; Final remainder in terms of w17 and norm-div -- negative remainder
;;;;; correction and unshift
(sv::def-svtv-generalized-thm srt-div-remainder-formula
  :input-vars (divisor dividend)
  :override-vars (w17 iters norm-div)
  :output-vars (remainder)
  :hyp (and (not (Equal divisor 0))
            (equal (integer-length norm-div) 33)
            (<= iters 17)
            (not (equal iters 0))
            (signed-byte-p 34 (logext 36 w17))
            (srt-div-remainder-in-bounds (ash w17 2) norm-div))
  :concl (equal remainder
                (loghead 32 (srt-div-remainder-shift
                             (srt-div-remainder-correction w17 norm-div)
                             divisor))))

;;;;; Full function for the final remainder in terms of the inputs.
(define srt-div-remainder ((dividend integerp)
                           (divisor integerp))
  :returns (remainder integerp :rule-classes :type-prescription)
  (srt-div-remainder-shift
   (srt-div-remainder-correction
    (srt-div-wn 17 dividend divisor)
    (srt-div-norm-div divisor))
   divisor)
  ///
  (local (defthm <-of-logtail
           (implies (and (natp x)
                         (integerp y)
                         (natp n)
                         (< x (ash y n)))
                    (< (logtail n x) y))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              BITOPS::LOGCONS->-N-STRONG)
                                           (fty::bitp-when-unsigned-byte-p-1))))))
                    
  ;;;;; This theorem is key to showing that we're actually computing the
  ;;;;; correct floor/mod.  We'll later show that dividend = remainder +
  ;;;;; quotient*divisor.  The theorem floor-unique says that to show we're
  ;;;;; computing the floor, we then just need to know 0 <= remainder <
  ;;;;; divisor.
  (defret <fn>-bounds
    (implies (not (Equal 0 (loghead 32 divisor)))
             (and (<= 0 remainder)
                  (< remainder (loghead 32 divisor))))
    :hints(("Goal" :in-theory (e/d (srt-div-remainder-shift)
                                   (srt-div-remainder-correction-bounds))
            :use ((:instance SRT-DIV-REMAINDER-CORRECTION-bounds
                   (w (srt-div-wn 17 dividend divisor))
                   (div (srt-div-norm-div divisor)))))
           (and stable-under-simplificationp
                '(:in-theory (enable srt-div-norm-div))))
    :rule-classes :linear)
  )

;;;;; Composition: final remainder = srt-div-remainder of the inputs.  Remains
;;;;; to show that this computes the correct mathematical result
;;;;; (mod dividend divisor).
(sv::def-svtv-generalized-thm srt-div-remainder-redef
  :input-vars (divisor dividend)
  :output-vars (remainder)
  :hyp (not (Equal divisor 0))
  :concl (equal remainder
                (loghead 32 (srt-div-remainder dividend divisor)))
  :no-lemmas t
  :hints(("Goal" :in-theory (enable srt-div-remainder
                                    bitops::signed-byte-p-by-find-rule
                                    bitops::unsigned-byte-p-by-find-rule))))


;;;;; Now we turn our attention to the quotient digit accumulation.

;;;;; Full function for the first quotient digit.  We don't really prove that
;;;;; any particular vector in the RTL computes this; it's just a convenient
;;;;; decomposition for theorem proving purposes.
(define srt-div-guessN ((n natp)
                        (dividend integerp)
                        (divisor integerp))
  :returns (guessn integerp :rule-classes :type-prescription)
  (srt-div-guess (srt-div-wn n dividend divisor)
                 (srt-div-norm-div divisor)))


;;;;; This is an approximate quotient because the corresponding remainder may be negative.
(define srt-div-qapprox ((n natp)
                          (dividend integerp)
                          (divisor integerp))
  :returns (quo integerp :rule-classes :type-prescription)
  (b* ((iters (srt-div-iters divisor)))
    (cond ((zp n) 0)
          ((<= n iters)
           (+ (srt-div-guessn (1- n) dividend divisor)
              (ash (srt-div-qapprox (1- n) dividend divisor) 2)))
          (t (srt-div-qapprox (1- n) dividend divisor))))
  ///
  
  (defretd srt-div-wn-in-terms-of-qn
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-wn n dividend divisor)
                    (b* ((div (srt-div-norm-div divisor))
                         (w0 (srt-div-w0 dividend divisor)))
                      (- (ash w0 (* 2 (min (nfix n) (1- (srt-div-iters divisor)))))
                                 (ash (* div quo) (if (< (nfix n) (srt-div-iters divisor)) 2 0))))))
    :hints(("Goal" :in-theory (enable srt-div-next-partial-remainder
                                      srt-div-guessn
                                      bitops::unsigned-byte-p-by-find-rule)
            :induct <call>
            :expand (<call>
                     (srt-div-wn n dividend divisor)))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::ash-is-expt-*-x)
                  :do-not '(generalize) :do-not-induct t)))
    :otf-flg t)

  (defthmd srt-div-wn-17-in-terms-of-qn
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-wn 17 dividend divisor)
                    (b* ((div (srt-div-norm-div divisor))
                         (w0 (srt-div-w0 dividend divisor)))
                      (- (ash w0 (* 2 (1- (srt-div-iters divisor))))
                         (* div (srt-div-qapprox 17 dividend divisor))))))
    :hints(("Goal" :in-theory (e/d (srt-div-wn-in-terms-of-qn) (srt-div-qapprox))))
    :otf-flg t)

  (defthmd srt-div-wn-17-in-terms-of-unnormed
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-wn 17 dividend divisor)
                    (ash (- (loghead 32 dividend)
                            (* (loghead 32 divisor)
                               (srt-div-qapprox 17 dividend divisor)))
                         (- 33 (integer-length (loghead 32 divisor))))))
    :hints(("Goal" :in-theory (e/d (srt-div-wn-in-terms-of-qn
                                    srt-div-norm-div
                                    srt-div-w0
                                    srt-div-iters
                                    mod)
                                   (srt-div-qapprox)))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::ash-is-expt-*-x))))
    :otf-flg t))


(define srt-div-list-prems ((n natp) (dividend integerp) (divisor integerp))
  :returns (prems integer-listp)
  (if (zp n)
      nil
    (cons (loghead 36 (srt-div-wn (1- n) dividend divisor))
          (srt-div-list-prems (1- n) dividend divisor)))
  ///
  (defret len-of-<fn>
    (equal (len prems) (nfix n))))

;;;;; This function adds up the approximate quotient from the list of partial
;;;;; remainders, ordered last first, given the number of iterations.  This
;;;;; needs to be corrected by looking at the sign of the last one to get the
;;;;; exact quotient.
(define srt-div-qapprox-for-prem-list ((x integer-listp)
                                       (iters natp)
                                       (norm-div integerp))
  :returns (quo integerp :rule-classes :type-prescription)
  (if (atom x)
      0
    (let ((Rest (srt-div-qapprox-for-prem-list (cdr x) iters norm-div)))
      (if (<= (len x) iters)
          (+ (srt-div-guess (car x) norm-div)
             (ash rest 2))
        rest)))
  ///
  (defthm srt-div-qapprox-for-prem-list-in-terms-of-prem-list
    ;; (implies (<= n (srt-div-iters divisor))
    (equal (srt-div-qapprox-for-prem-list (srt-div-list-prems n dividend divisor)
                                          (srt-div-iters divisor)
                                          (srt-div-norm-div divisor))
           (srt-div-qapprox n dividend divisor))
    :hints(("Goal" :in-theory (enable srt-div-qapprox
                                      srt-div-list-prems
                                      srt-div-guessn)))))

;;;;; This computes the final quotient for a prem list given the number of
;;;;; iterations, by getting the guesses for each
;;;;; remainder and adding them up correctly.  The quotient digit accumulation
;;;;; logic is a little fussy but not hard for bitblasting to deal with, so we
;;;;; just show that the final quotient produced is just this function of the
;;;;; partial remainders.
(define srt-div-quotient-for-prems ((x integer-listp) ;; 17
                                    (iters posp) ;; <= 17
                                    (norm-div integerp))
  :guard (consp x)
  :returns (quo integerp :rule-classes :type-prescription)
  (+ (if (< (logext 36 (car x)) 0) -1 0)
     (srt-div-qapprox-for-prem-list (cdr x) iters norm-div)))



(encapsulate nil
;;;;; This sets up the final check in the following theorem to use an AIG SAT
;;;;; sweeping transform before calling SAT directly.
  (local (defun transforms-config ()
           (declare (Xargs :guard t))
           #!aignet
           (list ;; (make-observability-config)
            (make-obs-constprop-config)
            (make-balance-config :search-higher-levels t
                                 :search-second-lit t)
            (change-fraig-config *fraig-default-config*
                                 :random-seed-name nil
                                 :ctrex-queue-limit 8
                                 :sim-words 2
                                 :initial-sim-words 8
                                 :initial-sim-rounds 40
                                 :ctrex-force-resim t
                                 :ipasir-limit 1
                                 :ipasir-recycle-count 20000
                                 )
            )))
  (local (defattach fgl::fgl-aignet-transforms-config transforms-config))
  (local (define monolithic-sat-with-transforms ()
           (fgl::make-fgl-satlink-monolithic-sat-config :transform t)))
  (local (defattach fgl::fgl-toplevel-sat-check-config monolithic-sat-with-transforms))

;;;;; Show that the quotient signal is srt-div-quotient-for-prems of the
;;;;; partial remainders/normalized divisor --- override theorem
  (make-event
   (let ((ws '(w17 w16 w15 w14 w13 w12 w11 w10 w9 w8 w7 w6 w5 w4 w3 w2 w1 w0)))
     `(sv::def-svtv-generalized-thm srt-div-quotient-formula
        :input-vars (divisor)
        :override-vars ,ws
        :output-vars (quotient iters norm-div)
        :hyp (not (Equal divisor 0))
        :concl (b* ((spec (srt-div-quotient-for-prems (list . ,ws) iters norm-div)))
                 (cw "spec: ~s0~%" (str::hexify spec))
                 (implies (<= 0 spec)
                          (equal quotient (loghead 32 spec))))))))




;;;;; Full function for the quotient in terms of the inputs.  We show that this
;;;;; equals the floor of the dividend/divisor by showing (via rewriting) that
;;;;; dividend = remainder + divisor * quotient, and by showing that remainder
;;;;; is in the right range.  This then implies that the remainder is the mod.
(define srt-div-quotient ((dividend integerp)
                          (divisor integerp))
  :returns (quotient integerp :rule-classes :type-prescription)
  (b* ((rem (srt-div-wn 17 dividend divisor))
       (qapprox (srt-div-qapprox 17 dividend divisor)))
    (if (< rem 0)
        (1- qapprox)
      qapprox))
  ///

  (local (defthm +-of-ash-same
           (implies (natp n)
                    (equal (+ (ash x n) (ash y n))
                           (ash (+ (ifix x) (ifix y)) n)))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))
  
  (defthmd srt-div-remainder-in-terms-of-quotient
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-remainder dividend divisor)
                    (- (loghead 32 dividend)
                       (* (loghead 32 divisor)
                          (srt-div-quotient dividend divisor)))))
    :hints(("Goal" :in-theory (enable srt-div-quotient
                                      srt-div-remainder
                                      srt-div-remainder-shift
                                      srt-div-remainder-correction
                                      bitops::signed-byte-p-by-find-rule))
           (and stable-under-simplificationp
                '(:in-theory (enable srt-div-norm-div
                                     srt-div-wn-17-in-terms-of-unnormed
                                     srt-div-iters)))))

  (defthm srt-div-quotient-is-floor
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-quotient dividend divisor)
                    (floor (loghead 32 dividend)
                           (loghead 32 divisor))))
    :hints (("goal" :use ((:instance acl2::floor-unique
                           (num (loghead 32 dividend))
                           (div (loghead 32 divisor))
                           (quot (srt-div-quotient dividend divisor)))
                          srt-div-remainder-in-terms-of-quotient)
             :in-theory (disable srt-div-quotient))))


  (defthm natp-of-srt-div-quotient
    (implies (not (equal (loghead 32 divisor) 0))
             (natp (srt-div-quotient dividend divisor)))
    :hints(("Goal" :in-theory (disable srt-div-quotient)))
    :rule-classes :type-prescription)
  
  (defthm srt-div-remainder-is-mod
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-remainder dividend divisor)
                    (mod (loghead 32 dividend)
                         (loghead 32 divisor))))
    :hints (("goal" :in-theory (e/d (srt-div-remainder-in-terms-of-quotient
                                     mod)
                                    (srt-div-quotient)))))

  (defthmd srt-div-quotient-is-quotient-for-prems
    (implies (not (equal (loghead 32 divisor) 0))
             (equal (srt-div-quotient dividend divisor)
                    (srt-div-quotient-for-prems (srt-div-list-prems 18 dividend divisor)
                                                (srt-div-iters divisor)
                                                (srt-div-norm-div divisor))))
    :hints(("Goal" :in-theory (enable srt-div-quotient-for-prems
                                      srt-div-quotient))
           (and stable-under-simplificationp
                '(:expand ((srt-div-list-prems 18 dividend divisor)))))))



;;;;; Composition: final quotient = srt-div-quotient of the inputs.
(sv::def-svtv-generalized-thm srt-div-quotient-redef
  :input-vars (divisor dividend)
  :output-vars (quotient)
  :hyp (not (Equal divisor 0))
  :concl (equal quotient
                (loghead 32 (srt-div-quotient dividend divisor)))
  :no-lemmas t
  :hints(("Goal" :in-theory (e/d (srt-div-remainder
                                  srt-div-quotient-is-quotient-for-prems
                                  bitops::signed-byte-p-by-find-rule
                                  bitops::unsigned-byte-p-by-find-rule)
                                 (srt-div-qapprox-for-prem-list-in-terms-of-prem-list
                                  natp-of-srt-div-quotient
                                  srt-div-quotient-is-floor))
          :use ((:instance natp-of-srt-div-quotient
                 (dividend (sv::svex-env-lookup 'dividend sv::env))
                 (divisor (sv::svex-env-lookup 'divisor sv::env))))
          :expand ((:free (n dividend divisor) (srt-div-list-prems n dividend divisor))
                   (:free (dividend divisor) (srt-div-wn 0 dividend divisor))))))

(local (defthm unsigned-byte-p-32-of-floor
         (implies (and (unsigned-byte-p 32 x)
                       (posp y))
                  (unsigned-byte-p 32 (floor x y)))
         :hints(("Goal" :in-theory (e/d (unsigned-byte-p)
                                        (acl2::floor-recursion))
                 :use ((:instance acl2::floor-recursion (x x) (y y)))))))


;;;;; Finally we show that the quotient signal correctly computes (floor
;;;;; dividend divisor).  This uses srt-div-quotient-formula to reduce the
;;;;; quotient signal to exactly the definition of srt-div-quotient, then
;;;;; applies srt-div-quotient-is-floor.
(sv::def-svtv-generalized-thm srt-div-quotient-correct
  :input-vars (divisor dividend)
  :output-vars (quotient)
  :hyp (not (Equal divisor 0))
  :concl (equal quotient
                (floor dividend divisor))
  :no-lemmas t)


;;;;; Similarly we show that the remainder signal correctly computes (mod
;;;;; dividend divisor) -- srt-div-remainder-formula reduces the remainder
;;;;; signal to the definition of srt-div-remainder, and applies
;;;;; srt-div-remainder-is-mod.
(sv::def-svtv-generalized-thm srt-div-remainder-correct
  :input-vars (divisor dividend)
  :output-vars (remainder)
  :hyp (not (Equal divisor 0))
  :concl (equal remainder
                (mod dividend divisor))
  :no-lemmas t)

;;;;; We specify the outputs when the divisor is 0 directly with just symbolic
;;;;; simulation
(sv::def-svtv-generalized-thm srt-div-by-zero
  :input-vars (dividend)
  :input-var-bindings ((divisor 0))
  :output-vars (remainder quotient error)
  :concl (and (equal error 1)
              (equal quotient 0)
              (equal remainder 0)))

;;;;; Finally we show that the finish signal is 0 during the whole computation
;;;;; until it reaches 1 on the final cycle, when the quotient/remainder are
;;;;; definitely correct.
(make-event
 `(sv::def-svtv-generalized-thm srt-div-finish
  :input-vars (dividend divisor)
  :output-vars (,@(loop$ for i from 1 to 16 collect
                         (flet ((suffix (sym n)
                                        (intern-in-package-of-symbol (concatenate 'string (symbol-name sym) (coerce (explode-atom n 10) 'string))
                                                                     'a-symbol-from-this-package)))
                               (suffix 'finish i)))
                finish)
  :concl (and ,@(loop$ for i from 1 to 16 collect
                         (flet ((suffix (sym n)
                                        (intern-in-package-of-symbol (concatenate 'string (symbol-name sym) (coerce (explode-atom n 10) 'string))
                                                                     'a-symbol-from-this-package)))
                               `(equal ,(suffix 'finish i) 0)))
              (equal finish 1))))
  




:endif) ;; (ifdef "SRTDIV_HAS_IMPLEMENTATION"
