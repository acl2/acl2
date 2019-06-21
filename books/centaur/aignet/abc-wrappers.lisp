; Copyright (C) 2017 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "AIGNET")

(include-book "centaur/aignet/abc" :dir :system)
(include-book "transform-utils")
(include-book "oslib/tempfile" :dir :system)

(local (xdoc::set-default-parents abc-comb-simplify))

(fty::defprod abc-comb-simp-config
  ((script stringp :rule-classes :type-prescription)
   (quiet booleanp))
  :parents (abc-comb-simplify comb-transform)
  :short "Configuration object for using the @(see abc-comb-simplify) transform on an aignet."
  :tag :abc-comb-simp-config)

(defconst *default-abc-comb-simp-config*
  (make-abc-comb-simp-config
   :script "&put; dc2; dfraig; &get"
   :quiet nil))

(local (in-theory (disable w)))

(define abc-comb-simplify ((input-aignet)
                           (output-aignet)
                           (config abc-comb-simp-config-p)
                           (state))
  :returns (mv new-output-aignet new-state)
  :parents (aignet-comb-transforms)
  :short "Use the external tool ABC to apply a combinational simplification to
          the network, and assume the result correct."
  (b* (((abc-comb-simp-config config))
       ((mv input-filename state) (oslib::tempfile "abc-comb-simplify-input.aig"))
       ((mv output-filename state) (oslib::tempfile "abc-comb-simplify-output.aig"))
       ((mv script-filename state) (oslib::tempfile "abc-comb-simplify-script"))
       ((unless (and input-filename output-filename script-filename))
        (cw "Error -- couldn't generate temp filenames.~%")
        (b* ((output-aignet (aignet-raw-copy input-aignet output-aignet)))
          (mv output-aignet state)))
       (script (str::cat "&r " input-filename "; " config.script "; &w " output-filename))
       ((local-stobjs frames)
        (mv output-aignet state frames))
       ((mv status output-aignet frames)
        (aignet-abc input-aignet output-aignet frames script
                    :script-filename script-filename
                    :input-filename input-filename
                    :output-filename output-filename
                    :axiom :comb-simp))
       ((when (stringp status))
        (cw "Error -- ABC failed: ~s0~%" status)
        (b* ((output-aignet (aignet-raw-copy input-aignet output-aignet)))
          (mv output-aignet state frames))))
    (mv output-aignet state frames))
  ///

  (defthm normalize-inputs-of-abc-comb-simplify
    (implies (syntaxp (not (equal output-aignet ''nil)))
             (equal (abc-comb-simplify input-aignet output-aignet config state)
                    (abc-comb-simplify input-aignet nil config state))))

  (defret num-ins-of-abc-comb-simplify
    (equal (stype-count :pi new-output-aignet)
           (stype-count :pi input-aignet)))

  (defret num-regs-of-abc-comb-simplify
    (equal (stype-count :reg new-output-aignet)
           (stype-count :reg input-aignet)))

  (defret num-outs-of-abc-comb-simplify
    (equal (stype-count :po new-output-aignet)
           (stype-count :po input-aignet)))

  (defret abc-comb-simplify-comb-equivalent
    (comb-equiv new-output-aignet input-aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(define abc-comb-simplify! ((aignet)
                            (config abc-comb-simp-config-p)
                            (state))
  :returns (mv new-aignet new-state)
  :parents (abc-comb-simplify)
  :short "Like @(see abc-comb-simplify), but overwrites the original network instead of returning a new one."
  (b* (((abc-comb-simp-config config))
       ((mv input-filename state) (oslib::tempfile "abc-comb-simplify-input.aig"))
       ((mv output-filename state) (oslib::tempfile "abc-comb-simplify-output.aig"))
       ((mv script-filename state) (oslib::tempfile "abc-comb-simplify-script"))
       ((unless (and input-filename output-filename script-filename))
        (cw "Error -- couldn't generate temp filenames.~%")
        (mv aignet state))
       (script (str::cat "&r " input-filename "; " config.script "; &w " output-filename))
       ((local-stobjs frames aignet2)
        (mv aignet state frames aignet2))
       ((mv status aignet2 frames)
        (aignet-abc aignet aignet2 frames script
                    :script-filename script-filename
                    :input-filename input-filename
                    :output-filename output-filename
                    :axiom :comb-simp))
       ((when (stringp status))
        (cw "Error -- ABC failed: ~s0~%" status)
        (mv aignet state frames aignet2))
       (aignet (aignet-raw-copy aignet2 aignet)))
    (mv aignet state frames aignet2))
  ///

  (defret num-ins-of-abc-comb-simplify!
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-abc-comb-simplify!
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-abc-comb-simplify!
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret abc-comb-simplify!-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))
       
                           

