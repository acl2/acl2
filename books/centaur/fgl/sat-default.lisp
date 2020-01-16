; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")

(include-book "ipasir-sat")
(include-book "satlink-sat")

(local (in-theory (disable w)))

(fty::deftranssum fgl-sat-config
  :parents (fgl-sat-check)
  :short "Configuration object for either monolithic or incremental SAT in the default FGL configuration."
  (fgl-satlink-monolithic-sat-config
   fgl-ipasir-config))

(make-event
 `(define fgl-default-sat-check-impl (params
                                      (bfr interp-st-bfr-p)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
    :returns (mv status new-interp-st new-state)
    (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
          (cw "SAT check failed because we are not in AIGNET mode!~%")
          (mv :failed interp-st state))
         ((when (interp-st->errmsg interp-st))
          (mv :failed interp-st state))
         ((unless (fgl-sat-config-p params))
          (fgl-interp-error
           :msg (fgl-msg "Malformed fgl-sat-check call: params was not resolved to an fgl-sat-config object."))))
      (case (tag params)
        (:fgl-satlink-config
         (interp-st-satlink-sat-check-core params bfr interp-st state))
        (otherwise
         (interp-st-ipasir-sat-check-core params bfr interp-st state))))
    ///
    . ,*interp-st-sat-check-thms*))

(define fgl-default-sat-counterexample-impl (params
                                             (interp-st interp-st-bfrs-ok)
                                             state)
  :returns (mv err new-interp-st)
  (case (tag params)
    (:fgl-satlink-config (interp-st-satlink-counterexample params interp-st state))
    (otherwise           (interp-st-ipasir-counterexample params interp-st state)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :ctrex-env))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret bfr-env$-p-of-<fn>
    (implies (not err)
             (bfr-env$-p (interp-st->ctrex-env new-interp-st)
                         (logicman->bfrstate (interp-st->logicman interp-st)))))

  

  (defret aignet-vals-p-of-<fn>
    (implies (and (not err)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (aignet::aignet-vals-p
              (env$->bitarr (interp-st->ctrex-env new-interp-st))
              (logicman->aignet (interp-st->logicman interp-st))))))

(defmacro fgl-use-default-sat-check ()
  `(progn (defattach interp-st-sat-check fgl-default-sat-check-impl)
          (defattach interp-st-sat-counterexample fgl-default-sat-counterexample-impl)
          (defattach fgl-toplevel-sat-check-config fgl-satlink-default-toplevel-sat-check-config)))

(fgl-use-default-sat-check)


       
