; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "../top")
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "centaur/sv/svtv/fsm" :dir :system)
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/sv/svex/gl-rules" :dir :system)

; (depends-on "counter.sv")
; cert_param: (hons-only)
; cert_param: (uses-glucose)

(value-triple (acl2::tshell-ensure))

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (and (acl2::hons-enabledp state)
          (f-get-global 'acl2::parallel-execution-enabled state))
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))
(local (include-book "centaur/aig/g-aig-eval" :dir :system))

(local (gl::def-gl-clause-processor counter-glcp))

(defconsts (*counter* state)
  (b* (((mv loadres state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files (list "counter.sv"))))
       (design (vl::vl-loadresult->design loadres))
       ((mv ?err svdesign ?good ?bad)
        (vl::cwtime (vl::vl-design->svex-design "counter" design (vl::make-vl-simpconfig)))))
    (and err
         (er hard? 'counter "Error: ~@0~%Warnings: ~s1~%" err
             (vl::vl-reportcard-to-string (vl::vl-design-reportcard bad))))
    (mv svdesign state)))


(defsvtv counter-step
  :mod *counter*
  :inputs '(("clk"    0  1)
            ("reset"  reset _)
            ("incr"   incr  _))
  :outputs '(("count" count _)
             ("reset"  reset _)
             ("incr"   incr  _))
  :state-machine t
  :simplify t
  :pre-simplify t)


(gl::gl-satlink-mode)

(gl::def-gl-thm counter-step-does-not-overflow-symbolic
  :hyp t
  :concl (b* ((steps (svex-alistlist-eval-for-symbolic
                      (svtv-cycles-compose (counter-step) 1)
                      env
                      '((:allvars t))))
              ((list step0 step1) steps)
              (step0 (make-fast-alist step0))
              (step1 (make-fast-alist step1))
              (count0 (svex-env-lookup-nofix 'count step0))
              (reset (svex-env-lookup-nofix 'reset step0))
              (incr (svex-env-lookup-nofix 'incr step0))
              (count1 (svex-env-lookup-nofix 'count step1)))
           (cw "Step0:~%")
           (sv::svtv-print-alist-readable step0)
           (cw "Step1:~%")
           (sv::svtv-print-alist-readable step1)

           (implies (and (2vec-p count0)
                         (2vec-p reset)
                         (2vec-p incr)
                         (< (2vec->val count0) 10))
                    (and (2vec-p count1)
                         (< (2vec->val count1) 10))))
  :g-bindings nil
  :ctrex-transform ctrex-clean-env)

(acl2::must-fail
 (gl::def-gl-thm counter-step-does-not-overflow-symbolic-bug
   :hyp t
   :concl (b* ((steps (svex-alistlist-eval-for-symbolic
                       (svtv-cycles-compose (counter-step) 1)
                       env
                       '((:allvars t))))
               ((list step0 step1) steps)
              (step0 (make-fast-alist step0))
              (step1 (make-fast-alist step1))
               (count0 (svex-env-lookup-nofix 'count step0))
               (reset (svex-env-lookup-nofix 'reset step0))
               (incr (svex-env-lookup-nofix 'incr step0))
               (count1 (svex-env-lookup-nofix 'count step1)))
            (cw "Step0:~%")
            (sv::svtv-print-alist-readable step0)
            (cw "Step1:~%")
            (sv::svtv-print-alist-readable step1)

            (implies (and (2vec-p count0)
                          (2vec-p reset)
                          (2vec-p incr)
                          (< (2vec->val count0) 9))
                     (and (2vec-p count1)
                          (< (2vec->val count1) 9))))
   :g-bindings nil
   :rule-classes nil
   :ctrex-transform ctrex-clean-env))

(defthm counter-step-no-cycle-vars
  (and (not (svarlist-has-svtv-cycle-var (svex-alist-keys (svtv->nextstate (counter-step)))))
       (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->nextstate (counter-step)))))
       (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->outexprs (counter-step))))))
  :hints(("Goal" :in-theory (enable (counter-step)))))

(define counter-step-preconds ((step svex-env-p))
  (and (2vec-p (svex-env-lookup 'reset step))
       (2vec-p (svex-env-lookup 'incr step))))

(define counter-step-invariant ((step svex-env-p))
  (b* ((count (svex-env-lookup 'count step)))
    (and (2vec-p count)
         (< (2vec->val count) 10))))

(local
 (defsection svarlist-has-svtv-cycle-var-of-set-equiv
   (local (defun svarlist-has-svtv-cycle-var-witness (x)
            (if (atom x)
                nil
              (if (svtv-is-cycle-var (car x))
                  (car x)
                (svarlist-has-svtv-cycle-var-witness (cdr x))))))

   (local (in-theory (enable svarlist-has-svtv-cycle-var)))

   (local (defthm svarlist-has-svtv-cycle-var-iff-witness
            (implies (acl2::rewriting-negative-literal `(svarlist-has-svtv-cycle-var ,x))
                     (iff (svarlist-has-svtv-cycle-var x)
                          (b* ((witness (svarlist-has-svtv-cycle-var-witness x)))
                            (and (svtv-is-cycle-var witness)
                                 (member witness x)))))))

   (local (defthm no-cycle-var-when-not-has-cycle-var
            (implies (and (member v x)
                          (svtv-is-cycle-var v))
                     (svarlist-has-svtv-cycle-var x))))

   (defcong set-equiv equal (svarlist-has-svtv-cycle-var x) 1
     :hints (("goal" :do-not-induct t)
             (set-reasoning)))))
  

(defthm counter-step-does-not-overflow-invariant
  (b* ((steps (svtv-fsm-run (list env0 env1) init-st (counter-step)))
       ((list step0 step1) steps))

    (implies (and (counter-step-preconds step0)
                  (counter-step-invariant step0)
                  (set-equiv (alist-keys (svex-env-fix init-st))
                             (svex-alist-keys (svtv->nextstate (counter-step)))))
             (counter-step-invariant step1)))
  :hints (("goal" :in-theory (e/d (svtv-fsm-run-alt
                                   counter-step-preconds
                                   counter-step-invariant)
                                  ((counter-step)
                                   2vec-p
                                   counter-step-does-not-overflow-symbolic))
           :use ((:instance counter-step-does-not-overflow-symbolic
                  (env (svtv-cycle-envs-to-single-env (list env0 env1) 0 init-st)))))
          (and stable-under-simplificationp
               '(:cases ((svarlist-has-svtv-cycle-var (alist-keys (Svex-env-fix init-st))))))))

(define counter-step-invariant-holds ((steps svex-envlist-p))
  :guard (consp steps)
  (and (counter-step-invariant (car steps))
       (or (not (counter-step-preconds (car steps)))
           (atom (cdr steps))
           (counter-step-invariant-holds (cdr steps)))))





(defthm counter-step-does-not-overflow
  (implies (and (consp envs)
                (set-equiv (alist-keys (svex-env-fix init-st))
                           (svex-alist-keys (svtv->nextstate (counter-step)))))
           (b* ((steps (svtv-fsm-run envs init-st (counter-step))))
             (implies (counter-step-invariant (car steps))
                      (counter-step-invariant-holds steps))))
  :hints (("goal" :induct (svtv-fsm-run envs init-st (counter-step))
           :in-theory (e/d (counter-step-invariant-holds
                            counter-step-invariant
                            counter-step-preconds
                            (:i svtv-fsm-run))
                           (2vec-p
                            2vec->val
                            append
                            acl2::append-when-not-consp
                            svtv-fsm-run-is-run-alt
                            counter-step-does-not-overflow-invariant))
           :expand ((svtv-fsm-run envs init-st (counter-step))))
          (and stable-under-simplificationp
               '(:use ((:instance counter-step-does-not-overflow-invariant
                        (env0 (car envs))
                        (env1 (cadr envs))))))))
