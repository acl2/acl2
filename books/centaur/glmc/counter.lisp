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

(include-book "centaur/sv/top" :dir :system)
(include-book "glmc")
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "bfr-mcheck-abc")
(include-book "centaur/sv/svtv/fsm" :dir :system)
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/sv/svex/gl-rules" :dir :system)
(include-book "oslib/ls" :dir :system)

(local (in-theory (disable (tau-system))))
; (depends-on "counter.sv")
; cert_param: (uses-glucose)
; cert_param: (uses-abc)

(value-triple (acl2::tshell-ensure))
(gl::gl-satlink-mode)
(gl::bfr-mcheck-use-abc-simple)

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (f-get-global 'acl2::parallel-execution-enabled state)
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))

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


(defcycle counter-step
  :design *counter*
  :phases (list (make-svtv-cyclephase :constants '(("clk" . 0))
                                      :inputs-free t
                                      :outputs-captured t)
                (make-svtv-cyclephase :constants '(("clk" . 1))))
  :names '((reset . "reset")
           (incr . "incr")
           (count . "count")))

;; (defconst *counter-step-fsm*
;;   (b* (((svtv x) (counter-step-svtv)))
;;     (make-svtv-fsm :values x.outexprs
;;                    :nextstate x.nextstate
;;                    :design *counter*)))


;; (make-event
;;  `(defun counter-step ()
;;     (declare (xargs :guard t))
;;     ',*counter-step-fsm*))

(in-theory (disable counter-step (counter-step)))

(local (defun my-satlink-config ()
         (declare (Xargs :guard t))
         (satlink::make-config
          :cmdline "glucose -model"
          :verbose t
          :mintime 1)))

(local (defattach gl::gl-satlink-config my-satlink-config))


(gl::gl-set-uninterpreted base-fsm-symbolic-env)


(define counter-run-step ((ins svex-env-p)
                          (st svex-env-p))
  :guard (equal (alist-keys st)
                (svex-alist-keys (svtv-fsm->nextstate (counter-step))))
  :guard-hints (("goal" :in-theory (enable ;; 
                                           (counter-step))))
  :guard-debug t
  :returns (mv (step svex-env-p)
               (nextst svex-env-p))
  (b* (((svtv-fsm counter) (counter-step))
       (ins (make-fast-alist ins))
       ((mv (list step) (list nextst))
        (svtv-fsm-run-outs-and-states
         (list (make-fast-alist ins)) nil st (counter-step)
         :out-signals'((count reset incr))
         :state-signals (list (svex-alist-keys (svtv-fsm->nextstate (counter-step)))))))
    (mv (make-fast-alist step)
        (make-fast-alist nextst))))

(gl::add-gl-rewrite svtv-fsm-run-outs-and-states-is-base-fsm-run-outs-and-states)
(gl::gl-set-uninterpreted svtv-fsm-run-outs-and-states-fn)
(gl::gl-set-uninterpreted svtv-env-to-values)
(gl::gl-set-uninterpreted join-val/test-envs)
(gl::add-gl-rewrite lookup-in-join-val/test-envs)

(gl::def-glcp-ctrex-rewrite
  ((svex-env-lookup key (svtv-env-to-values env map updates)) val)
  (env (hons-acons (sv::change-svar key :override-val t) val env)))

(define counter-ok ((st svex-env-p)
                    (ins svex-envlist-p))
  :measure (len ins)
  :verify-guards nil
  (b* (((when (atom ins)) t)
       ((svtv-fsm counter) (counter-step))
       (in (car ins))
       ((mv step nextst) (counter-run-step in st))
       (count (svex-env-lookup 'count step))
       (reset (4vec-zero-ext 1 (svex-env-lookup 'reset step)))
       (incr (4vec-zero-ext 1 (svex-env-lookup 'incr step)))
       ((unless (and (2vec-p reset)
                     (2vec-p incr))) t)
       ((unless (and (2vec-p count)
                     (not (equal (2vec->val count) 14))))
        nil))
    (counter-ok nextst (cdr ins))))


(local
 (define gl-abc-mcheck-script-mine ((input-fname stringp) (ctrex-fname stringp))
   :returns (script stringp :rule-classes :type-prescription)
   (concatenate 'string
                "&r " input-fname "
                &put
                dprove -v
                print_status
                write_cex " ctrex-fname)
   ///
   (defattach gl::gl-abc-mcheck-script gl-abc-mcheck-script-mine)))

(defthm counter-is-ok
  (b* (((mv step &) (counter-run-step (car ins) st))
       (count (svex-env-lookup 'count step)))
    (implies (and (2vec-p count)
                  (< count 5))
             (counter-ok st ins)))
  :hints ((gl::glmc-hint
           :state-var st
           :body-bindings (((mv step nextst) (counter-run-step in st)))
           :nextstate nextst
           :prop (b* ((count (svex-env-lookup 'count step)))
                   (and (2vec-p count)
                        (not (equal (2vec->val count) 14))))
           :constraint (and (2vec-p (4vec-zero-ext 1 (svex-env-lookup 'reset step)))
                            (2vec-p (4vec-zero-ext 1 (svex-env-lookup 'incr step))))
           :initstatep (b* ((count (svex-env-lookup 'count step)))
                         (and (2vec-p count)
                              (< count 5)))
           :frame-input-bindings ((in (car ins)))
           :rest-of-input-bindings ((ins (cdr ins)))
           :end-of-inputsp (atom ins)
           :measure (len ins)
           :run (counter-ok st ins)
           :shape-spec-bindings `((in ,(gl::g-var 'in))
                                  (st ,(gl::g-var 'st)))
           :run-check-hints ('(:expand ((counter-ok st ins)))))))
