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
(include-book "centaur/fgl/top" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "centaur/sv/svtv/svtv-stobj-defcycle" :dir :system)
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/sv/svex/gl-rules" :dir :system)
(include-book "std/testing/eval" :dir :system)
(include-book "oslib/ls" :dir :system)

(local (in-theory (disable (tau-system))))
; (depends-on "counter.sv")
; cert_param: (uses-glucose)

(value-triple (acl2::tshell-ensure))

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (f-get-global 'acl2::parallel-execution-enabled state)
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))
(local (include-book "centaur/aig/g-aig-eval" :dir :system))

;; (local (gl::def-gl-clause-processor counter-glcp))

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
  :phases (list (make-svtv-cyclephase :constants '(("clk" . 0)) :inputs-free t
                                       :outputs-captured t)
                (make-svtv-cyclephase :constants '(("clk" . 1))))
  :names '((reset . "reset")
           (incr . "incr")
           (count . "count"))
  :rewrite-phases t :rewrite-cycle t)


(gl::gl-satlink-mode)

;; configure satlink to use base glucose
(local (progn (defun my-satlink-config ()
                (declare (Xargs :guard t))
                (satlink::make-config
                 :cmdline "glucose -model"
                 :verbose t
                 :mintime 1))
              (defattach gl::gl-satlink-config my-satlink-config)))

(local
 (progn
   (fgl::remove-fgl-rewrite sv::svex-env-lookup)

   (fgl::remove-fgl-rewrite sv::svex-env-fix$inline)
   (fgl::remove-fgl-rewrite acl2::alist-keys)

   (fgl::add-fgl-rewrite sv::base-fsm-run-is-symbolic)
   (fgl::add-fgl-rewrite sv::base-fsm-run-states-is-symbolic)

   (fgl::remove-fgl-rewrite sv::base-fsm-symbolic-env)
   (fgl::add-fgl-rewrite sv::svex-env-fix-of-base-fsm-symbolic-env)
   (fgl::add-fgl-rewrite sv::svex-env-lookup-of-base-fsm-symbolic-env)

   (fgl::def-fgl-rewrite svex-env-lookup-of-g-map
     (implies (syntaxp (and (fgl::fgl-object-case x :g-map)
                            (fgl::fgl-object-case k :g-concrete)))
              (equal (sv::svex-env-lookup k x)
                     (sv::4vec-fix (cdr (hons-get (sv::svar-fix k) x)))))
     :hints(("Goal" :in-theory (enable sv::svex-env-lookup))))

   (fgl::add-fgl-rewrite SV::4VEC-P-OF-SVEX-ENV-LOOKUP)

   (fgl::def-ctrex-rule svex-env-lookup-ctrex-rule
     :match ((val (sv::svex-env-lookup k x)))
     :assign (hons-acons k val x)
     :assigned-var x
     ;;:hyp (alistp x)
     :ruletype :property)

   (fgl::def-ctrex-rule 4vec-elim
     :match ((upper (sv::4vec->upper x))
             (lower (sv::4vec->lower x)))
     :assign (sv::4vec upper lower)
     :assigned-var x
     ;;:hyp (alistp x)
     :ruletype :elim)

   (fgl::def-fgl-rewrite integerp-of-svex-env-lookup-break
     (equal (integerp (sv::svex-env-lookup k x))
            (fgl::fgl-prog2 (fgl::fgl-error! :msg "(integerp (svex-env-lookup k x))"
                                             :debug-obj `((k . ,k) (x . ,x)))
                            (integerp (sv::svex-env-lookup k x)))))

   (fgl::remove-fgl-rewrites fgl::4vec->upper-of-integer
                             fgl::4vec->lower-of-integer)

   (fgl::def-fgl-rewrite fgl::4vec->lower-of-int
     (equal (sv::4vec->lower (fgl::int x))
            (ifix x))
     :hints(("Goal" :in-theory (enable sv::4vec->lower))))

   (fgl::def-fgl-rewrite fgl::4vec->upper-of-int
     (equal (sv::4vec->upper (fgl::int x))
            (ifix x))
     :hints(("Goal" :in-theory (enable sv::4vec->upper))))

   (fgl::add-fgl-rewrite sv::nth-redef)

   (fgl::add-fgl-rewrite sv::svtv-fsm-run-is-base-fsm-run)
   (fgl::remove-fgl-rewrites sv::svtv-fsm-run)

   (fgl::remove-fgl-rewrites sv::svtv-env-to-values)
   (fgl::remove-fgl-rewrites sv::join-val/test-envs)

   (fgl::add-fgl-rewrite sv::lookup-in-join-val/test-envs)

   ;; (fgl::def-fgl-rewrite integerp-of-svex-env-lookup
   ;;   (equal (integerp (sv::svex-env-lookup k x))
   ;;          (sv::2vec-p (sv::svex-env-lookup k x)))
   ;;   :hints(("Goal" :in-theory (enable sv::integerp-when-2vec-p))))
   ))

;; ************************************************************************
;;  NOTE: This book is CURRENTLY MARKED BROKEN in books/GNUMakefile, because
;;  the following theorem is failing on the build server at leeroy.defthm.com.
;;  Specifically, it comes back with an error:
;;
;;     Vacuity check did not finish
;;
;;  which suggests that the SAT solver is producing unexpected output or
;;  failing to solve the problem submitted by the vacuity check on the
;;  hypothesis.  To debug this, you can examine the output on that server
;;  from:
;;
;;     (include-book "centaur/satlink/top" :dir :system)
;;     (satlink::sat '((3) (3)) satlink::env$)
;;
;;  If anyone fixes this, please remove this book from BROKEN_BOOKS in
;;  GNUMakefile.
;;  ************************************************************************




(fgl::def-fgl-thm counter-step-does-not-overflow-symbolic
  :hyp t
  :concl (b* ((steps (svtv-fsm-run ins nil prev-st (counter-step)
                                   '((count reset incr)
                                     (count))))
              ((list step0 step1) steps)
              (step0 (make-fast-alist step0))
              (step1 (make-fast-alist step1))
              (count0 (svex-env-lookup 'count step0))
              (reset (svex-env-lookup 'reset step0))
              (incr (svex-env-lookup 'incr step0))
              (count1 (svex-env-lookup 'count step1)))
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
  :g-bindings nil)

(acl2::must-fail
 (fgl::def-fgl-thm counter-step-does-not-overflow-symbolic-bug
   :hyp t
   :concl (b* ((steps (svtv-fsm-run ins nil prev-st (counter-step)
                                   '((count reset incr)
                                     (count))))
               ((list step0 step1) steps)
               (step0 (make-fast-alist step0))
               (step1 (make-fast-alist step1))
               (count0 (svex-env-lookup 'count step0))
               (reset (svex-env-lookup 'reset step0))
               (incr (svex-env-lookup 'incr step0))
               (count1 (svex-env-lookup 'count step1)))
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
   :rule-classes nil))

;; (defthm counter-step-no-cycle-vars
;;   (and (not (svarlist-has-svex-cycle-var (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm (counter-step))))))
;;        (not (svarlist-has-svex-cycle-var (svex-alist-vars (base-fsm->nextstate (svtv-fsm->base-fsm (counter-step))))))
;;        (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->outexprs (counter-step))))))
;;   :hints(("Goal" :in-theory (enable (counter-step)))))

(define counter-step-preconds ((step svex-env-p))
  (and (2vec-p (svex-env-lookup 'reset step))
       (2vec-p (svex-env-lookup 'incr step))))

(define counter-step-invariant ((step svex-env-p))
  (b* ((count (svex-env-lookup 'count step)))
    (and (2vec-p count)
         (< (2vec->val count) 10))))


(defthm counter-step-does-not-overflow-invariant
  (b* ((steps (svtv-fsm-eval (list env0 env1) nil init-st (counter-step)))
       ((list step0 step1) steps))

    (implies (and (counter-step-preconds step0)
                  (counter-step-invariant step0)
                  ;; (set-equiv (alist-keys (svex-env-fix init-st))
                  ;;            (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm (counter-step)))))
                  )
             (counter-step-invariant step1)))
  :hints (("goal" :in-theory (e/d (svtv-fsm-run-is-extract-of-eval
                                   svex-envlist-extract
                                   counter-step-preconds
                                   counter-step-invariant)
                                  ((counter-step)
                                   2vec-p
                                   counter-step-does-not-overflow-symbolic
                                   ;; ap hacking
                                   svex-env-extract-when-alist-keys-equal
                                   append
                                   acl2::append-when-not-consp
                                   (tau-system)))
           :use ((:instance counter-step-does-not-overflow-symbolic
                  (ins (list env0 env1))
                  (prev-st init-st))))))

(define counter-step-invariant-holds ((steps svex-envlist-p))
  :guard (consp steps)
  (and (counter-step-invariant (car steps))
       (or (not (counter-step-preconds (car steps)))
           (atom (cdr steps))
           (counter-step-invariant-holds (cdr steps)))))



(local (defthm consp-of-svtv-fsm-eval
         (equal (consp (svtv-fsm-eval ins overrides initst fsm))
                (consp ins))
         :hints(("Goal" :in-theory (enable svtv-fsm-eval)))))

(defthm counter-step-does-not-overflow
  (implies (and (consp envs)
                ;; (set-equiv (alist-keys (svex-env-fix init-st))
                ;;            (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm (counter-step)))))
                )
           (b* ((steps (svtv-fsm-eval envs nil init-st (counter-step))))
             (implies (counter-step-invariant (car steps))
                      (counter-step-invariant-holds steps))))
  :hints (("goal" :induct (svtv-fsm-eval envs nil init-st (counter-step))
           :in-theory (e/d (counter-step-invariant-holds
                            counter-step-invariant
                            counter-step-preconds
                            (:i svtv-fsm-eval))
                           (2vec-p
                            2vec->val
                            append
                            ;; sv::car-of-svtv-fsm-eval
                            ;; sv::cdr-of-svtv-fsm-eval
                            ;; sv::svtv-fsm-eval-of-cons
                            acl2::append-when-not-consp
                            counter-step-does-not-overflow-invariant
                            ;; ap hacking
                            svex-env-extract-when-alist-keys-equal
                            svex-env-p-when-not-consp
                            acl2::alist-keys-when-atom
                            (tau-system)))
           :expand ((svtv-fsm-eval envs nil init-st (counter-step))))
          (and stable-under-simplificationp
               '(:use ((:instance counter-step-does-not-overflow-invariant
                        (env0 (car envs))
                        (env1 (cadr envs))))
                 :expand ((:free (a b initst fsm) (svtv-fsm-eval (cons a b) nil initst fsm)))))))
