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

(include-book "assign")
(include-book "fsm")
(include-book "probe")
(include-book "compose-phases")
(include-book "../svex/rewrite")
(include-book "../svex/alist-equiv")
(local (std::add-default-post-define-hook :fix))





;; First goal: make a set of svex alists that symbolically gives the outputs
;; from an svtv-fsm-run.  Then, extract those outputs into a single
;; svex alist in the style of svtv-run.  Additionally, parse a defsvtv-like
;; form into symbolic inputs for this symbolic svtv-fsm-run.

;; Ingredients: svtv-fsm-run can be phrased as

;; (svtv-fsm-run-extract-outs
;;  outvars
;;  (svtv-fsm-run
;;   (svtv-fsm-run-input-envs inputs override-tests x)
;;   prev-st
;;   x
;;   (svtv-fsm-run-output-signals (take (len inputs) outvars) x))
;;  x)

;; (svtv-fsm-run-output-signals (take (len inputs) outvars) x) has no symbolic components
;; so it can remain the same.

;; (svtv-fsm-run-input-envs inputs override-tests x) becomes
;; svtv-fsm-run-input-substs.

;; svtv-fsm-run becomes a series of svex-alist-compose-svtv-phases

;; svtv-fsm-run-extract-outs becomes a series of 
;; (svex-alist-subst
;;   (svtv-name-lhs-map-to-svex-alist (fal-extract outvars) x.namemap)
;;   full-outs)
;; as in svtv-fsm-step-extract-outs.

(local (defthm len-of-svex-alist-keys
         (implies (svex-alist-p x)
                  (equal (len (svex-alist-keys x))
                         (len x)))
         :hints(("Goal" :in-theory (enable svex-alist-p svex-alist-keys)))))

(local (defthm svex-alist-keys-of-svex-alist-extract
         (equal (svex-alist-keys (svex-alist-extract vars x))
                (svarlist-fix vars))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-extract)))))

(local (defthm len-of-svexlist-compose-svtv-phases
         (equal (len (svexlist-compose-svtv-phases x phase data))
                (len x))
         :hints(("Goal" :in-theory (enable svexlist-compose-svtv-phases)))))

(define base-fsm-run-compile-phase ((phase natp)
                                    (outvars svarlist-p)
                                    (out-values svex-alist-p)
                                    (data svtv-composedata-p))
  :returns (out-alist svex-alist-p)
  (b* ((alist (svex-alist-extract outvars out-values)))
    (svex-alist-compose-svtv-phases alist phase data))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval out-alist env)
           (b* (((svtv-composedata data)))
             (pairlis$ (svarlist-fix outvars)
                       (svexlist-eval-unroll-multienv
                        (svex-alist-vals (svex-alist-extract outvars out-values))
                        phase
                        data.nextstates
                        (svex-alistlist-eval data.input-substs env)
                        (svex-alist-eval data.initst env)))))
    :hints(("Goal" :in-theory (enable svex-alist-compose-svtv-phases-correct)))))



(local
 (std::defret-mutual take-in-envs-of-svex-eval-unroll-multienv
   (defret take-in-envs-of-<fn>
     (implies (< (nfix cycle) (nfix n))
              (equal (let ((in-envs (take n in-envs))) <call>)
                     new-x))
     :hints ('(:expand ((:free (in-envs cycle) <call>))))
     :fn svex-eval-unroll-multienv)
   (defret take-in-envs-of-<fn>
     (implies (< (nfix cycle) (nfix n))
              (equal (let ((in-envs (take n in-envs))) <call>)
                     new-x))
     :hints ('(:expand ((:free (in-envs) <call>))))
     :fn svexlist-eval-unroll-multienv)
   :mutual-recursion svex-eval-unroll-multienv))
            
            


(define base-fsm-run-compile-phases ((phase natp)
                                     (outvars svarlist-list-p)
                                     (out-values svex-alist-p)
                                     (data svtv-composedata-p))
  :returns (out-alists svex-alistlist-p)
  (if (atom outvars)
      nil
    (cons (base-fsm-run-compile-phase phase (car outvars) out-values data)
          (base-fsm-run-compile-phases (1+ (lnfix phase)) (cdr outvars) out-values data)))
  ///
  (local (defthm svex-env-extract-nil
           (equal (svex-env-extract nil env) nil)
           :hints(("Goal" :in-theory (enable svex-env-extract)))))

  (local (defthm nth-of-svex-envlist-extract
           (equal (nth n (svex-envlist-extract lst envs))
                  (svex-env-extract (nth n lst) (nth n envs)))
           :hints(("Goal" :in-theory (enable nth svex-envlist-extract)
                   :induct t))))

  (local (defun eval-nth-ind (n phase outvars out-values data)
           (if (atom outvars)
               (list n phase out-values data)
             (eval-nth-ind (1- (nfix n)) (1+ (nfix phase)) (cdr outvars) out-values data))))

  (local (include-book "std/lists/nth" :dir :system))
  (local (include-book "std/lists/take" :dir :system))
  ;; (local (defthm consp-of-take
  ;;          (equal (consp (take n x))
  ;;                 (posp n))
  ;;          :hints(("Goal" :in-theory (enable take)))))
  ;; (local (defthm len-of-take
  ;;          (equal (len (take n x))
  ;;                 (nfix n))))


  (local (defthm svex-env-lookup-of-pairlis-svexlist-eval-unroll-multienv
           (equal (svex-env-lookup var
                                   (pairlis$ (svex-alist-keys out-alist)
                                             (svexlist-eval-unroll-multienv
                                              (svex-alist-vals out-alist)
                                              phase nextstates ins initst)))
                  (svex-eval-unroll-multienv
                   (svex-lookup var out-alist)
                   phase nextstates ins initst))
           :hints(("Goal" :in-theory (enable svexlist-eval-unroll-multienv
                                             svex-alist-keys
                                             svex-alist-vals
                                             svex-env-lookup
                                             svex-lookup)
                   :induct t
                   :expand ((svex-eval-unroll-multienv '(-1 . 0) phase nextstates ins initst))))))

  (local (defthm svex-env-extract-of-pairlis-svexlist-eval-unroll-multienv
           (equal (svex-env-extract outvars
                                    (pairlis$ (svex-alist-keys out-alist)
                                              (svexlist-eval-unroll-multienv
                                               (svex-alist-vals out-alist)
                                               phase nextstates ins initst)))
                  (pairlis$ (svarlist-fix outvars)
                            (svexlist-eval-unroll-multienv
                             (svex-alist-vals (svex-alist-extract outvars out-alist))
                             phase nextstates ins initst)))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svex-alist-extract
                                             svex-alist-vals
                                             svexlist-eval-unroll-multienv)))))
                             


  ;; (defret eval-nth-of-<fn>
  ;;   (equal (svex-alist-eval (nth n out-alists) env)
  ;;          (b* (((svtv-composedata data)))
  ;;            (nth (+ (nfix phase) (nfix n))
  ;;                 (svtv-fsm-run (svex-alistlist-eval data.input-substs env)
  ;;                               (svex-alist-eval data.initst env)
  ;;                               (make-svtv-fsm :nextstate data.nextstates
  ;;                                              :values out-values)
  ;;                               (append (repeat phase nil) outvars)))))
  ;;   :hints(("Goal" :in-theory (e/d (svtv-fsm-run
  ;;                                   svtv-fsm-eval-is-svex-eval-unroll-multienv)
  ;;                                  (car-of-svtv-fsm-eval
  ;;                                   svtv-fsm-eval-of-cons
  ;;                                   acl2::take-of-too-many
  ;;                                   take))
  ;;           :expand ((svex-alist-eval nil env)
  ;;                    (:free (n a b) (nth n (cons a b))))
  ;;           :induct (eval-nth-ind n phase outvars out-values data))))

  (local (defthm nthcdr-gte-len
           (implies (and (true-listp x)
                         (<= (len x) (nfix n)))
                    (equal (nthcdr n x) nil))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (local (defthm nthcdr-of-svex-envlist-extract
           (equal (nthcdr n (svex-envlist-extract vars envs))
                  (svex-envlist-extract (nthcdr n vars) (nthcdr n envs)))
           :hints(("Goal" :in-theory (enable svex-envlist-extract nthcdr)))))

  (local (defthm cdr-nthcdr
           (equal (cdr (nthcdr n x))
                  (nthcdr n (cdr x)))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (local (defthm car-nthcdr
           (equal (car (nthcdr n x))
                  (nth n x))
           :hints(("Goal" :in-theory (enable nthcdr nth)))))

  (local (defthm len-of-take
           (equal (len (take n x))
                  (nfix n))
           :hints(("Goal" :in-theory (enable take)))))

  (defret svex-alistlist-eval-of-<fn>
    (equal (svex-alistlist-eval out-alists env)
           (b* (((svtv-composedata data)))
             (nthcdr phase
                     (base-fsm-run (svex-alistlist-eval data.input-substs env)
                                   (svex-alist-eval data.initst env)
                                   (make-base-fsm :nextstate data.nextstates
                                                  :values out-values)
                                   (append (repeat phase nil) outvars)))))
    :hints(("Goal" :in-theory (e/d (base-fsm-run
                                    ;; svex-envlist-extract
                                    base-fsm-eval-is-svex-eval-unroll-multienv)
                                   (car-of-base-fsm-eval
                                    cdr-of-base-fsm-eval
                                    base-fsm-eval-of-cons
                                    acl2::take-of-too-many
                                    nthcdr-of-base-fsm-eval-is-base-fsm-eval
                                    take))
            :expand ((svex-alist-eval nil env)
                     (:free (n a b) (nth n (cons a b)))
                     ;; (:free (x ins initst fsm) (base-fsm-eval (take (+ 1 x) ins) initst fsm))
                     (:free (x) (svex-envlist-extract outvars x)))
            :induct (eval-nth-ind n phase outvars out-values data)))))



         

(define make-fast-alistlist (x)
  :returns (new-x (equal new-x x))
  (if (atom x)
      x
    (cons-with-hint
     (make-fast-alist (car x))
     (make-fast-alistlist (cdr x))
     x)))

(define fast-alistlist-clean-aux (x)
  (if (atom x)
      nil
    (let ((ans1 (fast-alist-clean (car x))))
      (declare (ignore ans1))
      (fast-alistlist-clean-aux (cdr x)))))

(define fast-alistlist-clean (x)
  (mbe :logic x
       :exec (let ((ans1 (fast-alistlist-clean-aux x)))
               (declare (ignore ans1))
               x)))
  

(define base-fsm-run-compile ((ins svex-alistlist-p)
                              (prev-st svex-alist-p)
                              (x base-fsm-p)
                              (signals svarlist-list-p)
                              (rewrite booleanp))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (out-alists svex-alistlist-p)
  (b* (((base-fsm x))
       ((acl2::with-fast x.nextstate x.values prev-st))
       (composedata (make-svtv-composedata :nextstates x.nextstate
                                           :input-substs (make-fast-alistlist ins)
                                           :initst prev-st
                                           :rewrite rewrite))
       (ans (base-fsm-run-compile-phases 0 signals x.values composedata)))
    (fast-alistlist-clean ins)
    ans)
  ///
  (defret svex-alistlist-eval-of-<fn>
    (equal (svex-alistlist-eval out-alists env)
           (base-fsm-run (svex-alistlist-eval ins env)
                         (svex-alist-eval prev-st env)
                         x
                         signals))))


;; (define svtv-fsm-step-compile-extract-outs ((outvars svarlist-p)
;;                                                     (full-outs svex-alist-p)
;;                                                     (x svtv-fsm-p))
;;   :returns (outs svex-alist-p)
;;   (b* (((svtv-fsm x))
;;        (out-alist1 (acl2::fal-extract (svarlist-fix outvars) x.renamed-values)))
;;     (with-fast-alist full-outs
;;       (svtv-name-lhs-map-subst out-alist1 full-outs)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval outs env)
;;            (svtv-fsm-step-extract-outs
;;             outvars (svex-alist-eval full-outs env) x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-step-extract-outs)))))
       

;; (define svtv-fsm-run-compile-extract-outs ((outvars svarlist-list-p)
;;                                                    (full-outs svex-alistlist-p)
;;                                                    (x svtv-fsm-p))
;;   :returns (outs svex-alistlist-p)
;;   (if (atom outvars)
;;       nil
;;     (cons (svtv-fsm-step-compile-extract-outs (car outvars) (car full-outs) x)
;;           (svtv-fsm-run-compile-extract-outs (cdr outvars) (cdr full-outs) x)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alistlist-eval outs env)
;;            (svtv-fsm-run-extract-outs
;;             outvars (svex-alistlist-eval full-outs env) x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-run-extract-outs
;;                                       svex-alistlist-eval)
;;             :expand ((svex-alist-eval nil env))))))

(local (in-theory (disable hons-dups-p)))




(define svtv-fsm-run-compile ((ins svex-alistlist-p)
                                      (overrides svex-alistlist-p)
                                      (prev-st svex-alist-p)
                                      (x svtv-fsm-p)
                                      (outvars svarlist-list-p)
                                      (rewrite booleanp))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints (("goal" :in-theory (enable svtv-fsm->renamed-fsm)))
  :returns (out-alists svex-alistlist-p)
  (b* ((input-substs (svtv-fsm-run-input-substs
                      (take (len outvars) ins)
                      overrides x))
       ((svtv-fsm x)))
    (base-fsm-run-compile input-substs prev-st x.renamed-fsm outvars rewrite))
  ///

  (local (defthm take-of-svex-alistlist-eval
           (equal (take n (svex-alistlist-eval x env))
                  (svex-alistlist-eval (take n x) env))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-eval)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :expand ((svex-alist-eval nil env))))))

  (defret eval-of-<fn>
    (equal (svex-alistlist-eval out-alists env)
           (svtv-fsm-run
            (svex-alistlist-eval ins env)
            (svex-alistlist-eval overrides env)
            (svex-alist-eval prev-st env)
            x
            outvars))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-is-base-fsm-run))))

  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup var (nth n out-alists)) env)
           (svex-env-lookup var (nth n (svtv-fsm-run
                                        (svex-alistlist-eval ins env)
                                        (svex-alistlist-eval overrides env)
                                        (svex-alist-eval prev-st env)
                                        x
                                        outvars))))
    :hints(("Goal" :use eval-of-<fn>
            :in-theory (disable eval-of-<fn> <fn>))))

  (local
   (defret lookup-under-iff-of-<fn>
     (iff (svex-lookup var (nth n out-alists))
          (svex-env-boundp var (nth n (svtv-fsm-run
                                       (svex-alistlist-eval ins env)
                                       (svex-alistlist-eval overrides env)
                                       (svex-alist-eval prev-st env)
                                       x
                                       outvars))))
     :hints(("Goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn> <fn>)))))

  (local
   (defret len-of-<fn>
     (equal (len out-alists)
            (len (svtv-fsm-run
                  (svex-alistlist-eval ins env)
                  (svex-alistlist-eval overrides env)
                  (svex-alist-eval prev-st env)
                  x
                  outvars)))
     :hints(("Goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn> <fn> len-of-svtv-fsm-run)))))


  (defret normalize-<fn>-rewrite-under-svex-alistlist-eval-equiv
    (implies (syntaxp (not (equal rewrite ''nil)))
             (svex-alistlist-eval-equiv out-alists
                                        (let ((rewrite nil)) <call>)))
    :hints (("goal" :in-theory (disable <fn>))
            (witness) (witness) (witness)))

  (local (defthm take-of-svex-alistlist-fix
           (equal (take n (svex-alistlist-fix x))
                  (svex-alistlist-fix (take n x)))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-fix)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))))))

  (defcong svtv-fsm-eval/namemap-equiv svex-alistlist-eval-equiv
    (svtv-fsm-run-compile ins overrides prev-st x outvars rewrite) 4
    :hints (("goal" :in-theory (disable svtv-fsm-run-compile))
            (witness) (witness) (witness))))
       



                               

(local (defthm rassoc-equal-of-lookup
         (implies (And (hons-assoc-equal key x)
                       (alistp x))
                  (rassoc-equal (cdr (hons-assoc-equal key x)) x))
         :hints(("Goal" :in-theory (enable hons-assoc-equal rassoc-equal)))))

(local (defthm alistp-when-svtv-probealist-p-rw
         (implies (svtv-probealist-p probes)
                  (alistp probes))
         :hints(("Goal" :in-theory (enable svtv-probealist-p)))))

(local (defthm svarlist-p-of-nth
         (implies (svarlist-list-p x)
                  (svarlist-p (nth n x)))
         :hints(("Goal" :in-theory (enable nth svarlist-p)))))

(encapsulate nil
  (local
   (defun take-of-in-envs-ind (n ins override-tests)
     (if (zp n)
         (list ins override-tests)
       (take-of-in-envs-ind (1- n) (cdr ins) (cdr override-tests)))))

  (defthm take-of-svtv-fsm-run-input-envs
           (equal (take n (svtv-fsm-run-input-envs (take n ins) override-tests x))
                  (svtv-fsm-run-input-envs (take n ins) override-tests x))
           :hints(("Goal" :in-theory (e/d (svtv-fsm-run-input-envs)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (take-of-in-envs-ind n ins override-tests)))))

(defthm lookup-in-pipeline
  (equal (svex-eval (svex-lookup name
                                 (svtv-probealist-extract-alist
                                  probes
                                  (svtv-fsm-run-compile
                                   inputs overrides initst fsm
                                   (svtv-probealist-outvars probes) rewrite)))
                    env)
         (b* ((inputs-eval (svex-alistlist-eval inputs env))
              (overrides-eval (svex-alistlist-eval overrides env))
              (initst-eval (svex-alist-eval initst env))
              (probe-look (hons-assoc-equal (svar-fix name) (svtv-probealist-fix probes)))
              ((svtv-probe probe) (cdr probe-look))
              (ins (svtv-fsm-run-input-envs
                    (take (len (svtv-probealist-outvars probes)) inputs-eval)
                    overrides-eval fsm)))
           (if probe-look
               (svex-env-lookup
                probe.signal
                (nth probe.time (base-fsm-run
                                 ins initst-eval
                                 (svtv-fsm->renamed-fsm fsm)
                                 (svtv-probealist-outvars probes))))
             (4vec-x))))
  :hints(("Goal" :in-theory (e/d (SVTV-FSM-RUN-IS-EXTRACT-OF-EVAL
                                    ;; lookup-of-svtv-fsm-step-extract-outs
                                    svtv-fsm-eval-is-svtv-fsm-eval-of-input-envs)
                                 (nth)))))
