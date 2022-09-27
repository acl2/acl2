; SV - Symbolic Vector Hardware Analysis Framework
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "probe")
(include-book "cycle-compile")
(include-book "assign")
(local (std::add-default-post-define-hook :fix))

(define svtv-name-lhs-map-eval-list ((namemap svtv-name-lhs-map-p)
                                     (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svtv-name-lhs-map-eval namemap (car envs))
          (svtv-name-lhs-map-eval-list namemap (cdr envs))))
  ///
  (defret nth-of-<fn>
    (equal (nth n new-envs)
           (and (< (lnfix n) (len envs))
                (svtv-name-lhs-map-eval namemap (nth n envs))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth n envs))))

  (defret len-of-<fn>
    (Equal (len new-envs) (len envs))))

(define svtv-probealist-cycle-adjust-aux ((x svtv-probealist-p)
                                          (cycle-len posp)
                                          (cycle-outphase natp))
  :returns (new-x svtv-probealist-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (consp (car x))))
        (svtv-probealist-cycle-adjust-aux (cdr x) cycle-len cycle-outphase))
       ((cons var (svtv-probe pr)) (car x)))
    (cons (cons (svar-fix var) (change-svtv-probe pr :time (+ (* pr.time (lposfix cycle-len))
                                                              (lnfix cycle-outphase))))
          (svtv-probealist-cycle-adjust-aux (cdr x) cycle-len cycle-outphase)))
  ///
  (local (defthmd len-of-svtv-cycle-run-fsm-inputs
           (equal (len (svtv-cycle-run-fsm-inputs ins phases))
                  (* (len ins) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs)))))

  (local (defthm svtv-cycle-output-phase-limit
           (implies (svtv-cycle-output-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
           :rule-classes :linear))

  (local (defthm cycle-output-phase-bound
           (implies (and (natp probe-time)
                         (svtv-cycle-output-phase phases))
                    (iff (> (len (svtv-cycle-run-fsm-inputs ins phases))
                            (+ (SVTV-CYCLE-OUTPUT-PHASE PHASES)
                               (* (LEN PHASES)
                                  probe-time)))
                         (< probe-time (LEN INS))))
           :hints(("Goal" :in-theory (enable len-of-svtv-cycle-run-fsm-inputs))
                  (and stable-under-simplificationp
                       '(:nonlinearp t)))))

  (defret <fn>-correct
    (implies (and (equal cycle-len (len phases))
                  (equal cycle-outphase (svtv-cycle-output-phase phases))
                  cycle-outphase)
             (equal (svtv-probealist-extract x (base-fsm-eval ins initst (base-fsm-to-cycle phases fsm simp)))
                    (svtv-probealist-extract
                     new-x (base-fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm))))
    :hints(("Goal"
            :expand (<call>
                     (:free (eval) (svtv-probealist-extract x eval))
                     (:free (eval) (svtv-probealist-extract nil eval))
                     (:free (eval a b) (svtv-probealist-extract (cons a b) eval)))
            :induct <call>)))

  (defret <fn>-correct-name-lhs-map-eval-list
    (implies (and (equal cycle-len (len phases))
                  (equal cycle-outphase (svtv-cycle-output-phase phases))
                  cycle-outphase)
             (equal (svtv-probealist-extract x (svtv-name-lhs-map-eval-list
                                                map
                                                (base-fsm-eval ins initst (base-fsm-to-cycle phases fsm simp))))
                    (svtv-probealist-extract
                     new-x
                     (svtv-name-lhs-map-eval-list
                      map
                      (base-fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm)))))
    :hints(("Goal"
            :expand (<call>
                     (svtv-name-lhs-map-eval map nil)
                     (:free (eval) (svtv-probealist-extract x eval))
                     (:free (eval) (svtv-probealist-extract nil eval))
                     (:free (eval a b) (svtv-probealist-extract (cons a b) eval)))
            :induct <call>)))

  (local (in-theory (enable svtv-probealist-fix))))


(define svtv-probealist-cycle-adjust ((x svtv-probealist-p)
                                      (phases svtv-cyclephaselist-p))
  :returns (new-x svtv-probealist-p)
  (b* ((len (pos-fix (len phases)))
       (outphase (or (svtv-cycle-output-phase phases) 0)))
    (svtv-probealist-cycle-adjust-aux x len outphase))
  ///
  (local (defthm svtv-cycle-output-phase-limit
           (implies (svtv-cycle-output-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
           :rule-classes :linear))
  
  (defret <fn>-correct
    (implies (svtv-cycle-output-phase phases)
             (equal (svtv-probealist-extract x (base-fsm-eval ins initst (base-fsm-to-cycle phases fsm simp)))
                    (svtv-probealist-extract
                     new-x (base-fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm)))))

  (defret <fn>-correct-name-lhs-map-eval-list
    (implies (svtv-cycle-output-phase phases)
             (equal (svtv-probealist-extract x (svtv-name-lhs-map-eval-list
                                                map
                                                (base-fsm-eval ins initst (base-fsm-to-cycle phases fsm simp))))
                    (svtv-probealist-extract
                     new-x
                     (svtv-name-lhs-map-eval-list
                      map
                      (base-fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm)))))))
