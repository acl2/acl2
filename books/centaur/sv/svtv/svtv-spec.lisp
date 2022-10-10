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

;; (include-book "svtv-fsm-ideal")
(include-book "cycle-probe")
(include-book "assign")
(local (include-book "../svex/svex-lattice"))  
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (in-theory (disable floor mod)))

(local (std::add-default-post-define-hook :fix))

;; How to "run" an ideal FSM as a pseudo-SVTV --

;; When we do cutpoint proofs using SVTVs, the composition is done relative to
;; the idealized FSM, but we still want to give a high-level, SVTV-like
;; interface for it.  So we wrap it in a structure like an SVTV that has all
;; the mappings etc. to give it that interface.

(defthm svex-env-p-nth-of-svex-envlist
  (implies (svex-envlist-p x)
           (svex-env-p (nth n x))))

(defthm nthcdr-of-svex-envlist-fix
  (equal (nthcdr n (svex-envlist-fix x))
         (svex-envlist-fix (nthcdr n x)))
  :hints(("Goal" :in-theory (enable svex-envlist-fix))))


(defthm svtv-cycle-output-phase-iff-has-outputs-captured
  (iff (svtv-cycle-output-phase phases)
       (svtv-cyclephaselist-has-outputs-captured phases))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured))))

(defthm svtv-cycle-output-phase-type-when-has-outputs-captured
  (implies (svtv-cyclephaselist-has-outputs-captured x)
           (natp (svtv-cycle-output-phase x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured)))
  :rule-classes :type-prescription)

(defthm svtv-cyclephaselist-has-outputs-captured-when-atom
  (implies (atom x)
           (not (svtv-cyclephaselist-has-outputs-captured x)))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured))))

(define svex-envlist-phase-outputs-extract-cycle-outputs ((phases svtv-cyclephaselist-p)
                                                          (phase-outs svex-envlist-p))
  :guard (svtv-cycle-output-phase phases)
  :returns (cycle-outs svex-envlist-p)
  :measure (len phase-outs)
  (if (atom phase-outs)
      nil
    (cons (svex-env-fix (nth (svtv-cycle-output-phase phases) phase-outs))
          (svex-envlist-phase-outputs-extract-cycle-outputs
           phases
           (nthcdr (if (mbt (consp phases))
                       (len phases)
                     1)
                   phase-outs))))
  ///

  (local (defun nth-of-extract-ind (n phases phase-outs)
           (if (zp n)
               (list phases phase-outs)
             (nth-of-extract-ind (1- n) phases (nthcdr (len phases) phase-outs)))))

  (local (defthm natp-of-times-decr-lemma
           (implies (and (posp n)
                         (natp len)
                         (natp m))
                    (natp (+ (- len)
                             m
                             (* n len))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))
           :rule-classes :type-prescription))

  (local (defthm plus-x-y-minus-x-z
           (equal (+ x y (* -1 x) z)
                  (+ y z))))
  
  (defret nth-of-<fn>
    (implies (svtv-cyclephaselist-has-outputs-captured phases)
             (Equal (nth n cycle-outs)
                    (svex-env-fix (nth (+ (svtv-cycle-output-phase phases)
                                          (* (nfix n) (len phases)))
                                       phase-outs))))
    :hints (("goal" :induct (nth-of-extract-ind n phases phase-outs)
             :expand (<call>))))

  (defret len-of-<fn>
    (implies (and (equal 0 (mod (len phase-outs) (len phases)))
                  (consp phases))
             (equal (len cycle-outs)
                    (floor (len phase-outs) (len phases))))
    :hints(("Goal" :in-theory (enable acl2::mod-redef acl2::floor-redef))))

  (local (defthm svtv-cyclephaselist-has-outputs-captured-implies-posp-len
           (implies (svtv-cyclephaselist-has-outputs-captured phases)
                    (posp (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured)))
           :rule-classes :forward-chaining))
  
  (defthm svtv-probealist-extract-of-probealist-cycle-adjust
    (implies (svtv-cyclephaselist-has-outputs-captured phases)
             (equal (svtv-probealist-extract (svtv-probealist-cycle-adjust probes phases) phase-outputs)
                    (svtv-probealist-extract probes (svex-envlist-phase-outputs-extract-cycle-outputs phases phase-outputs))))
    :hints(("Goal" :in-theory (enable svtv-probealist-extract
                                      svtv-probealist-cycle-adjust
                                      svtv-probealist-cycle-adjust-aux)
            :induct (len probes))))

    (local
   (defthm svtv-name-lhs-map-eval-list-under-iff
     (iff (svtv-name-lhs-map-eval-list namemap envs)
          (consp envs))
     :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))

  (local (defthm consp-of-svex-envlist-phase-outputs-extract-cycle-outputs
           (equal (consp (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))
                  (consp envs))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)))))

  
  (local (defthm mod-0-when-less
           (implies (and (natp x) (natp y)
                         (< x y))
                    (equal (equal 0 (mod x y))
                           (equal x 0)))
           :hints (("goal" :in-theory (e/d (acl2::mod-redef) (mod))))))
          

  (local (defthm nthcdr-of-svtv-name-lhs-map-eval-list
           (equal (nthcdr n (svtv-name-lhs-map-eval-list namemap envs))
                  (svtv-name-lhs-map-eval-list namemap (nthcdr n envs)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))


  (local (defthm consp-of-svtv-name-lhs-map-eval-list
           (equal (consp (svtv-name-lhs-map-eval-list namemap envs))
                  (consp envs))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))

  (local (defthm svtv-cycle-output-phase-<-len
           (implies (svtv-cyclephaselist-has-outputs-captured phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                             svtv-cyclephaselist-has-outputs-captured)))
           :rule-classes :linear))
  
  (defthm svex-envlist-phase-outputs-extract-cycle-outputs-of-svtv-name-lhs-map-eval-list
    (implies (and (equal 0 (mod (len envs) (len phases)))
                  (svtv-cyclephaselist-has-outputs-captured phases))
             (equal (svex-envlist-phase-outputs-extract-cycle-outputs phases (svtv-name-lhs-map-eval-list namemap envs))
                    (svtv-name-lhs-map-eval-list namemap (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))))
    :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs
                                      svtv-name-lhs-map-eval-list
                                      acl2::mod-redef)
            :induct (svex-envlist-phase-outputs-extract-cycle-outputs phases envs)
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases
                                                                       (svtv-name-lhs-map-eval-list namemap envs))))
           (and stable-under-simplificationp
                '(:cases ((equal (len envs) (svtv-cycle-output-phase phases))))))))




(define 4vec-x-override ((a 4vec-p)
                         (b 4vec-p))
  ;; For each bit, the result is the corresp bit of a unless that bit is x, else the corresponding bit of b.
  :returns (res 4vec-p)
  (b* (((4vec a))
       ((4vec b))
       (a-non-x-mask (logior (lognot a.upper) a.lower)))
    (4vec (logior (logand a-non-x-mask a.upper)
                  (logandc1 a-non-x-mask b.upper))
          (logior (logand a-non-x-mask a.lower)
                  (logandc1 a-non-x-mask b.lower))))
  ///
  (defret 4vec-bit-index-of-<fn>
    (equal (4vec-bit-index n res)
           (b* ((an (4vec-bit-index n a)))
             (if (equal an (4vec-1x))
                 (4vec-bit-index n b)
               an)))
    :hints(("Goal" :in-theory (enable 4vec-bit-index))))

  (defret 4vec-x-override->>=-a
    (4vec-<<= a res)
    :hints(("Goal" :in-theory (enable 4vec-<<=))
           (bitops::logbitp-reasoning)))

  (defret 4vec-x-override-when-a-<<=-b
    (implies (4vec-<<= a b)
             (equal res (4vec-fix b)))
    :hints(("Goal" :in-theory (enable 4vec-<<=))
           (bitops::logbitp-reasoning)))

  (defthm 4vec-x-override-of-x
    (and (equal (4vec-x-override (4vec-x) b) (4vec-fix b))
         (equal (4vec-x-override a (4vec-x)) (4vec-fix a)))
    :hints ((bitops::logbitp-reasoning)))

  (defthm 4vec-x-override-monotonic-on-b
    (implies (4vec-<<= b1 b2)
             (4vec-<<= (4vec-x-override a b1)
                       (4vec-x-override a b2)))
    :hints(("Goal" :in-theory (enable 4vec-<<=))
           (bitops::logbitp-reasoning))))


(define svex-env-x-override ((a svex-env-p) (b svex-env-p))
  :returns (res svex-env-p)
  (if (atom b)
      (svex-env-fix a)
    (if (mbt (and (consp (car b))
                  (svar-p (caar b))))
        (cons (cons (caar b)
                    (4vec-x-override (svex-env-lookup (caar b) a) (cdar b)))
              (svex-env-x-override a (cdr b)))
      (svex-env-x-override a (cdr b))))
  ///
  (defret lookup-in-<fn>
    (equal (svex-env-lookup v res)
           (4vec-x-override (svex-env-lookup v a)
                            (svex-env-lookup v b)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (defret boundp-of-<fn>
    (equal (svex-env-boundp v res)
           (or (svex-env-boundp v b)
               (svex-env-boundp v a)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret <fn>-when-a-<<=-b
    (implies (svex-env-<<= a b)
             (svex-envs-similar res b))
    :hints(("Goal" :in-theory (enable svex-envs-similar))))

  (defret <fn>-when-b-nil
    :pre-bind ((b nil))
    (equal res (svex-env-fix a)))

  (defret <fn>-when-b-empty
    (implies (svex-envs-similar b nil)
             (svex-envs-similar res a))
    :hints(("Goal" :in-theory (disable <fn>))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret <fn>-lower-bound
    (svex-env-<<= a res)
    :hints(("Goal" :in-theory (e/d (svex-env-<<=)
                                   (<fn>)))))

  (defthm svex-env-x-override-monotonic-on-b
    (implies (svex-env-<<= b1 b2)
             (svex-env-<<= (svex-env-x-override a b1)
                           (svex-env-x-override a b2)))
    :hints(("Goal" :in-theory (e/d (svex-env-<<=)
                                   (svex-env-x-override)))))

  (local (in-theory (enable svex-env-fix))))



(defthmd svex-envlists-similar-rec
  (equal (svex-envlists-similar x y)
         (if (or (atom x) (atom y))
             (and (atom x) (atom y))
           (and (svex-envs-similar (car x) (car y))
                (svex-envlists-similar (cdr x) (cdr y)))))
  :hints (("goal" :cases ((svex-envlists-similar x y))
           :do-not-induct t)
          (and stable-under-simplificationp
               (b* ((lit (assoc 'svex-envlists-similar clause)))
                 `(:expand (,lit)))))
  :rule-classes ((:definition :install-body nil
                  :controller-alist ((svex-envlists-similar t t)))))


(encapsulate nil
  ;; move
  (defthm svex-env-<<=-self
    (svex-env-<<= a a)
    :hints(("Goal" :in-theory (enable svex-env-<<=))))
  
  (defthm svex-envlist-<<=-self
    (svex-envlist-<<= a a)
    :hints(("Goal" :in-theory (enable svex-envlist-<<=))))

  (defthm 4vec-<<=-x-means-equiv-x
    (equal (4vec-<<= x (4vec-x))
           (4vec-equiv x (4vec-x)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable 4vec-<<=
                                      4vec-fix-is-4vec-of-fields)))
            (bitops::logbitp-reasoning)))


  (defthm svex-env-<<=-nil-means-similar-to-nil
    (equal (svex-env-<<= x nil)
           (svex-envs-similar x nil))
    :hints (("Goal" :cases ((svex-env-<<= x nil)))
            (and stable-under-simplificationp
                 '(:expand ((svex-envs-similar x nil))
                   :use ((:instance svex-env-<<=-necc
                          (var (svex-envs-similar-witness x nil))
                          (x x) (y nil))))))))

(define svex-envlist-x-override ((a svex-envlist-p)
                                 (b svex-envlist-p))
  :returns (res svex-envlist-p)
  (cond ((atom b) (svex-envlist-fix a))
        ((atom a) (svex-envlist-fix b))
        (t (cons (svex-env-x-override (car a) (car b))
                 (svex-envlist-x-override (cdr a) (cdr b)))))
  ///
  (defret <fn>-when-a-<<=-b
    (implies (and (svex-envlist-<<= a b)
                  (<= (len a) (len b)))
             (svex-envlists-similar res b))
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec
                                      svex-envlist-<<=))))

  (local (defthm len-equal-0
           (Equal (equal (len x) 0) (atom x))))
  
  (defret <fn>-when-b-empty
    (implies (and (subsetp-equal b '(nil))
                  (<= (len b) (len a)))
             (equal res (svex-envlist-fix a)))
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec
                                      svex-envlist-<<=)
            :induct t
            :expand ((svex-env-x-override (car a) nil)))))

  (defret <fn>-lower-bound
    (svex-envlist-<<= a res)
    :hints(("Goal" :in-theory (e/d (svex-envlist-<<=)))))

  (defret len-of-<fn>
    (equal (len res) (max (len a) (len b))))

  
  (defthm svex-envlist-x-override-monotonic-on-b
    (implies (svex-envlist-<<= b1 b2)
             (svex-envlist-<<= (svex-envlist-x-override a b1)
                               (svex-envlist-x-override a b2)))
    :hints(("Goal" :in-theory (e/d (svex-envlist-<<= svex-envlist-fix)))))

  (defthm svex-envlist-x-override-monotonic-on-a-when-b-is-empty
    (implies (and (svex-envlist-<<= a1 a2)
                  (svex-envlists-similar b nil))
             (svex-envlist-<<= (svex-envlist-x-override a1 b)
                               (svex-envlist-x-override a2 b)))
    :hints(("Goal" :in-theory (e/d (svex-envlist-<<=))))))



(defprod svtv-spec
  ((fsm base-fsm-p)
   (cycle-phases svtv-cyclephaselist-p)
   (namemap svtv-name-lhs-map-p)
   (probes svtv-probealist-p)
   (in-alists svex-alistlist-p)
   (override-test-alists svex-alistlist-p)
   (override-val-alists svex-alistlist-p)
   (initst-alist svex-alist-p)))

(define svtv-spec-pipe-env->phase-envs ((x svtv-spec-p) (pipe-env svex-env-p))
  :returns (phase-envs svex-envlist-p)
  (b* (((svtv-spec x))
       (svtv-fsm-ins (svex-alistlist-eval x.in-alists pipe-env))
       (svtv-fsm-tests (svex-alistlist-eval x.override-test-alists pipe-env))
       (svtv-fsm-vals (svex-alistlist-eval x.override-val-alists pipe-env))
       (cycle-ins (svtv-fsm-to-base-fsm-inputs
                   (take (len (svtv-probealist-outvars x.probes))
                         svtv-fsm-ins)
                   svtv-fsm-vals svtv-fsm-tests x.namemap)))
    (svtv-cycle-run-fsm-inputs cycle-ins x.cycle-phases))

  ///
  (defret len-of-<fn>
    (equal (len phase-envs)
           (b* (((svtv-spec x)))
             (* (len x.cycle-phases)
                (len (svtv-probealist-outvars x.probes)))))))

(define svtv-spec-phase-outs->pipe-out ((x svtv-spec-p)
                                        (phase-outs svex-envlist-p))
  :returns (pipe-out svex-env-p)
  :guard (svtv-cyclephaselist-has-outputs-captured (svtv-spec->cycle-phases x))
  (b* (((svtv-spec x))
       (cycle-outs (svex-envlist-phase-outputs-extract-cycle-outputs
                    x.cycle-phases phase-outs))
       (svtv-fsm-outs (svtv-name-lhs-map-eval-list x.namemap cycle-outs)))
    (svtv-probealist-extract x.probes svtv-fsm-outs)))

(define svtv-spec-run ((x svtv-spec-p)
                       (pipe-env svex-env-p)
                       &key
                       (base-ins svex-envlist-p)
                       (initst svex-env-p))
  :returns (pipe-out svex-env-p)
  :guard (and (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm x)))))
              (equal (svex-alist-keys (svtv-spec->initst-alist x))
                     (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm x))))
              (svtv-cyclephaselist-has-outputs-captured (svtv-spec->cycle-phases x)))
  (b* (((svtv-spec x))
       (phase-ins (svtv-spec-pipe-env->phase-envs x pipe-env))
       (full-ins (svex-envlist-x-override phase-ins base-ins))
       (full-initst (svex-env-x-override (svex-alist-eval x.initst-alist pipe-env) initst))
       (phase-outs (mbe :logic (base-fsm-eval full-ins full-initst x.fsm)
                        :exec (base-fsm-eval full-ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x.fsm)) full-initst)
                                             x.fsm))))
    (svtv-spec-phase-outs->pipe-out x phase-outs)))
