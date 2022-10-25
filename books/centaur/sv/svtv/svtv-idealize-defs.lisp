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

(include-book "svtv-spec")
(include-book "svtv-fsm-ideal")
(include-book "svtv-data-obj-spec")
(include-book "override-common")

(local (std::add-default-post-define-hook :fix))

(define 4vec-override-values-ok-<<= ((test 4vec-p)
                                     (val 4vec-p)
                                     (ref 4vec-p))
  (4vec-<<= (4vec-bit?! test val 0)
            (4vec-bit?! test ref 0))
  ///
  (defthm 4vec-override-values-ok-<<=-of-x-val
    (equal (4vec-override-values-ok-<<= test (4vec-x) ref)
           t)
    :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=))))

  (defthm 4vec-override-values-ok-<<=-of-x-test
    (equal (4vec-override-values-ok-<<= (4vec-x) val ref)
           t)
    :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=))))

  (defthm 4vec-override-values-ok-of-greater-ref
    (implies (and (4vec-override-values-ok-<<= test val ref1)
                  (4vec-<<= ref1 ref2))
             (4vec-override-values-ok-<<= test val ref2))
    :hints(("Goal" :in-theory (enable 4vec-<<=-transitive-1)))))






(define svtv-override-triple-ok ((triple svtv-override-triple-p)
                                 (pipe-env svex-env-p)
                                 (ref-env svex-env-p))
  :returns (ok)
  (b* (((svtv-override-triple triple)))
    (4vec-override-values-ok-<<= (svex-eval triple.test pipe-env)
                                 (svex-eval triple.val pipe-env)
                                 (svex-env-lookup triple.refvar ref-env)))
  ///
  (defthm svtv-override-triple-ok-when-<<=
    (implies (and (svtv-override-triple-ok triple pipe-env ref-env1)
                  (svex-env-<<= ref-env1 ref-env2))
             (svtv-override-triple-ok triple pipe-env ref-env2))))

(define svtv-override-triplemap-ok ((triplemap svtv-override-triplemap-p)
                                    (pipe-env svex-env-p)
                                    (ref-env svex-env-p))
  :returns (ok)
  (if (atom triplemap)
      t
    (and (or (not (mbt (and (consp (car triplemap))
                            (svar-p (caar triplemap)))))
             (svtv-override-triple-ok (cdar triplemap) pipe-env ref-env))
         (svtv-override-triplemap-ok (cdr triplemap) pipe-env ref-env)))
  ///
  (defret svtv-override-triple-ok-of-lookup-when-<fn>
    (implies (and ok
                  (hons-assoc-equal key triplemap)
                  (svar-p key))
             (svtv-override-triple-ok (cdr (hons-assoc-equal key triplemap))
                                      pipe-env ref-env)))

  (defthm svtv-override-triplemap-ok-when-<<=
    (implies (and (svtv-override-triplemap-ok triplemaps pipe-env ref-env1)
                  (svex-env-<<= ref-env1 ref-env2))
             (svtv-override-triplemap-ok triplemaps pipe-env ref-env2)))
  
  (local (in-theory (enable svtv-override-triplemap-fix))))
                  
                  
        


(define svtv-override-triplemap-key-check ((key svar-p)
                                        (phase natp)
                                        (test-alist svex-alist-p)
                                        (val-alist svex-alist-p)
                                        (probes svtv-probealist-p)
                                        (triplemap svtv-override-triplemap-p))
  :returns (ok)
  (b* ((test (svex-fastlookup key test-alist))
       ((unless test) t)
       (val (svex-fastlookup key val-alist))
       ((unless val) t)
       (triple (cdr (hons-get (svar-fix key) (svtv-override-triplemap-fix triplemap))))
       ((unless triple) nil)
       ((svtv-override-triple triple))
       ((unless (and (equal triple.test test)
                     (equal triple.val val)))
        nil)
       (probe (cdr (hons-get triple.refvar (svtv-probealist-fix probes))))
       ((unless probe) nil)
       ((svtv-probe probe)))
    (and (equal probe.signal (svar-fix key))
         (equal probe.time (lnfix phase))))
  ///

  ;; (local (defthm equal-of-svar-fix
  ;;          (implies (equal x (svar-fix y))
  ;;                   (svar-equiv x y))
  ;;          :rule-classes :forward-chaining))
  ;; (local (defthm equal-of-svar-fix
  ;;          (implies (equal x (svar-fix y))
  ;;                   (svar-equiv x y))
  ;;          :rule-classes :forward-chaining))
  
  (defret <fn>-implies
    (implies (and ok
                  (svtv-override-triple-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
                                           pipe-env
                                           (svtv-probealist-extract probes ref-envs)))
             (4vec-override-values-ok-<<=
              (svex-eval (svex-lookup key test-alist) pipe-env)
              (svex-eval (svex-lookup key val-alist) pipe-env)
              (svex-env-lookup key (nth phase ref-envs))))
    :hints(("Goal" :in-theory (enable svtv-override-triple-ok))))

  (defretd <fn>-implies-lookup-in-triplemap
    (implies (and ok
                  (case-split (svex-lookup key test-alist))
                  (case-split (svex-lookup key val-alist)))
             (hons-assoc-equal (svar-fix key) triplemap))))
              
         


(define svtv-override-triplemap-syntax-check ((keys svarlist-p)
                                          (phase natp)
                                          (test-alist svex-alist-p)
                                          (val-alist svex-alist-p)
                                          (probes svtv-probealist-p)
                                          (triplemap svtv-override-triplemap-p))
  :returns (ok)
  (if (atom keys)
      t
    (and (svtv-override-triplemap-key-check (car keys) phase test-alist val-alist probes triplemap)
         (svtv-override-triplemap-syntax-check (cdr keys) phase test-alist val-alist probes triplemap))))




(define svtv-override-triplemaplist-ok ((triplemaps svtv-override-triplemaplist-p)
                                        (pipe-env svex-env-p)
                                        (ref-env svex-env-p))
  :returns (ok)
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-ok (car triplemaps) pipe-env ref-env)
         (svtv-override-triplemaplist-ok (cdr triplemaps) pipe-env ref-env)))
  ///

  (defthm svtv-override-triplemaplist-ok-when-<<=
    (implies (and (svtv-override-triplemaplist-ok triplemaps pipe-env ref-env1)
                  (svex-env-<<= ref-env1 ref-env2))
             (svtv-override-triplemaplist-ok triplemaps pipe-env ref-env2))))

(define svtv-override-triplemaplist-syntax-check-aux ((phase natp)
                                              (test-alists svex-alistlist-p)
                                              (val-alists svex-alistlist-p)
                                              (probes svtv-probealist-p)
                                              (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  :measure (len val-alists)
  (if (atom val-alists)
      t
    (and (b* ((test-alist (car test-alists))
              (val-alist (car val-alists))
              (triplemap (car triplemaps))
              ((acl2::with-fast test-alist val-alist triplemap)))
           (svtv-override-triplemap-syntax-check (svex-alist-keys (car val-alists))
                                                 phase
                                                 (car test-alists)
                                                 (car val-alists)
                                                 probes
                                                 (car triplemaps)))
         (svtv-override-triplemaplist-syntax-check-aux (1+ (lnfix phase))
                                                   (cdr test-alists)
                                                   (cdr val-alists)
                                                   probes
                                                   (cdr triplemaps)))))


(define svtv-override-triplemaplist-syntax-check ((test-alists svex-alistlist-p)
                                                  (val-alists svex-alistlist-p)
                                                  (probes svtv-probealist-p)
                                                  (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  (acl2::with-fast-alist probes
    (svtv-override-triplemaplist-syntax-check-aux 0 test-alists val-alists probes triplemaps)))


;; now, we need to show how to find a triplemaplist that satisfies the syntactic check above.


;; REDUNDANT with svtv-fsm-override
(fty::defmap svtv-rev-probealist :key-type svtv-probe :val-type svar :true-listp t)

(define svtv-construct-triplemap ((keys svarlist-p)
                                  (phase natp)
                                  (test-alist svex-alist-p)
                                  (val-alist svex-alist-p)
                                  (rev-probes svtv-rev-probealist-p))
  :returns (triplemap svtv-override-triplemap-p)
  (b* (((when (atom keys)) nil)
       (key (svar-fix (car keys)))
       (test (svex-fastlookup key test-alist))
       (val (svex-fastlookup key val-alist))
       ((unless (and test val))
        (svtv-construct-triplemap (cdr keys) phase test-alist val-alist rev-probes))
       (probevar-look (hons-get (make-svtv-probe :signal key :time phase)
                                (svtv-rev-probealist-fix rev-probes)))
       ((unless probevar-look)
        (raise "No output for signal ~s0 at time ~x1 -- needed for override mappings"
               key phase)
        (svtv-construct-triplemap (cdr keys) phase test-alist val-alist rev-probes)))
    (cons (cons key (make-svtv-override-triple
                     :test test
                     :val val
                     :refvar (cdr probevar-look)))
          (svtv-construct-triplemap (cdr keys) phase test-alist val-alist rev-probes))))

(define svtv-construct-triplemaplist-aux ((phase natp)
                                          (test-alists svex-alistlist-p)
                                          (val-alists svex-alistlist-p)
                                          (rev-probes svtv-rev-probealist-p))
  :returns (triplemaplist svtv-override-triplemaplist-p)
  (if (atom val-alists)
      nil
    (cons (b* ((test-alist (car test-alists))
               (val-alist (car val-alists))
               ((acl2::with-fast test-alist val-alist)))
            (svtv-construct-triplemap (svex-alist-keys val-alist) phase test-alist val-alist rev-probes))
          (svtv-construct-triplemaplist-aux (1+ (lnfix phase))
                                            (cdr test-alists)
                                            (cdr val-alists)
                                            rev-probes))))

(define svtv-construct-triplemaplist ((test-alists svex-alistlist-p)
                                      (val-alists svex-alistlist-p)
                                      (probes svtv-probealist-p))
  :returns (triplemaplist svtv-override-triplemaplist-p)
  :prepwork
  ((local (defthm svtv-rev-probealist-p-of-pair-vals-keys
            (implies (svtv-probealist-p x)
                     (svtv-rev-probealist-p (pairlis$ (alist-vals x) (alist-keys x))))
            :hints(("Goal" :in-theory (enable svtv-rev-probealist-p svtv-probealist-p pairlis$ alist-keys alist-vals))))))
  (b* ((probes (svtv-probealist-fix probes))
       (rev-probes (make-fast-alist (pairlis$ (alist-vals probes) (alist-keys probes))))
       (triplemaplist (svtv-construct-triplemaplist-aux 0 test-alists val-alists rev-probes)))
    (fast-alist-free rev-probes)
    triplemaplist))


(define svtv-cyclephaselist-keys ((x svtv-cyclephaselist-p))
  (if (atom x)
      nil
    (append (alist-keys (svtv-cyclephase->constants (car x)))
            (svtv-cyclephaselist-keys (cdr x)))))


(define svtv-cyclephaselist-no-i/o-phase ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      t
    (and (b* (((svtv-cyclephase ph1) (car phases)))
           (and (not ph1.inputs-free)
                (not ph1.outputs-captured)))
         (svtv-cyclephaselist-no-i/o-phase (cdr phases)))))

(define svtv-cyclephaselist-unique-i/o-phase ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      nil
    (b* (((svtv-cyclephase ph1) (car phases)))
      (or (and (not ph1.inputs-free)
               (not ph1.outputs-captured)
               (svtv-cyclephaselist-unique-i/o-phase (cdr phases)))
          (and ph1.inputs-free
               ph1.outputs-captured
               (svtv-cyclephaselist-no-i/o-phase (cdr phases)))))))


(define svex-alist-keys-list ((x svex-alistlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-alist-keys (car x))
          (svex-alist-keys-list (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len keys)
           (len x))))


(define svex-env-keys-list ((x svex-envlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (alist-keys (svex-env-fix (car x)))
          (svex-env-keys-list (cdr x))))
  ///
  (defthm svex-env-keys-list-of-svex-alistlist-eval
    (equal (svex-env-keys-list (svex-alistlist-eval x env))
           (svex-alist-keys-list x))
    :hints(("Goal" :in-theory (enable svex-alist-keys-list
                                      svex-alistlist-eval)))))

(local (in-theory (disable hons-dups-p)))

(define no-duplicatesp-each (x)
  (if (atom x)
      t
    (and (mbe :logic (no-duplicatesp-equal (car x))
              :exec (not (hons-dups-p (car x))))
         (no-duplicatesp-each (cdr x))))
  ///
  (defthm no-duplicatesp-each-of-take
    (implies (no-duplicatesp-each x)
             (no-duplicatesp-each (take n x)))
    :hints(("Goal" :in-theory (disable acl2::take-of-too-many acl2::take-when-atom)))))


(fty::deflist svtv-name-lhs-map-list :elt-type svtv-name-lhs-map :true-listp t)

(defthm svarlist-p-alist-keys-of-svtv-name-lhs-map-fix
  (svarlist-p (alist-keys (svtv-name-lhs-map-fix x)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix alist-keys))))

(define svtv-name-lhs-map-list-all-keys ((x svtv-name-lhs-map-list-p))
  :returns (keys svarlist-p)
  (if (atom x)
      nil
    (append (alist-keys (svtv-name-lhs-map-fix (car x)))
            (svtv-name-lhs-map-list-all-keys (cdr x)))))

(define svtv-name-lhs-map-inverse-list ((x svtv-name-lhs-map-list-p))
  :returns (invlist svtv-name-lhs-map-list-p)
  (if (atom x)
      nil
    (cons (b* (((mv ?collision inverse)
                (svtv-name-lhs-map-inverse (car x))))
            inverse)
          (svtv-name-lhs-map-inverse-list (cdr x)))))

(define svtv-name-lhs-map-extract-list ((keyslist svarlist-list-p)
                                        (x svtv-name-lhs-map-p))
  :returns (maplist svtv-name-lhs-map-list-p)
  (if (atom keyslist)
      nil
    (cons (acl2::fal-extract (Svarlist-fix (car keyslist)) (svtv-name-lhs-map-fix x))
          (svtv-name-lhs-map-extract-list (cdr keyslist) x))))

(define svtv-data-obj->ideal-spec ((x svtv-data-obj-p))
  :returns (spec svtv-spec-p)
  :non-executable t
  :guard (non-exec (svtv-data$ap (svtv-data-obj-to-stobj-logic x)))
  (b* (((svtv-data-obj x))
       ((pipeline-setup x.pipeline-setup)))
    (make-svtv-spec :fsm (design->ideal-fsm x.design)
                    :cycle-phases x.cycle-phases
                    :namemap x.namemap
                    :probes x.pipeline-setup.probes
                    :in-alists x.pipeline-setup.inputs
                    :initst-alist x.pipeline-setup.initst)))


