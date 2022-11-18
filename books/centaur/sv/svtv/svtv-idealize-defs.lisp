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

(defxdoc svtv-idealize-internals
  :short "Umbrella topic for internal concepts used in the proofs for the svtv-idealize framework."
  :parents (svtv-idealize))


;; (define 4vec-override-values-ok-<<= ((test 4vec-p)
;;                                      (val 4vec-p)
;;                                      (ref 4vec-p))
;;   (4vec-<<= (4vec-bit?! test val 0)
;;             (4vec-bit?! test ref 0))
;;   ///
;;   (defthm 4vec-override-values-ok-<<=-of-x-val
;;     (equal (4vec-override-values-ok-<<= test (4vec-x) ref)
;;            t)
;;     :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=))))

;;   (defthm 4vec-override-values-ok-<<=-of-x-test
;;     (equal (4vec-override-values-ok-<<= (4vec-x) val ref)
;;            t)
;;     :hints(("Goal" :in-theory (enable 4vec-override-values-ok-<<=))))

;;   (defthm 4vec-override-values-ok-of-greater-ref
;;     (implies (and (4vec-override-values-ok-<<= test val ref1)
;;                   (4vec-<<= ref1 ref2))
;;              (4vec-override-values-ok-<<= test val ref2))
;;     :hints(("Goal" :in-theory (enable 4vec-<<=-transitive-1)))))



(define svtv-override-triple-mux-<<= ((triple svtv-override-triple-p)
                                      (pipe-env svex-env-p)
                                      (spec-env svex-env-p)
                                      (spec-run svex-env-p))
  :returns (ok)
  (b* (((svtv-override-triple triple)))
    (4vec-override-mux-<<= (svex-eval triple.test pipe-env)
                           (svex-eval triple.val pipe-env)
                           (svex-eval triple.test spec-env)
                           (svex-eval triple.val spec-env)
                           (svex-env-lookup triple.refvar spec-run)))
  ///
  ;; (defthm 4vec-override-mux-<<=-when-spec-ref-<<=
  ;;   (implies (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref1)
  ;;                 (4vec-<<= spec-ref1 spec-ref2))
  ;;            (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref2))
  ;;   :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=
  ;;                                     4vec-bit?!
  ;;                                     4vec-<<=))))
  (defthm svtv-override-triple-mux-<<=-when-<<=
    (implies (and (svtv-override-triple-mux-<<= triple pipe-env spec-env spec-run1)
                  (svex-env-<<= spec-run1 spec-run2))
             (svtv-override-triple-mux-<<= triple pipe-env spec-env spec-run2))))

(define svtv-override-triplemap-muxes-<<= ((triplemap svtv-override-triplemap-p)
                                           (pipe-env svex-env-p)
                                           (spec-env svex-env-p)
                                           (spec-run svex-env-p))
  :returns (ok)
  (if (atom triplemap)
      t
    (and (or (not (mbt (and (consp (car triplemap))
                            (svar-p (caar triplemap)))))
             (svtv-override-triple-mux-<<= (cdar triplemap) pipe-env spec-env spec-run))
         (svtv-override-triplemap-muxes-<<= (cdr triplemap) pipe-env spec-env spec-run)))
  ///
  (defret svtv-override-triple-mux-<<=-of-lookup-when-<fn>
    (implies (and ok
                  (hons-assoc-equal key triplemap)
                  (svar-p key))
             (svtv-override-triple-mux-<<= (cdr (hons-assoc-equal key triplemap))
                                           pipe-env spec-env spec-run)))

  (defthm svtv-override-triplemap-muxes-<<=-when-<<=
    (implies (and (svtv-override-triplemap-muxes-<<= triplemaps pipe-env spec-env spec-run1)
                  (svex-env-<<= spec-run1 spec-run2))
             (svtv-override-triplemap-muxes-<<= triplemaps pipe-env spec-env spec-run2)))
  
  (local (in-theory (enable svtv-override-triple-mux-<<=)))
  (defcong svex-envs-similar equal (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env) 2)
  (defcong svex-envs-similar equal (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env) 3)
  (defcong svex-envs-similar equal (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env) 4)
  (local (in-theory (e/d (svtv-override-triplemap-fix) (svtv-override-triple-mux-<<=)))))


(define svtv-override-triplemaplist-muxes-<<= ((triplemaps svtv-override-triplemaplist-p)
                                               (pipe-env svex-env-p)
                                               (spec-env svex-env-p)
                                               (spec-run svex-env-p))
  :returns (ok)
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-muxes-<<= (car triplemaps) pipe-env spec-env spec-run)
         (svtv-override-triplemaplist-muxes-<<= (cdr triplemaps) pipe-env spec-env spec-run)))
  ///

  (defthm svtv-override-triplemaplist-muxes-<<=-when-<<=
    (implies (and (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-env spec-run1)
                  (svex-env-<<= spec-run1 spec-run2))
             (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-env spec-run2)))

  (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env ref-env) 2)
  (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env ref-env) 3)
  (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env ref-env) 4))

(define svtv-override-triplemap->tests ((triplemap svtv-override-triplemap-p))
  :returns (tests svexlist-p)
  (if (atom triplemap)
      nil
    (if (mbt (and (consp (car triplemap))
                  (svar-p (caar triplemap))))
        (cons (svtv-override-triple->test (cdar triplemap))
              (svtv-override-triplemap->tests (cdr triplemap)))
      (svtv-override-triplemap->tests (cdr triplemap))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svex-envs-svexlist-muxtests-subsetp ((tests svexlist-p)
                                             (spec-env svex-env-p)
                                             (impl-env svex-env-p))
  :returns (ok)
  (if (atom tests)
      t
    (and (4vec-muxtest-subsetp (svex-eval (car tests) spec-env)
                               (svex-eval (car tests) impl-env))
         (svex-envs-svexlist-muxtests-subsetp (cdr tests) spec-env impl-env)))
  ///
  (defret <fn>-implies-4vec-muxtest-subsetp-when-member-tests
    (implies (and ok
                  (member-equal (svex-fix test) (Svexlist-fix tests)))
             (4vec-muxtest-subsetp (svex-eval test spec-env)
                                   (svex-eval test impl-env)))
    :hints(("Goal" :in-theory (enable svexlist-fix))))

  (defcong svex-envs-similar equal (svex-envs-svexlist-muxtests-subsetp tests spec-env impl-env) 2)
  (defcong svex-envs-similar equal (svex-envs-svexlist-muxtests-subsetp tests spec-env impl-env) 3))

(define svtv-override-triplemaplist-muxtests-subsetp ((triplemaps svtv-override-triplemaplist-p)
                                                      (spec-env svex-env-p)
                                                      (impl-env svex-env-p))
  (if (atom triplemaps)
      t
    (and (svex-envs-svexlist-muxtests-subsetp (svtv-override-triplemap->tests (car triplemaps))
                                              spec-env impl-env)
         (svtv-override-triplemaplist-muxtests-subsetp (cdr triplemaps) spec-env impl-env)))
  ///
  (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-env impl-env) 2)
  (defcong svex-envs-similar equal (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-env impl-env) 3))





;; (define svtv-override-triple-ok ((triple svtv-override-triple-p)
;;                                  (pipe-env svex-env-p)
;;                                  (ref-env svex-env-p))
;;   :returns (ok)
;;   (b* (((svtv-override-triple triple)))
;;     (4vec-override-values-ok-<<= (svex-eval triple.test pipe-env)
;;                                  (svex-eval triple.val pipe-env)
;;                                  (svex-env-lookup triple.refvar ref-env)))
;;   ///
;;   (defthm svtv-override-triple-ok-when-<<=
;;     (implies (and (svtv-override-triple-ok triple pipe-env ref-env1)
;;                   (svex-env-<<= ref-env1 ref-env2))
;;              (svtv-override-triple-ok triple pipe-env ref-env2))))

;; (define svtv-override-triplemap-ok ((triplemap svtv-override-triplemap-p)
;;                                     (pipe-env svex-env-p)
;;                                     (ref-env svex-env-p))
;;   :returns (ok)
;;   (if (atom triplemap)
;;       t
;;     (and (or (not (mbt (and (consp (car triplemap))
;;                             (svar-p (caar triplemap)))))
;;              (svtv-override-triple-ok (cdar triplemap) pipe-env ref-env))
;;          (svtv-override-triplemap-ok (cdr triplemap) pipe-env ref-env)))
;;   ///
;;   (defret svtv-override-triple-ok-of-lookup-when-<fn>
;;     (implies (and ok
;;                   (hons-assoc-equal key triplemap)
;;                   (svar-p key))
;;              (svtv-override-triple-ok (cdr (hons-assoc-equal key triplemap))
;;                                       pipe-env ref-env)))

;;   (defthm svtv-override-triplemap-ok-when-<<=
;;     (implies (and (svtv-override-triplemap-ok triplemaps pipe-env ref-env1)
;;                   (svex-env-<<= ref-env1 ref-env2))
;;              (svtv-override-triplemap-ok triplemaps pipe-env ref-env2)))
  
;;   (local (in-theory (enable svtv-override-triplemap-fix))))
                  
                  




(define svtv-override-triplemap-key-check ((key svar-p)
                                        (phase natp)
                                        (test-alist svex-alist-p)
                                        (val-alist svex-alist-p)
                                        (probes svtv-probealist-p)
                                        (triplemap svtv-override-triplemap-p))
  :short "Checks that the given key either isn't bound the test alist, or else
has a triple in the triplemap such that the test of the triple is the key's
binding in the test-alist, the val of the triple is the key's binding in the
val-alist, and the refvar of the triple is bound in probes to a probe whose
signal is the key and time is the current phase."
  :parents (svtv-idealize-internals)
  :returns (ok)
  (b* ((test (svex-fastlookup key test-alist))
       ((unless test) t)
       (val (or (svex-fastlookup key val-alist) (svex-x)))
       ;; ((unless val) t)
       (triple (cdr (hons-get (svar-fix key) (svtv-override-triplemap-fix triplemap))))
       ((unless triple)
        nil)
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
  
  ;; (defret <fn>-implies
  ;;   (implies (and ok
  ;;                 (svtv-override-triple-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
  ;;                                          pipe-env
  ;;                                          (svtv-probealist-extract probes ref-envs)))
  ;;            (4vec-override-values-ok-<<=
  ;;             (svex-eval (svex-lookup key test-alist) pipe-env)
  ;;             (svex-eval (svex-lookup key val-alist) pipe-env)
  ;;             (svex-env-lookup key (nth phase ref-envs))))
  ;;   :hints(("Goal" :in-theory (enable svtv-override-triple-ok))))

  (local (defthm 4vec-override-mux-<<=-when-impl-test-x
           (4vec-override-mux-<<= (4vec-x) impl-val spec-test spec-val spec-ref)
           :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=)))))

  (local (defthm 4vec-override-mux-<<=-when-impl-val-x
           (4vec-override-mux-<<= impl-test (4vec-x) spec-test spec-val spec-ref)
           :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=)))))
  
  (defret <fn>-implies-4vec-override-mux-<<=
    (implies (and ok
                  (svtv-override-triple-mux-<<= (cdr (hons-assoc-equal (svar-fix key) triplemap))
                                                pipe-env spec-env
                                                (svtv-probealist-extract probes ref-envs)))
             (4vec-override-mux-<<=
              (svex-eval (svex-lookup key test-alist) pipe-env)
              (svex-eval (svex-lookup key val-alist) pipe-env)
              (svex-eval (svex-lookup key test-alist) spec-env)
              (svex-eval (svex-lookup key val-alist) spec-env)
              (svex-env-lookup key (nth phase ref-envs))))
    :hints(("Goal" :in-theory (enable svtv-override-triple-mux-<<=))))


  ;; (defret <fn>-implies-4vec-muxtest-subsetp
  ;;   (implies (and ok
  ;;                 (svtv-override-triple-mux-<<= (cdr (hons-assoc-equal (svar-fix key) triplemap))
  ;;                                               pipe-env spec-env
  ;;                                               (svtv-probealist-extract probes ref-envs)))
  ;;            (4vec-muxtest-subsetp
  ;;             (svex-eval (svex-lookup key test-alist) spec-env)
  ;;             (svex-eval (svex-lookup key test-alist) pipe-env)))
  ;;   :hints(("Goal" :in-theory (enable svtv-override-triple-mux-<<=))))

  (local (defthm member-triplemap-tests-when-lookup-lemma
           (implies (and (hons-assoc-equal key triplemap)
                         (svar-p key))
                    (member-equal (svtv-override-triple->test (cdr (hons-assoc-equal key triplemap)))
                                  (svtv-override-triplemap->tests triplemap)))
           :hints(("Goal" :in-theory (enable svtv-override-triplemap->tests)))))

  (local (defthm member-triplemap-tests-when-lookup
           (implies (and (equal val (svtv-override-triple->test (cdr (hons-assoc-equal key triplemap))))
                         (hons-assoc-equal key triplemap)
                         (svar-p key))
                    (member-equal val
                                  (svtv-override-triplemap->tests triplemap)))))
           
  
  (defret member-tests-when-<fn>
    (implies (and ok
                  (svex-lookup key test-alist))
             (member-equal (svex-lookup key test-alist)
                           (svtv-override-triplemap->tests triplemap))))
  
  (defretd <fn>-implies-lookup-in-triplemap
    (implies (and ok
                  (case-split (svex-lookup key test-alist))
                  ;; (case-split (svex-lookup key val-alist))
                  )
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




;; (define svtv-override-triplemaplist-ok ((triplemaps svtv-override-triplemaplist-p)
;;                                         (pipe-env svex-env-p)
;;                                         (ref-env svex-env-p))
;;   :returns (ok)
;;   (if (atom triplemaps)
;;       t
;;     (and (svtv-override-triplemap-ok (car triplemaps) pipe-env ref-env)
;;          (svtv-override-triplemaplist-ok (cdr triplemaps) pipe-env ref-env)))
;;   ///

;;   (defthm svtv-override-triplemaplist-ok-when-<<=
;;     (implies (and (svtv-override-triplemaplist-ok triplemaps pipe-env ref-env1)
;;                   (svex-env-<<= ref-env1 ref-env2))
;;              (svtv-override-triplemaplist-ok triplemaps pipe-env ref-env2))))

(define svtv-override-triplemaplist-syntax-check-aux ((phase natp)
                                                      (test-alists svex-alistlist-p)
                                                      (val-alists svex-alistlist-p)
                                                      (probes svtv-probealist-p)
                                                      (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  :measure (len test-alists)
  (if (atom test-alists)
      t
    (and (b* ((test-alist (car test-alists))
              (val-alist (car val-alists))
              (triplemap (car triplemaps))
              ((acl2::with-fast test-alist val-alist triplemap)))
           (svtv-override-triplemap-syntax-check (svex-alist-keys test-alist)
                                                 phase
                                                 test-alist
                                                 val-alist
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
  :guard (non-exec (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                        (svtv-data-obj->flatten-validp x)))
  :guard-hints (("goal" :in-theory (enable design-flatten-okp)))
  (b* (((svtv-data-obj x))
       ((pipeline-setup x.pipeline-setup)))
    (make-svtv-spec :fsm (design->ideal-fsm x.design x.phase-fsm-setup)
                    :cycle-phases x.cycle-phases
                    :namemap x.namemap
                    :probes x.pipeline-setup.probes
                    :in-alists x.pipeline-setup.inputs
                    :override-test-alists x.pipeline-setup.override-tests
                    :override-val-alists x.pipeline-setup.override-vals                    
                    :initst-alist x.pipeline-setup.initst)))



