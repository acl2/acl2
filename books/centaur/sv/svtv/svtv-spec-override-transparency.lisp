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

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(include-book "svtv-spec")
(include-book "override-common")
(include-book "override-envlist-defs")
(include-book "fsm-override-transparency")
(include-book "svtv-generalize-defs")

(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/alists/fal-extract" :dir :system))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/alists/alist-equiv" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "centaur/misc/hons-sets" :dir :system))
  
(local (in-theory (disable mod floor ceiling)))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))


(defcong svex-envlists-similar svex-envlists-similar (svtv-name-lhs-map-eval-list map envs) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))






(local (defthm subsetp-equal-lhs-vars-of-svtv-name-lhs-map-lookup
         (implies (and (hons-assoc-equal key namemap)
                       (svar-p key))
                  (subsetp-equal (lhs-vars (cdr (hons-assoc-equal key namemap)))
                                 (svtv-name-lhs-map-vars namemap)))
         :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars alist-keys)))))

(local (defthm subsetp-svtv-name-lhs-map-vars-of-fal-extract
         (subsetp-equal (svtv-name-lhs-map-vars (fal-extract keys (svtv-name-lhs-map-fix namemap)))
                        (svtv-name-lhs-map-vars namemap))
         :hints(("Goal" :in-theory (enable fal-extract svtv-name-lhs-map-vars)
                 :induct (len keys)))))


(local (in-theory (disable acl2::hons-subset)))

(defsection svtv-override-triplemap-overridekeys-ok
  (local (in-theory (enable svtv-override-triplemap-overridekeys-ok)))
  (local (std::set-define-current-function svtv-override-triplemap-overridekeys-ok))
  
  (local (defthm svtv-override-triplemap-overridekeys-ok-implies-subsetp-lookup
           (implies (and (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                         (svtv-override-triple->refvar
                          (cdr (hons-assoc-equal key triplemap)))
                         (svar-p key))
                    (subsetp-equal (lhs-vars (cdr (hons-assoc-equal key namemap)))
                                   (svarlist-change-override overridekeys nil)))
           :hints(("Goal" :in-theory (e/d (svtv-override-triplemap-overridekeys-ok
                                           svtv-override-triplemap-refvar-keys
                                           fal-extract
                                           svtv-name-lhs-map-vars)
                                          (acl2::hons-assoc-equal-iff-member-alist-keys))))))

  (local (defthm lhs-var/idx-find-implies-member-lhs-vars
           (implies (lhs-var/idx-find var idx x)
                    (member-equal (svar-fix var) (lhs-vars x)))
           :hints(("Goal" :in-theory (enable lhs-var/idx-find lhs-vars lhatom-vars)))))

  (local (defthm hons-assoc-eq
           (implies (lhs-var/idx-find var idx x)
                    (member-equal (svar-fix var) (lhs-vars x)))
           :hints(("Goal" :in-theory (enable lhs-var/idx-find lhs-vars lhatom-vars)))))
  
  (local (defthm suffixp-of-cdr
           (implies (and (acl2::suffixp x y)
                         (consp x))
                    (acl2::suffixp (cdr x) y))
           :hints(("Goal" :in-theory (enable acl2::suffixp)))))

  (local (defthm member-alist-keys-when-svtv-name-lhs-map-var-/idx-find
           (implies (equal (lhbit-kind (svtv-name-lhs-map-var/idx-find v badbit namemap)) :var)
                    (member-equal (lhbit-var->name (svtv-name-lhs-map-var/idx-find v badbit namemap))
                                  (alist-keys (svtv-name-lhs-map-fix namemap))))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-var/idx-find)))))
  

  (local (defthm member-lhs-vars-of-svtv-name-lhs-map-var/idx-find
           (implies (and (equal (lhbit-kind (SVTV-NAME-LHS-MAP-VAR/IDX-FIND v BADBIT NAMEMAP)) :var)
                         (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap))))
                    (member-equal (svar-fix v) (lhs-vars (cdr (hons-assoc-equal
                                                               (LHBIT-VAR->NAME (SVTV-NAME-LHS-MAP-VAR/IDX-FIND V BADBIT NAMEMAP))
                                                               namemap)))))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-var/idx-find
                                             svtv-name-lhs-map-fix
                                             alist-keys)))))
  
  (defthm svtv-override-triplemap-overridekeys-ok-implies-no-refvar-when-not-member-overridekeys
    (implies (and (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                  (not (member-equal (svar-fix v) (svarlist-change-override overridekeys nil)))
                  (svar-override-p v nil)
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (equal (lhbit-kind (SVTV-NAME-LHS-MAP-VAR/IDX-FIND v BADBIT NAMEMAP)) :var))
             (not (SVTV-OVERRIDE-TRIPLE->REFVAR
                   (CDR
                    (HONS-ASSOC-EQUAL
                     (LHBIT-VAR->NAME
                      (SVTV-NAME-LHS-MAP-VAR/IDX-FIND v BADBIT NAMEMAP))
                     TRIPLEMAP)))))
    :hints (("goal" :use ((:instance svtv-override-triplemap-overridekeys-ok-implies-subsetp-lookup
                           (key (LHBIT-VAR->NAME
                                 (SVTV-NAME-LHS-MAP-VAR/IDX-FIND v BADBIT NAMEMAP))))
                          (:instance member-lhs-vars-of-svtv-name-lhs-map-var/idx-find))
             :do-not-induct t
             :in-theory (disable svtv-override-triplemap-overridekeys-ok-implies-subsetp-lookup
                                 member-lhs-vars-of-svtv-name-lhs-map-var/idx-find))))

  (local (defthm fal-extract-of-fal-extract
           (equal (fal-extract a (fal-extract b x))
                  (fal-extract (intersection-equal a b) x))
           :hints(("Goal" :in-theory (enable fal-extract intersection-equal)))))

  (local (defthm intersection-equal-lemma
           (implies (subsetp-equal a c)
                    (equal (intersection-equal (intersection-equal a b) c)
                           (intersection-equal a b)))
           :hints(("Goal" :in-theory (enable intersection-equal subsetp-equal)))))
  
  (defthm svtv-override-triplemap-overridekeys-ok-of-fal-extract
    (implies (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
             (svtv-override-triplemap-overridekeys-ok triplemap
                                                      (fal-extract keys (svtv-name-lhs-map-fix namemap))
                                                      overridekeys))
    :hints (("goal" :use ((:instance subsetp-svtv-name-lhs-map-vars-of-fal-extract
                           (keys (intersection-equal (SVTV-OVERRIDE-TRIPLEMAP-REFVAR-KEYS TRIPLEMAP) keys))
                           (namemap (fal-extract (SVTV-OVERRIDE-TRIPLEMAP-REFVAR-KEYS TRIPLEMAP)
                                                 (svtv-name-lhs-map-fix namemap)))))
             :in-theory (e/d () (subsetp-svtv-name-lhs-map-vars-of-fal-extract))))))
  ;; ///
  ;; (implies
  ;;  (member-equal (svar-change-override v nil)

  ;;  (HONS-ASSOC-EQUAL
  ;;         (LHBIT-VAR->NAME (SVTV-NAME-LHS-MAP-VAR/IDX-FIND V BADBIT NAMEMAP))
  ;;         TRIPLEMAP))


(local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))
(local (in-theory (enable acl2::hons-assoc-equal-iff-member-alist-keys)))


(defthm alist-keys-of-svtv-hame-lhs-map-keys-change-override
  (equal (alist-keys (svtv-name-lhs-map-keys-change-override x type))
         (svarlist-change-override (alist-keys (svtv-name-lhs-map-fix x)) type))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                    svtv-name-lhs-map-keys-change-override
                                    svarlist-change-override
                                    alist-keys))))

;; Svtv-spec-override-mux has the proof that top-level SVTV inputs pipe-env and
;; spec-env, satisfying svtv-override-triplemaplist-envs-ok, give rise to FSM
;; inputs satisfying all the necessary conditions, such as muxes-<<=.  We want
;; to replicate this with the goal of showing that the FSM input envs satisfy
;; overridekeys-envlist-ok.

;; svtv-override-triplemaplist-muxes-<<=-of-spec-outs-implies-svar-override-keys-check-separate-override-envlists-of-spec-ins
;; expresses its conclusion (initially
;; svar-override-triplelist-envlists-muxes-<<=) in terms of
;; SVAR-OVERRIDE-RENAMED-KEYS-CHECK-SEPARATE-ENVLISTS-MUXES-<<=.  Somewhere in
;; there it also works through the cycles, leaving just the evaluation of
;; inverse extracted lhs-maps on in/val/test alist evaluations, and reworking
;; the inverse namemap extractions so they're all the same (those of the test
;; keys).  This then in turn uses
;; SVEX-SEPARATE-ENVLISTS-OVERRIDE-MUXES-<<=-IMPLIES-SVAR-OVERRIDE-KEYS-CHECK-SEPARATE-ENVLISTS-DOUBLE-RW
;; to express this in terms of SVEX-SEPARATE-ENVLISTS-OVERRIDE-MUXES-<<=.

;; This is proved using
;; svex-separate-envlists-override-muxes-<<=-of-eval-inverse.  This seems to be
;; the crux -- it shows that if the evaluations of the inverse namemap on
;; different envs for impl-tests, impl-vals, spec-tests, spec-vals are muxes-<<
;; with ref-envs, then the envs for impl-tests, impl-vals, etc are muxes-<<=
;; with the lhs-map evaluation of the (non-inverted) namemap on the ref-envs.

;; This then leaves svex-separate-envslists-override-muxes-<<= of the
;; evaluations of the test/val alists on pipe-env/spec-env, and the evaluation
;; of namemap under the phase cycle outputs as the ref-envs.  This is proved by
;; svtv-override-triplemaplist-syntax-check-implies.

;; Do we need all these special functions to do a similar proof here?  Not sure
;; the point in separating out all the envs etc.

;; Our version of the crux ought to be a theorem establishing
;; overridekeys-envlist-ok on the svtv-fsm-to-base-fsm-inputs (single phase
;; version being overridekeys-envs-ok on svtv-fsm-phase-inputs) given
;; syntax-check/svtv-override-triplemap-envs-ok.


(defthm lhs-eval-x-monotonic
  (implies (svex-env-<<= x y)
           (4vec-<<= (lhs-eval-x lhs x) (lhs-eval-x lhs y)))
  :hints(("Goal" :in-theory (enable lhs-eval-x lhatom-eval-x))))


(define 4vec-equiv-badbit ((a 4vec-p) (b 4vec-p))
  :returns (badbit natp :rule-classes :type-prescription)
  (b* (((4vec a))
       ((4vec b))
       (vec (logior (logxor a.upper b.upper)
                    (logxor a.lower b.lower))))
    (bitops::trailing-0-count vec))
  
  ///

  (local (defthmd logbitp-of-trailing-0-count
           (equal (logbitp (bitops::trailing-0-count x) x)
                  (not (zip x)))
           :hints(("Goal" :in-theory (enable bitops::trailing-0-count-properties)))))
  
  (defretd 4vec-equiv-when-badbit
    (implies (and (4vec-p a) (4vec-p b)
                  (equal (4vec-bit-index badbit a) (4vec-bit-index badbit b)))
             (equal (equal a b) t))
    :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-equiv)
            :use ((:instance logbitp-of-trailing-0-count
                   (x (b* (((4vec a))
                           ((4vec b))
                           (vec (logior (logxor a.upper b.upper)
                                        (logxor a.lower b.lower))))
                        vec)))))))
  
  (defretd 4vec-equiv-by-badbit
    (implies (and (acl2::rewriting-positive-literal `(equal ,a ,b))
                  (4vec-p a) (4vec-p b))
             (equal (equal a b)
                    (equal (4vec-bit-index badbit a) (4vec-bit-index badbit b))))
    :hints(("Goal" :in-theory (e/d (4vec-equiv-when-badbit)
                                   (<fn>))
            :restrict ((4vec-equiv-when-badbit
                        ((a a) (b b))))))))

(define 4vec-<<=-badbit ((a 4vec-p) (b 4vec-p))
  :returns (badbit natp :rule-classes :type-prescription)
  :prepwork (  )
  (b* (((4vec a))
       ((4vec b))
       (vec (lognot (logior (logand (logeqv a.upper b.upper)
                                    (logeqv a.lower b.lower))
                            (logand a.upper (lognot a.lower))))))
    (bitops::trailing-0-count vec))
  ///
  (defthmd 4vec-<<=-implies-bit-index
    (implies (and (4vec-<<= x y)
                  (not (equal (4vec-bit-index n x) (4vec-1x))))
             (equal (4vec-bit-index n y) (4vec-bit-index n x)))
    :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-bit-index))
           (bitops::logbitp-reasoning)))

  (local (defthmd logbitp-of-trailing-0-count
           (equal (logbitp (bitops::trailing-0-count x) x)
                  (not (zip x)))
           :hints(("Goal" :in-theory (enable bitops::trailing-0-count-properties)))))
  
  (defretd 4vec-<<=-when-badbit
    (implies (or (equal (4vec-bit-index badbit a) (4vec-1x))
                 (equal (4vec-bit-index badbit a) (4vec-bit-index badbit b)))
             (4vec-<<= a b))
    :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-<<=
                                      4vec-<<=-implies-bit-index)
            :use ((:instance logbitp-of-trailing-0-count
                   (x (b* (((4vec a))
                           ((4vec b))
                           (vec (lognot (logior (logand (logeqv a.upper b.upper)
                                                        (logeqv a.lower b.lower))
                                                (logand a.upper (lognot a.lower))))))
                        vec)))))))
  
  (defretd 4vec-<<=-by-badbit
    (implies (acl2::rewriting-positive-literal `(4vec-<<= ,a ,b))
             (equal (4vec-<<= a b)
                    (or (equal (4vec-bit-index badbit a) (4vec-1x))
                        (equal (4vec-bit-index badbit a) (4vec-bit-index badbit b)))))
    :hints(("Goal" :in-theory (e/d (4vec-<<=-when-badbit
                                    4vec-<<=-implies-bit-index)
                                   (<fn>))))))


(define 4vec-override-mux-<<=-badbit ((impl-test 4vec-p)
                                      (impl-val 4vec-p)
                                      (spec-test 4vec-p)
                                      (spec-val 4vec-p)
                                      (spec-ref 4vec-p))
  :returns (badbit natp :rule-classes :type-prescription)
  (b* ((spec-mux (4vec-bit?! spec-test spec-val spec-ref)))
    (4vec-<<=-badbit (4vec-bit?! impl-test impl-val spec-mux)
              spec-mux))
  ///
  (local (Defthm 4vec-bit-index-of-4vec-bit?!
           (equal (4vec-bit-index n (4vec-bit?! test then else))
                  (if (eql (4vec-bit-index n test) 1)
                      (4vec-bit-index n then)
                    (4vec-bit-index n else)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index
                                             4vec-bit?! 4vec-bitmux 4vec-1mask b-ite)))))

  (defthmd 4vec-override-mux-<<=-implies-bit-index
    (implies (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref)
                  (equal 1 (4vec-bit-index n impl-test))
                  (not (equal (4vec-1x) (4vec-bit-index n impl-val))))
             (equal (4vec-bit-index n impl-val)
                    (if (eql (4vec-bit-index n spec-test) 1)
                        (4vec-bit-index n spec-val)
                      (4vec-bit-index n spec-ref))))
    :hints(("Goal" :in-theory (e/d (4vec-override-mux-<<=)
                                   (4vec-<<=-implies-bit-index))
            :use ((:instance 4vec-<<=-implies-bit-index
                   (x (4vec-bit?! impl-test impl-val (4vec-bit?! spec-test spec-val spec-ref)))
                   (y (4vec-bit?! spec-test spec-val spec-ref)))))))

  (defretd 4vec-override-mux-<<=-when-badbit
    (implies (or (not (equal 1 (4vec-bit-index badbit impl-test)))
                 (equal (4vec-1x) (4vec-bit-index badbit impl-val))
                 (equal (4vec-bit-index badbit impl-val)
                        (if (eql (4vec-bit-index badbit spec-test) 1)
                            (4vec-bit-index badbit spec-val)
                          (4vec-bit-index badbit spec-ref))))
             (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref))
    :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=
                                      4vec-<<=-when-badbit))))

  (defretd 4vec-override-mux-<<=-by-badbit
    (implies (acl2::rewriting-positive-literal `(4vec-override-mux-<<= ,impl-test ,impl-val ,spec-test ,spec-val ,spec-ref))
             (equal (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref)
                    (or (not (equal 1 (4vec-bit-index badbit impl-test)))
                        (equal (4vec-1x) (4vec-bit-index badbit impl-val))
                        (equal (4vec-bit-index badbit impl-val)
                               (if (eql (4vec-bit-index badbit spec-test) 1)
                                   (4vec-bit-index badbit spec-val)
                                 (4vec-bit-index badbit spec-ref))))))
    :hints(("Goal" :in-theory (e/d (4vec-override-mux-<<=-when-badbit
                                    4vec-override-mux-<<=-implies-bit-index)
                                   (<fn>))))))



(define 4vec-muxtest-subsetp-badbit ((a 4vec-p) (b 4vec-p))
  :returns (badbit natp :rule-classes :type-prescription)
  :prepwork (  )
  (bitops::trailing-0-count (logandc2 (4vec-1mask a) (4vec-1mask b)))
  ///
  (defthmd 4vec-muxtest-subsetp-implies-bit-index
    (implies (and (equal (4vec-bit-index n x) 1)
                  (4vec-muxtest-subsetp x y))
             (equal (4vec-bit-index n y) 1))
    :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp 4vec-1mask 4vec-bit-index))
           (bitops::logbitp-reasoning)))

  (local (defthmd logbitp-of-trailing-0-count
           (equal (logbitp (bitops::trailing-0-count x) x)
                  (not (zip x)))
           :hints(("Goal" :in-theory (enable bitops::trailing-0-count-properties)))))
  
  (defretd 4vec-muxtest-subsetp-when-badbit
    (implies (or (not (equal (4vec-bit-index badbit a) 1))
                 (equal (4vec-bit-index badbit b) 1))
             (4vec-muxtest-subsetp a b))
    :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-muxtest-subsetp 4vec-1mask)
            :use ((:instance logbitp-of-trailing-0-count
                   (x (logandc2 (4vec-1mask a) (4vec-1mask b))))))))

  (defretd 4vec-muxtest-subsetp-by-badbit
    (implies (acl2::rewriting-positive-literal `(4vec-muxtest-subsetp ,a ,b))
             (equal (4vec-muxtest-subsetp a b)
                    (or (not (equal (4vec-bit-index badbit a) 1))
                        (equal (4vec-bit-index badbit b) 1))))
    :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp-when-badbit
                                      4vec-muxtest-subsetp-implies-bit-index)))))


(define lhbit-eval-x ((x lhbit-p)
                      (env svex-env-p))
  (lhbit-case x
    :z (4vec-1x)
    :var (4vec-bit-index x.idx (svex-env-lookup x.name env)))
  ///
  (local (defthm 4vec-bit-index-of-4vec-concat
           (implies (natp w)
                    (equal (4vec-bit-index n (4vec-concat (2vec w) x y))
                           (if (< (nfix n) w)
                               (4vec-bit-index n x)
                             (4vec-bit-index (- (nfix n) w) y))))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-concat)))))

  (local (defthm 4vec-bit-index-of-4vec-rsh
           (implies (natp sh)
                    (equal (4vec-bit-index n (4vec-rsh (2vec sh) x))
                           (4vec-bit-index (+ (nfix n) sh) x)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-bit-index-of-x
           (equal (4vec-bit-index n (4vec-x))
                  (4vec-1x))
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))
  
  (defthm 4vec-bit-index-of-lhs-eval-x
    (equal (4vec-bit-index n (lhs-eval-x x env))
           (lhbit-eval-x (lhs-bitproj n x) env))
    :hints(("Goal" :in-theory (enable lhs-eval-x lhs-bitproj lhatom-bitproj lhatom-eval-x)))))


(define lhbit-eval-zero ((x lhbit-p)
                         (env svex-env-p))
  (lhbit-case x
    :z 0
    :var (4vec-bit-index x.idx (svex-env-lookup x.name env)))
  ///
  (local (defthm 4vec-bit-index-of-4vec-concat
           (implies (natp w)
                    (equal (4vec-bit-index n (4vec-concat (2vec w) x y))
                           (if (< (nfix n) w)
                               (4vec-bit-index n x)
                             (4vec-bit-index (- (nfix n) w) y))))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-concat)))))

  (local (defthm 4vec-bit-index-of-4vec-rsh
           (implies (natp sh)
                    (equal (4vec-bit-index n (4vec-rsh (2vec sh) x))
                           (4vec-bit-index (+ (nfix n) sh) x)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-bit-index-of-0
           (equal (4vec-bit-index n 0)
                  0)
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))

  (defthm 4vec-bit-index-of-lhs-eval-zero
    (equal (4vec-bit-index n (lhs-eval-zero x env))
           (lhbit-eval-zero (lhs-bitproj n x) env))
    :hints(("Goal" :in-theory (enable lhs-eval-zero lhs-bitproj lhatom-bitproj lhatom-eval-zero)))))



;; (defthm svtv-name-lhs-map-var/idx-find-of-fal-extract
;;   (implies (and (equal find  (svtv-name-lhs-map-var/idx-find v bit namemap))
;;                 (equal (lhbit-kind find) :var)
;;                 (member-equal (lhbit-var->name find) keys)
;;                 (not (svtv-name-lhs-map-selfcollide-p namemap)))
;;            (Equal (SVTV-NAME-LHS-MAP-VAR/IDX-FIND
;;                    v bit (FAL-EXTRACT keys NAMEMAP))
;;                   find))
;;   :hints(("Goal" :in-theory (enable fal-extract)
;;           :expand ((:free (a b) (svtv-name-lhs-map-var/idx-find v bit (cons a b)))))))

(defthm svex-env-lookup-of-svtv-name-lhs-map-eval
  (equal (svex-env-lookup v (svtv-name-lhs-map-eval namemap env))
         (b* ((look (hons-assoc-equal (svar-fix v) namemap)))
           (if look
               (lhs-eval-zero (cdr look) env)
             (4vec-x))))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval svex-env-lookup))))

(defthm svex-env-boundp-of-svtv-name-lhs-map-eval
  (iff (svex-env-boundp v (svtv-name-lhs-map-eval x env))
       (hons-assoc-equal (svar-fix v) x))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval svex-env-boundp))))

(defthm svtv-name-lhs-map-eval-of-fal-extract
  (implies (svarlist-p vars)
           (equal (svtv-name-lhs-map-eval (fal-extract vars x) env)
                  (svex-env-reduce vars (svtv-name-lhs-map-eval x env))))
  :hints(("Goal" :in-theory (enable svex-env-reduce-redef svtv-name-lhs-map-eval fal-extract svarlist-p))))







(defsection svtv-override-triplemap-envs-ok-of-extract-namemap
  (local
   (defthmd svtv-override-triplemap-envs-ok-implies-svtv-override-triple-envs-ok
     (implies (and (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env spec-outs)
                   (member-equal pair triplemap)
                   (consp pair)
                   (svar-p (car pair)))
              (svtv-override-triple-envs-ok (cdr pair) pipe-env spec-env spec-outs))
     :hints(("Goal" :in-theory (enable svtv-override-triplemap-envs-ok)))))

  (local (defthmd svtv-override-triplemap-syntax-check-implies-key-check
           (implies (and (svtv-override-triplemap-syntax-check keys phase test-alist val-alist probes triplemap)
                         (member-equal (svar-fix key) (svarlist-fix keys)))
                    (svtv-override-triplemap-key-check key phase test-alist val-alist probes triplemap))
           :hints(("Goal" :in-theory (enable svtv-override-triplemap-syntax-check svarlist-fix)))))


  (local (defthmd member-car-of-alist-keys-when-member-pair
           (implies (and (member pair x)
                         (consp pair))
                    (member (car pair) (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (local (defthm lookup-when-member-no-dups
           (implies (and (no-duplicatesp-equal (alist-keys x))
                         (member-equal pair x)
                         (consp pair))
                    (equal (hons-assoc-equal (car pair) x) pair))
           :hints(("Goal" :in-theory (enable alist-keys
                                             member-car-of-alist-keys-when-member-pair)))))

  
  (local (defthmd member-car-of-triplemap-alist-keys-when-member-pair
           (implies (and (member pair x)
                         (consp pair)
                         (svar-p (car pair)))
                    (member (car pair) (alist-keys (svtv-override-triplemap-fix x))))
           :hints(("Goal" :in-theory (enable alist-keys svtv-override-triplemap-fix)))))

  (local (defthm lookup-triplemap-when-member-no-dups
           (implies (and (no-duplicatesp-equal (alist-keys (svtv-override-triplemap-fix x)))
                         (member-equal pair x)
                         (consp pair)
                         (svar-p (car pair)))
                    (svtv-override-triple-equiv (cdr (hons-assoc-equal (car pair) x))
                                                (cdr pair)))
           :hints(("Goal" :in-theory (enable alist-keys
                                             svtv-override-triplemap-fix
                                             member-car-of-triplemap-alist-keys-when-member-pair)))))
  

  (local
   (defthm svtv-override-triplemap-envs-ok-of-extract-namemap-subset
     (implies
      (and (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env
                                            (svtv-probealist-extract
                                             probes
                                             (svtv-name-lhs-map-eval-list namemap ref-envs)))
           (SVTV-OVERRIDE-TRIPLEMAP-SYNTAX-CHECK
            (SVEX-ALIST-KEYS TEST-ALIST)
            PHASE
            TEST-ALIST VAL-ALIST PROBES TRIPLEMAP)
           (no-duplicatesp-equal (alist-keys (svtv-override-triplemap-fix triplemap)))
           (subsetp-equal triplemap-sub triplemap)
           (subsetp-equal (svtv-override-triplemap-refvar-keys triplemap-sub)
                          (svex-alist-keys test-alist)))
      (svtv-override-triplemap-envs-ok
       triplemap-sub pipe-env spec-env
       (svtv-probealist-extract
        probes
        (svtv-name-lhs-map-eval-list
         (fal-extract (svex-alist-keys test-alist) namemap)
         ref-envs))))
     :hints (("goal" :induct (len triplemap-sub)
              :expand ((:free (spec-outs)
                        (svtv-override-triplemap-envs-ok
                         triplemap-sub pipe-env spec-env spec-outs))
                       (svtv-override-triplemap-refvar-keys triplemap-sub)
                       (subsetp-equal triplemap-sub triplemap)))
             (and stable-under-simplificationp
                  '(:use ((:instance svtv-override-triplemap-envs-ok-implies-svtv-override-triple-envs-ok
                           (pair (car triplemap-sub))
                           (spec-outs (svtv-probealist-extract
                                       probes
                                       (svtv-name-lhs-map-eval-list namemap ref-envs))))
                          (:instance svtv-override-triplemap-syntax-check-implies-key-check
                           (keys (svex-alist-keys test-alist))
                           (key (caar triplemap-sub))))
                    :in-theory (enable svtv-override-triple-envs-ok
                                       svtv-override-triplemap-key-check)
                    :do-not-induct t)))))

  (defthm svtv-override-triplemap-envs-ok-of-extract-namemap
    (implies
     (and (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env
                                           (svtv-probealist-extract
                                            probes
                                            (svtv-name-lhs-map-eval-list namemap ref-envs)))
          (SVTV-OVERRIDE-TRIPLEMAP-SYNTAX-CHECK
           (SVEX-ALIST-KEYS TEST-ALIST)
           PHASE
           TEST-ALIST VAL-ALIST PROBES TRIPLEMAP)
          (no-duplicatesp-equal (alist-keys (svtv-override-triplemap-fix triplemap)))
          (subsetp-equal (svtv-override-triplemap-refvar-keys triplemap)
                         (svex-alist-keys test-alist)))
     (svtv-override-triplemap-envs-ok
      triplemap pipe-env spec-env
      (svtv-probealist-extract
       probes
       (svtv-name-lhs-map-eval-list
        (fal-extract (svex-alist-keys test-alist) namemap)
        ref-envs))))))



(local (defthm svex-alist-eval-monotonic-when-extract-vars-<<=
         (implies (and (svex-alist-monotonic-p x)
                       (svex-env-<<= (svex-env-extract (svex-alist-vars x) env1) env2))
                  (svex-env-<<= (svex-alist-eval x env1)
                                (svex-alist-eval x env2)))
         :hints (("goal" :use ((:instance svex-alist-monotonic-p-necc
                                (env1 (svex-env-extract (svex-alist-vars x) env1))))
                  :in-theory (e/d (svexlist-vars-of-svex-alist-vals)
                                  (svex-alist-monotonic-p-necc))))))

(defsection svtv-override-triplemap-syntax-check
  
  (local (std::set-define-current-function svtv-override-triplemap-syntax-check))
  (local (in-theory (enable svtv-override-triplemap-syntax-check)))

  (local (in-theory (enable member-of-svarlist-change-override
                            member-when-svar-override-p-diff
                            member-when-not-svar-override-p
                            member-svarlist-change-override-when-not-svar-override-p)))



  
  


  (local (defthm hons-assoc-equal-of-svar-change-override-lhs-map-keys-change-override
           (implies (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix map)) nil)
                    (equal (cdr (hons-assoc-equal (svar-change-override v type)
                                                  (svtv-name-lhs-map-keys-change-override map type)))
                           (cdr (hons-assoc-equal (svar-change-override v nil)
                                                  (svtv-name-lhs-map-fix map)))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svtv-name-lhs-map-fix
                                             alist-keys
                                             svtv-name-lhs-map-keys-change-override
                                             equal-of-svar-change-override)))))

  (local (defthm hons-assoc-equal-of-lhs-map-keys-change-override
           (implies (and (syntaxp (not (equal type ''nil)))
                         (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix map)) nil)
                         (svar-override-p v type)
                         (svar-p v))
                    (equal (cdr (hons-assoc-equal v
                                                  (svtv-name-lhs-map-keys-change-override map type)))
                           (cdr (hons-assoc-equal (svar-change-override v nil)
                                                  (svtv-name-lhs-map-fix map)))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svtv-name-lhs-map-fix
                                             alist-keys
                                             svtv-name-lhs-map-keys-change-override
                                             equal-of-svar-change-override)))))

  (local (in-theory (disable EVAL-SVTV-NAME-LHS-MAP-INVERSE-OF-LOOKUP-GEN)))


  (local
   (defret <fn>-implies-4vec-muxtest-subsetp-rw
     (implies (and ok
                   (bind-free '((ref-env . ref-env)) (ref-env))
                   (svtv-override-triple-envs-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
                                                 pipe-env spec-env ref-env))
              (4vec-muxtest-subsetp
               (svex-eval (svex-lookup key test-alist) spec-env)
               (svex-eval (svex-lookup key test-alist) pipe-env)))
     :hints (("goal" :use <fn>-implies-4vec-muxtest-subsetp))
    :fn svtv-override-triplemap-key-check))
  
  (local
   (defret <fn>-implies-muxtests-subsetp
     (implies (and ok
                   (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env
                                                    ref-env)
                   (member-equal (svar-fix key) (svarlist-fix keys))
                   (hons-assoc-equal (svar-fix key) triplemap)
                   )
              (4vec-muxtest-subsetp (svex-eval (svex-lookup key test-alist) spec-env)
                                    (svex-eval (svex-lookup key test-alist) pipe-env)))
     :hints(("Goal" :in-theory (enable ;; svex-envs-svexlist-muxtests-subsetp
                                ;; svtv-override-triplemap->tests
                                svarlist-fix
                                )))))

  

  (local (defthmd member-alist-keys-when-hons-assoc-equal
           (implies (hons-assoc-equal k x)
                    (member-equal k (alist-keys x)))))

  (local (defretd <fn>-implies-lookup-in-triplemap-rw
           (implies (and (bind-free (and (eq triplemap 'triplemap)
                                         '((phase . phase)
                                           (val-alist . val-alist)
                                           (probes . probes)
                                           (test-alist . test-alist)))
                                    (phase val-alist probes test-alist))
                         ok
                         (svar-p key)
                         (case-split (svex-lookup key test-alist))
                         ;; (case-split (svex-lookup key val-alist))
                         )
                    (hons-assoc-equal key triplemap))
           :hints (("goal" :use <fn>-implies-lookup-in-triplemap
                    :in-theory (disable <fn>-implies-lookup-in-triplemap)))
           :fn svtv-override-triplemap-key-check))

  (local (defret <fn>-implies-4vec-muxtest-subsetp-rw2
           (implies (and (bind-free '((phase . phase)
                                      (val-alist . val-alist)
                                      (probes . probes)
                                      (triplemap . triplemap)
                                      (ref-env . ref-env))
                                    (phase val-alist probes triplemap ref-env))
                         (svtv-override-triple-envs-ok (cdr (hons-assoc-equal (svar-fix key) triplemap))
                                                       pipe-env spec-env ref-env)
                         ok)
                    (4vec-muxtest-subsetp
                     (svex-eval (svex-lookup key test-alist) spec-env)
                     (svex-eval (svex-lookup key test-alist) pipe-env)))
           :hints(("Goal" :use <fn>-implies-4vec-muxtest-subsetp
                   :in-theory (disable <fn>-implies-4vec-muxtest-subsetp)))
           :fn svtv-override-triplemap-key-check))

  
  (local (defret svtv-override-triplemap-key-check-when-member-and-<fn>
           (implies (and ok
                         (member-equal (svar-fix key) (svarlist-fix keys)))
                    (svtv-override-triplemap-key-check key phase test-alist val-alist probes triplemap))
           :hints(("Goal" :in-theory (enable svarlist-fix)))))

  (local (defret svtv-override-triplemap-key-check-when-<fn>
           :pre-bind ((keys (svex-alist-keys test-alist)))
           (implies ok
                    (svtv-override-triplemap-key-check key phase test-alist val-alist probes triplemap))
           :hints (("goal" :use ((:instance svtv-override-triplemap-key-check-when-member-and-<fn>
                                  (keys (Svex-alist-keys test-alist))))
                    :in-theory (disable svtv-override-triplemap-key-check-when-member-and-<fn>))
                   (and stable-under-simplificationp
                        '(:in-theory (enable svtv-override-triplemap-key-check))))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  
  (local
   (defret <fn>-implies-4vec-muxtest-subsetp
     :pre-bind ((keys (svex-alist-keys test-alist)))
     (implies (and ok
                   (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env ref-env)
                   ;; (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap)))
                   ;; (svarlist-override-p params :test)
                   ;; (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   ;; (subsetp-equal (lhs-vars (cdr (hons-assoc-equal testvar 
                   ;; (svex-alist-monotonic-p in-alist)
                   ;; (svex-alist-monotonic-p test-alist)
                   ;; (svex-alist-monotonic-p val-alist)
                   )
              (4vec-muxtest-subsetp
               (lhs-eval-x (cdr (hons-assoc-equal testvar (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist spec-env))
               (lhs-eval-x (cdr (hons-assoc-equal testvar (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist pipe-env))))
     :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp-by-badbit))
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst '4vec-muxtest-subsetp-badbit clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d  (lhbit-eval-x
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap
                                     4vec-muxtest-subsetp-implies-bit-index
                                     member-alist-keys-when-hons-assoc-equal
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap-rw)
                                    (acl2::hons-assoc-equal-iff-member-alist-keys)))))))

  (local (defthm 4vec-bit-index-of-x
           (equal (4vec-bit-index i (4vec-x))
                  '(1 . 0))
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))

  (local (defthmd equal-of-4vec-bit-index-when-<<=
           (implies (and (4vec-<<= x y)
                         (not (equal (4vec-bit-index i x) '(1 . 0))))
                    (equal (equal (4vec-bit-index i x) (4vec-bit-index i y)) t))
           :hints (("goal" :in-theory (enable 4vec-<<=-implies-bit-index)))))

  (local
   (defret <fn>-implies-4vec-override-mux-<<=
     :pre-bind ((keys (svex-alist-keys test-alist)))
     (implies (and ok
                   (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env
                                                    (svtv-probealist-extract
                                                     probes
                                                     (svtv-name-lhs-map-eval-list namemap ref-envs)))
                   ;; (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap)))
                   ;; (svarlist-override-p params :test)
                   ;; (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   ;; (subsetp-equal (lhs-vars (cdr (hons-assoc-equal testvar 
                   ;; (svex-alist-monotonic-p in-alist)
                   ;; (svex-alist-monotonic-p test-alist)
                   ;; (svex-alist-monotonic-p val-alist)
                   ;;  (svar-p v)
                   (member-equal (svar-change-override v nil)
                                 (svarlist-change-override overridekeys nil))
                   (or (svar-override-p v :test)
                       (svar-override-p v :val))
                   )
              (4vec-override-mux-<<=
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist pipe-env))
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval val-alist pipe-env))
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist spec-env))
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval val-alist spec-env))
               (svex-env-lookup (svar-change-override v nil) (nth phase ref-envs))))
     :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=-by-badbit) :do-not-induct t)
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst '4vec-override-mux-<<=-badbit clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
           
            (and stable-under-simplificationp
                 '(:in-theory (e/d  (lhbit-eval-x
                                     lhbit-eval-zero
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap
                                     4vec-override-mux-<<=-implies-bit-index
                                     member-alist-keys-when-hons-assoc-equal
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap-rw
                                     svtv-override-triple-envs-ok
                                     4vec-override-mux-ok
                                     svtv-override-triplemap-key-check
                                     equal-of-4vec-bit-index-when-<<=)
                                    (acl2::hons-assoc-equal-iff-member-alist-keys
                                     svtv-override-triplemap-key-check-when-svtv-override-triplemap-syntax-check
                                     svtv-override-triplemap-key-check-when-member-and-svtv-override-triplemap-syntax-check
                                     svtv-override-triple-envs-ok-of-lookup-when-svtv-override-triplemap-envs-ok))
                   :use ((:instance svtv-override-triple-envs-ok-of-lookup-when-svtv-override-triplemap-envs-ok
                          (spec-run (svtv-probealist-extract
                                     probes
                                     (svtv-name-lhs-map-eval-list namemap ref-envs)))
                          (key (lhbit-var->name (svtv-name-lhs-map-var/idx-find (svar-change-override v nil) badbit namemap))))
                         (:instance svtv-override-triplemap-key-check-when-svtv-override-triplemap-syntax-check
                          (key (lhbit-var->name (svtv-name-lhs-map-var/idx-find (svar-change-override v nil) badbit namemap))))))))))



  ;; Want to know that if a variable is not among the overridekeys, then it
  ;; isn't touched by any triples with refvars from the triplemap.  That is,
  ;; every signal mapped to the name corresponding to a triple with a refvar is
  ;; in the overridekeys.

  ;; (svtv-override-triplemap-overridekeys-ok triplemap namemap override-keys) -->
  ;; if k is a refvar key of triplemap, then the vars in its namemap lookup are a subset of the override keys
 
  (local
   (defret <fn>-implies-4vec-<<=-non-overridekey-override-vals
     :pre-bind ((keys (svex-alist-keys test-alist)))
     (implies (and ok
                   (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env ref-env)
                   ;; (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap)))
                   (equal (svex-alist-keys test-alist)
                          (svex-alist-keys val-alist))
                   ;; (svarlist-override-p params :test)
                   ;; (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   ;; (subsetp-equal (lhs-vars (cdr (hons-assoc-equal testvar 
                   ;; (svex-alist-monotonic-p in-alist)
                   ;; (svex-alist-monotonic-p test-alist)
                   ;; (svex-alist-monotonic-p val-alist)
                   ;;  (svar-p v)
                   (not (member-equal (svar-change-override v nil)
                                      (svarlist-change-override overridekeys nil)))
                   (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   (or (svar-override-p v :test)
                       (svar-override-p v :val)))
              (4vec-<<=
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval val-alist pipe-env))
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval val-alist spec-env))))
     :hints(("Goal" :in-theory (enable 4vec-<<=-by-badbit) :do-not-induct t)
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst '4vec-<<=-badbit clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
           
            (and stable-under-simplificationp
                 '(:in-theory (e/d  (lhbit-eval-x
                                     lhbit-eval-zero
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap
                                     4vec-override-mux-<<=-implies-bit-index
                                     member-alist-keys-when-hons-assoc-equal
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap-rw
                                     svtv-override-triple-envs-ok
                                     4vec-override-mux-ok
                                     svtv-override-triplemap-key-check
                                     equal-of-4vec-bit-index-when-<<=)
                                    (acl2::hons-assoc-equal-iff-member-alist-keys
                                     svtv-override-triplemap-key-check-when-svtv-override-triplemap-syntax-check
                                     svtv-override-triplemap-key-check-when-member-and-svtv-override-triplemap-syntax-check
                                     svtv-override-triple-envs-ok-of-lookup-when-svtv-override-triplemap-envs-ok))
                   :use ((:instance svtv-override-triple-envs-ok-of-lookup-when-svtv-override-triplemap-envs-ok
                          (spec-run ref-env)
                          (key (lhbit-var->name (svtv-name-lhs-map-var/idx-find (svar-change-override v nil) badbit namemap))))
                         (:instance svtv-override-triplemap-key-check-when-svtv-override-triplemap-syntax-check
                          (key (lhbit-var->name (svtv-name-lhs-map-var/idx-find (svar-change-override v nil) badbit namemap))))))))))


  (local (defthm equal-lhs-eval-x-by-badbit
           (implies (and (syntaxp (and (consp a) (eq (car a) 'lhs-eval-x)
                                       (consp b) (eq (car b) 'lhs-eval-x)))
                         (acl2::rewriting-positive-literal `(equal ,a ,b))
                         (4vec-p a)
                         (4vec-p b))
                    (equal (Equal a b)
                           (b* ((badbit (4vec-equiv-badbit a b)))
                             (equal (4vec-bit-index badbit a) (4vec-bit-index badbit b)))))
           :hints(("Goal" :use 4vec-equiv-by-badbit))))

  (local 
   (defret <fn>-implies-equal-non-overridekey-override-tests
     :pre-bind ((keys (svex-alist-keys test-alist)))
     (implies (and ok
                   (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env ref-env)
                   ;; (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap)))
                   (equal (svex-alist-keys test-alist)
                          (svex-alist-keys val-alist))
                   ;; (svarlist-override-p params :test)
                   ;; (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   ;; (subsetp-equal (lhs-vars (cdr (hons-assoc-equal testvar 
                   ;; (svex-alist-monotonic-p in-alist)
                   ;; (svex-alist-monotonic-p test-alist)
                   ;; (svex-alist-monotonic-p val-alist)
                   ;;  (svar-p v)
                   (not (member-equal (svar-change-override v nil)
                                      (svarlist-change-override overridekeys nil)))
                   (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   (or (svar-override-p v :test)
                       (svar-override-p v :val)))
              (equal (equal
                      (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist pipe-env))
                      (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist spec-env)))
                     t))
     :hints(("Goal" :in-theory (enable equal-lhs-eval-x-by-badbit) :do-not-induct t)
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst '4vec-equiv-badbit clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
           
            (and stable-under-simplificationp
                 '(:in-theory (e/d  (lhbit-eval-x
                                     lhbit-eval-zero
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap
                                     4vec-override-mux-<<=-implies-bit-index
                                     member-alist-keys-when-hons-assoc-equal
                                     svtv-override-triplemap-key-check-implies-lookup-in-triplemap-rw
                                     svtv-override-triple-envs-ok
                                     4vec-override-mux-ok
                                     svtv-override-triplemap-key-check
                                     equal-of-4vec-bit-index-when-<<=)
                                    (acl2::hons-assoc-equal-iff-member-alist-keys
                                     svtv-override-triplemap-key-check-when-svtv-override-triplemap-syntax-check
                                     svtv-override-triplemap-key-check-when-member-and-svtv-override-triplemap-syntax-check
                                     svtv-override-triple-envs-ok-of-lookup-when-svtv-override-triplemap-envs-ok))
                   :use ((:instance svtv-override-triple-envs-ok-of-lookup-when-svtv-override-triplemap-envs-ok
                          (spec-run ref-env)
                          (key (lhbit-var->name (svtv-name-lhs-map-var/idx-find (svar-change-override v nil) badbit namemap))))
                         (:instance svtv-override-triplemap-key-check-when-svtv-override-triplemap-syntax-check
                          (key (lhbit-var->name (svtv-name-lhs-map-var/idx-find (svar-change-override v nil) badbit namemap))))))))))

  (local
   (defret <fn>-implies-4vec-<<=-non-overridekey-override-tests
     :pre-bind ((keys (svex-alist-keys test-alist)))
     (implies (and ok
                   (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env ref-env)
                   ;; (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix namemap)))
                   (equal (svex-alist-keys test-alist)
                          (svex-alist-keys val-alist))
                   ;; (svarlist-override-p params :test)
                   ;; (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   ;; (subsetp-equal (lhs-vars (cdr (hons-assoc-equal testvar 
                   ;; (svex-alist-monotonic-p in-alist)
                   ;; (svex-alist-monotonic-p test-alist)
                   ;; (svex-alist-monotonic-p val-alist)
                   ;;  (svar-p v)
                   (not (member-equal (svar-change-override v nil)
                                      (svarlist-change-override overridekeys nil)))
                   (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                   (or (svar-override-p v :test)
                       (svar-override-p v :val)))
              (4vec-<<=
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist pipe-env))
               (lhs-eval-x (cdr (hons-assoc-equal (svar-change-override v nil) (mv-nth 1 (svtv-name-lhs-map-inverse namemap)))) (svex-alist-eval test-alist spec-env))))
     :hints (("goal" :use <fn>-implies-equal-non-overridekey-override-tests
              :in-theory (disable <fn>-implies-equal-non-overridekey-override-tests)))))
  

  (local (in-theory (disable fast-alist-clean)))

  (local
   (defthm alist-keys-of-fast-alist-clean-under-set-equiv
     (set-equiv (alist-keys (fast-alist-clean x))
                (alist-keys x))
     :hints(("Goal" :in-theory (e/d (acl2::set-unequal-witness-rw
                                     acl2::alist-keys-member-hons-assoc-equal)
                                    (acl2::hons-assoc-equal-iff-member-alist-keys))))))

  (local (defthm svarlist-override-p-when-subsetp
           (implies (and (svarlist-override-p x type)
                         (subsetp-equal (svarlist-fix y) (svarlist-fix x) ))
                    (svarlist-override-p y type))
           :hints(("Goal" :in-theory (enable svarlist-override-p svarlist-fix)
                   :induct (svarlist-override-p y type)))))



  (local (defthm no-duplicate-keys-of-fal-extract
           (implies (no-duplicatesp-equal keys)
                    (no-duplicatesp-equal (alist-keys (fal-extract keys x))))
           :hints(("Goal" :in-theory (e/d (alist-keys fal-extract
                                                      acl2::alist-keys-member-hons-assoc-equal)
                                          (acl2::hons-assoc-equal-iff-member-alist-keys))))))


  
  
  (local (defthm svar-overridekeys-envs-ok-of-svtv-fsm-phase-inputs-no-tests
           (implies (and (SVEX-ENV-<<= (SVEX-ENV-EXTRACT (SVEX-ALIST-VARS in-alist)
                                                         PIPE-ENV)
                                       SPEC-ENV)
                         (SVARLIST-OVERRIDE-P PARAMS :TEST)
                         (SVARLIST-OVERRIDE-P (SVTV-NAME-LHS-MAP-VARS NAMEMAP)
                                              NIL)
                         (SVEX-ALIST-monotonic-p in-alist))
                    (svar-overridekeys-envs-ok v params overridekeys
                                               (svtv-fsm-phase-inputs (svex-alist-eval in-alist pipe-env)
                                                                      nil
                                                                      nil namemap)
                                               (svtv-fsm-phase-inputs (svex-alist-eval in-alist spec-env)
                                                                      nil
                                                                      nil namemap)
                                               ref-env))
           :hints(("Goal" :in-theory (e/d (svar-overridekeys-envs-ok
                                             svtv-fsm-phase-inputs
                                             SVTV-FSM-ENV-INVERSEMAP
                                             svtv-fsm-namemap-env)
                                          (SVARLIST-CHANGE-OVERRIDE-WHEN-OVERRIDE-P))))))

  (defthm overridekeys-envs-ok-of-svtv-fsm-phase-inputs-no-tests
    (implies (and (SVEX-ENV-<<= (SVEX-ENV-EXTRACT (SVEX-ALIST-VARS in-alist)
                                                  PIPE-ENV)
                                SPEC-ENV)
                  (SVARLIST-OVERRIDE-P PARAMS :TEST)
                  (SVARLIST-OVERRIDE-P (SVTV-NAME-LHS-MAP-VARS NAMEMAP)
                                       NIL)
                  (SVEX-ALIST-monotonic-p in-alist))
             (overridekeys-envs-ok params overridekeys
                                   (svtv-fsm-phase-inputs (svex-alist-eval in-alist pipe-env)
                                                          nil
                                                          nil namemap)
                                   (svtv-fsm-phase-inputs (svex-alist-eval in-alist spec-env)
                                                          nil
                                                          nil namemap)
                                   ref-env))
    :hints(("Goal" :in-theory (enable overridekeys-envs-ok-by-witness))))
  
  (defret <fn>-implies-svar-overridekeys-envs-ok
    :pre-bind ((keys (svex-alist-keys test-alist)))
    (implies (and ok
                  (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env
                                                   (svtv-probealist-extract
                                                    probes
                                                    (svtv-name-lhs-map-eval-list namemap ref-envs)))
                  (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                  (equal (svex-alist-keys test-alist) (svex-alist-keys val-alist))
                  (no-duplicatesp-equal (svex-alist-keys test-alist))
                  (no-duplicatesp-equal (alist-keys (svtv-override-triplemap-fix triplemap)))
                  (svarlist-override-p params :test)
                  (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                  (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                  (subsetp-equal (svtv-override-triplemap-refvar-keys triplemap)
                                 (svex-alist-keys test-alist))
                  (svex-alist-monotonic-p in-alist))
             (svar-overridekeys-envs-ok v params overridekeys
                                   (svtv-fsm-phase-inputs (svex-alist-eval in-alist pipe-env)
                                                          (svex-alist-eval val-alist pipe-env)
                                                          (svex-alist-eval test-alist pipe-env)
                                                          namemap)
                                   (svtv-fsm-phase-inputs (svex-alist-eval in-alist spec-env)
                                                          (svex-alist-eval val-alist spec-env)
                                                          (svex-alist-eval test-alist spec-env)
                                                          namemap)
                                   (nth phase ref-envs)))
    :hints (("goal" :in-theory (e/d (svar-overridekeys-envs-ok
                                     svtv-fsm-phase-inputs
                                     svtv-fsm-namemap-env
                                       svtv-fsm-env-inversemap)
                                    (SVARLIST-CHANGE-OVERRIDE-WHEN-OVERRIDE-P))
             :do-not-induct t)))

  (defret <fn>-implies-overridekeys-envs-ok
    :pre-bind ((keys (svex-alist-keys test-alist)))
    (implies (and ok
                  (svtv-override-triplemap-envs-ok triplemap pipe-env spec-env
                                                   (svtv-probealist-extract
                                                    probes
                                                    (svtv-name-lhs-map-eval-list namemap ref-envs)))
                  (svex-env-<<= (svex-env-extract (svex-alist-vars in-alist) pipe-env) spec-env)
                  (equal (svex-alist-keys test-alist) (svex-alist-keys val-alist))
                  (no-duplicatesp-equal (svex-alist-keys test-alist))
                  (no-duplicatesp-equal (alist-keys (svtv-override-triplemap-fix triplemap)))
                  (svarlist-override-p params :test)
                  (svtv-override-triplemap-overridekeys-ok triplemap namemap overridekeys)
                  (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                  (subsetp-equal (svtv-override-triplemap-refvar-keys triplemap)
                                 (svex-alist-keys test-alist))
                  (svex-alist-monotonic-p in-alist))
             (overridekeys-envs-ok params overridekeys
                                   (svtv-fsm-phase-inputs (svex-alist-eval in-alist pipe-env)
                                                          (svex-alist-eval val-alist pipe-env)
                                                          (svex-alist-eval test-alist pipe-env)
                                                          namemap)
                                   (svtv-fsm-phase-inputs (svex-alist-eval in-alist spec-env)
                                                          (svex-alist-eval val-alist spec-env)
                                                          (svex-alist-eval test-alist spec-env)
                                                          namemap)
                                   (nth phase ref-envs)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))







                                        

(defsection svtv-override-triplemaplist-syntax-check-aux
  (local (std::set-define-current-function svtv-override-triplemaplist-syntax-check-aux))
  (local (in-theory (enable svtv-override-triplemaplist-syntax-check-aux)))

  (local (defun ind (phase in-alists test-alists val-alists triplemaps)
           (if (atom in-alists)
               (list phase in-alists test-alists val-alists triplemaps)
             (ind (+ 1 (nfix phase))
                  (cdr in-alists)
                  (Cdr test-alists)
                  (cdr val-alists)
                  (cdr triplemaps)))))

  (local (in-theory (disable fast-alist-clean)))

  
  (local
   (defthm svex-env-<<=-of-append-extract
     (iff (svex-env-<<= (append (svex-env-extract keys1 x)
                                (svex-env-extract keys2 x))
                        y)
          (and (svex-env-<<= (svex-env-extract keys1 x) y)
               (svex-env-<<= (svex-env-extract keys2 x) y)))
     :hints ((and stable-under-simplificationp
                  (b* ((lit (assoc 'svex-env-<<= clause))
                       (append-p (and (consp (cadr lit))
                                      (eq (caadr lit) 'acl2::binary-append))))
                    (if append-p
                        `(:expand (,lit)
                          :use ((:instance svex-env-<<=-necc
                                 (x (svex-env-extract keys1 x))
                                 (var (svex-env-<<=-witness . ,(cdr lit))))
                                (:instance svex-env-<<=-necc
                                 (x (svex-env-extract keys2 x))
                                 (var (svex-env-<<=-witness . ,(cdr lit)))))
                          :in-theory (disable svex-env-<<=-necc))
                      `(:expand (,lit)
                          :use ((:instance svex-env-<<=-necc
                                 (x (append (svex-env-extract keys1 x)
                                            (svex-env-extract keys2 x)))
                                 (var (svex-env-<<=-witness . ,(cdr lit)))))
                          :in-theory (disable svex-env-<<=-necc))))))))

  
  (defret <fn>-implies-overridekeys-envlists-ok
    (implies (and ok
                  (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env
                                                       (svtv-probealist-extract
                                                        probes
                                                        (svtv-name-lhs-map-eval-list namemap ref-envs)))
                  (svex-env-<<= (svex-env-extract (svex-alistlist-vars in-alists) pipe-env) spec-env)
                  (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
                  (no-duplicatesp-each (svex-alist-keys-list test-alists))
                  (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
                  (svarlist-override-p params :test)
                  (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
                  (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                  (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
                  (svex-alistlist-check-monotonic in-alists)
                  (<= (len test-alists) (len in-alists)))
             (overridekeys-envlists-ok params overridekeys
                                        (svtv-fsm-to-base-fsm-inputs (svex-alistlist-eval in-alists pipe-env)
                                                                     (svex-alistlist-eval val-alists pipe-env)
                                                                     (svex-alistlist-eval test-alists pipe-env)
                                                                     namemap)
                                        (svtv-fsm-to-base-fsm-inputs (svex-alistlist-eval in-alists spec-env)
                                                                     (svex-alistlist-eval val-alists spec-env)
                                                                     (svex-alistlist-eval test-alists  spec-env)
                                                                     namemap)
                                        (nthcdr phase ref-envs)))
    :hints (("goal" :in-theory (enable svtv-override-triplemaplist-envs-ok
                                       svex-alistlist-vars
                                       svex-alist-keys-list
                                       no-duplicatesp-each
                                       alistlist-keys
                                       svtv-override-triplemaplist-fix
                                       svtv-override-triplemaplist-overridekeys-ok
                                       svtv-override-triplemaplist-refvar-keys-subsetp
                                       svex-alistlist-check-monotonic
                                       overridekeys-envlists-ok
                                       svtv-fsm-to-base-fsm-inputs
                                       svex-alistlist-eval
                                       nthcdr)
             :induct (ind phase in-alists test-alists val-alists triplemaps)
             :expand ((:free (spec-outs)
                       (SVTV-OVERRIDE-TRIPLEMAP-ENVS-OK
                        NIL PIPE-ENV SPEC-ENV spec-outs))
                      (SVTV-OVERRIDE-TRIPLEMAP-OVERRIDEKEYS-OK NIL NAMEMAP OVERRIDEKEYS))
             :do-not-induct t))))

(defsection overridekeys-envlists-ok-of-svtv-cycle-run-fsm-inputs

  ;; (local (in-theory (enable member-of-svarlist-change-override
  ;;                           member-when-svar-override-p-diff
  ;;                           member-when-not-svar-override-p
  ;;                           member-svarlist-change-override-when-not-svar-override-p)))

  (local (defthm svtv-cyclephaselist-unique-i/o-phase-implies-consp
           (implies (svtv-cyclephaselist-unique-i/o-phase phases)
                    (consp phases))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase)))
           :rule-classes :forward-chaining))


  
  (defthm svar-overridekeys-envs-ok-of-append-consts
    (implies (and (svarlist-override-p (alist-keys (svex-env-fix c)) nil)
                  (svar-overridekeys-envs-ok v params overridkeys impl-env spec-env spec-outs))
             (svar-overridekeys-envs-ok v params overridkeys
                                        (append c impl-env)
                                        (append c spec-env)
                                        spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-ok
                                      svex-env-boundp-iff-member-alist-keys
                                      member-of-svarlist-change-override
                                      member-when-svar-override-p-diff
                                      member-when-not-svar-override-p
                                      member-svarlist-change-override-when-not-svar-override-p)
            :do-not-induct t)))

  (defthm overridekeys-envs-ok-of-append-consts
    (implies (and (svarlist-override-p (alist-keys (svex-env-fix c)) nil)
                  (overridekeys-envs-ok params overridkeys impl-env spec-env spec-outs))
             (overridekeys-envs-ok params overridkeys
                                   (append c impl-env)
                                   (append c spec-env)
                                   spec-outs))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm svar-overridekeys-envs-ok-of-only-consts
    (implies (svarlist-override-p (alist-keys (svex-env-fix c)) nil)
             (svar-overridekeys-envs-ok v params overridkeys c c spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-ok
                                      svex-env-boundp-iff-member-alist-keys
                                      member-of-svarlist-change-override
                                      member-when-svar-override-p-diff
                                      member-when-not-svar-override-p
                                      member-svarlist-change-override-when-not-svar-override-p
                                      4VEC-OVERRIDE-MUX-<<=-SAME)
            :do-not-induct t)))

  (defthm overridekeys-envs-ok-of-only-consts
    (implies (svarlist-override-p (alist-keys (svex-env-fix c)) nil)
             (overridekeys-envs-ok params overridkeys c c spec-outs))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))


  (local (defun ind1 (cycle-phases phase-outs)
           (if (atom cycle-phases)
               phase-outs
             (ind1 (cdr cycle-phases) (cdr phase-outs)))))

  ;; (defthm overridekeys-envlist-ok-of-svtv-cycle-fsm-inputs-no-output
  ;;   (implies (And (not (svtv-cycle-output-phase cycle-phases))
  ;;                 (svarlist-override-p (svtv-cyclephaselist-keys cycle-phases) nil))
  ;;            (overridekeys-envlists-ok params overridekeys
  ;;                                      (svtv-cycle-fsm-inputs impl-ins cycle-phases)
  ;;                                      (svtv-cycle-fsm-inputs spec-ins cycle-phases)
  ;;                                      phase-outs))
  ;;   :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
  ;;                                     svtv-cycle-step-fsm-inputs
  ;;                                     svtv-cycle-output-phase
  ;;                                     svtv-cyclephaselist-keys
  ;;                                     overridekeys-envlists-ok
  ;;                                     svtv-cyclephaselist-has-outputs-captured)
  ;;           :induct (ind1 cycle-phases phase-outs))))

  (local (defthm svtv-cyclephaselist-unique-i/o-phase-implies-output-scaptured
           (implies (svtv-cyclephaselist-unique-i/o-phase phases)
                    (svtv-cyclephaselist-has-outputs-captured phases))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured
                                             svtv-cyclephaselist-unique-i/o-phase)))))

  (defthm overridekeys-envlist-ok-of-svtv-cycle-fsm-inputs-when-no-i/o-phase
    (implies (And ;; (svtv-cycle-output-phase cycle-phases)
              (svtv-cyclephaselist-no-i/o-phase cycle-phases)
              (svarlist-override-p (svtv-cyclephaselist-keys cycle-phases) nil))
             (overridekeys-envlists-ok params overridekeys
                                       (svtv-cycle-fsm-inputs impl-ins cycle-phases)
                                       (svtv-cycle-fsm-inputs spec-ins cycle-phases)
                                       phase-outs))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cycle-step-fsm-inputs
                                      svtv-cycle-output-phase
                                      svtv-cyclephaselist-keys
                                      overridekeys-envlists-ok
                                      svtv-cyclephaselist-no-i/o-phase
                                      svtv-cyclephaselist-has-outputs-captured)
            :induct (ind1 cycle-phases phase-outs))))

  
  (defthm overridekeys-envlist-ok-of-svtv-cycle-fsm-inputs
    (implies (And ;; (svtv-cycle-output-phase cycle-phases)
              (svtv-cyclephaselist-unique-i/o-phase cycle-phases)
              (svarlist-override-p (svtv-cyclephaselist-keys cycle-phases) nil)
              (overridekeys-envs-ok params overridekeys impl-ins spec-ins
                                    (nth (svtv-cycle-output-phase cycle-phases) phase-outs)))
             (overridekeys-envlists-ok params overridekeys
                                       (svtv-cycle-fsm-inputs impl-ins cycle-phases)
                                       (svtv-cycle-fsm-inputs spec-ins cycle-phases)
                                       phase-outs))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cycle-step-fsm-inputs
                                      svtv-cycle-output-phase
                                      svtv-cyclephaselist-keys
                                      overridekeys-envlists-ok
                                      svtv-cyclephaselist-unique-i/o-phase
                                      svtv-cyclephaselist-has-outputs-captured)
            :induct (ind1 cycle-phases phase-outs))))

  (defthm overridekeys-envlists-ok-of-append
    (implies (equal (len spec1) (len impl1))
             (equal (overridekeys-envlists-ok params overridekeys
                                              (append impl1 impl2)
                                              (append spec1 spec2)
                                              phase-outs)
                    (and (overridekeys-envlists-ok params overridekeys
                                                   impl1 spec1 phase-outs)
                         (overridekeys-envlists-ok params overridekeys
                                                   impl2 spec2 (nthcdr (len spec1) phase-outs)))))
    :hints(("Goal" :in-theory (enable overridekeys-envlists-ok)
            :induct (overridekeys-envlists-ok params overridekeys
                                              impl1 spec1 phase-outs))))

  ;; (defthm overridekeys-envlists-ok-of-nil/append
  ;;   (equal (overridekeys-envlists-ok params overridekeys
  ;;                                    nil
  ;;                                    (append spec1 spec2)
  ;;                                    phase-outs)
  ;;          (and (overridekeys-envlists-ok params overridekeys
  ;;                                         nil spec1 phase-outs)
  ;;               (overridekeys-envlists-ok params overridekeys
  ;;                                         nil spec2 (nthcdr (len spec1) phase-outs))))
  ;;   :hints(("Goal" :in-theory (enable overridekeys-envlists-ok)
  ;;           :induct (overridekeys-envlists-ok params overridekeys
  ;;                                             nil spec1 phase-outs))))


  (local (defun ind2 (cycle-phases impl-ins spec-ins phase-outs)
           (if (atom spec-ins)
               (list cycle-phases impl-ins spec-ins phase-outs)
             (ind2 cycle-phases (cdr impl-ins) (cdr spec-ins) (nthcdr (len cycle-phases) phase-outs)))))

  (local (defthm svtv-cycle-output-phase-linear
           (implies (svtv-cyclephaselist-unique-i/o-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase
                                             svtv-cycle-output-phase)))
           :rule-classes (:rewrite :linear)))

  (local (defcong list-equiv equal (overridekeys-envlists-ok params overridekeys impl-ins spec-ins phase-outs) 5
           :hints(("Goal" :in-theory (enable overridekeys-envlists-ok)))))

  (local (defthm nthcdr-of-len-or-more-under-list-equiv
           (implies (<= (len x) (nfix n))
                    (list-equiv (nthcdr n x) nil))))
  
  (defthm overridekeys-envlists-ok-of-svtv-cycle-run-fsm-inputs
    (implies (and (overridekeys-envlists-ok params overridekeys impl-ins spec-ins
                                            (svex-envlist-phase-outputs-extract-cycle-outputs
                                             cycle-phases phase-outs))
                  (svtv-cyclephaselist-unique-i/o-phase cycle-phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys cycle-phases) nil)
                  (equal (len impl-ins) (len spec-ins)))
             (overridekeys-envlists-ok params overridekeys
                                       (svtv-cycle-run-fsm-inputs impl-ins cycle-phases)
                                       (svtv-cycle-run-fsm-inputs spec-ins cycle-phases)
                                       phase-outs))
    :hints (("goal" :induct (ind2 cycle-phases impl-ins spec-ins phase-outs)
             :in-theory (enable svtv-cycle-run-fsm-inputs
                                svex-envlist-phase-outputs-extract-cycle-outputs
                                overridekeys-envlists-ok))))

  )
  







(defsection svtv-override-triplemaplist-syntax-check
  (local (std::set-define-current-function svtv-override-triplemaplist-syntax-check))
  (local (in-theory (enable svtv-override-triplemaplist-syntax-check)))
  
  (defret <fn>-implies-overridekeys-envlists-ok
    (implies (and ok
                  (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env
                                                       (svtv-probealist-extract
                                                        probes
                                                        (svtv-name-lhs-map-eval-list namemap ref-envs)))
                  (svex-env-<<= (svex-env-extract (svex-alistlist-vars in-alists) pipe-env) spec-env)
                  (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
                  (no-duplicatesp-each (svex-alist-keys-list test-alists))
                  (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
                  (svarlist-override-p params :test)
                  (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
                  (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                  (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
                  (svex-alistlist-check-monotonic in-alists)
                  (<= (len test-alists) (len in-alists)))
             (overridekeys-envlists-ok params overridekeys
                                        (svtv-fsm-to-base-fsm-inputs (svex-alistlist-eval in-alists pipe-env)
                                                                     (svex-alistlist-eval val-alists pipe-env)
                                                                     (svex-alistlist-eval test-alists pipe-env)
                                                                     namemap)
                                        (svtv-fsm-to-base-fsm-inputs (svex-alistlist-eval in-alists spec-env)
                                                                     (svex-alistlist-eval val-alists spec-env)
                                                                     (svex-alistlist-eval test-alists  spec-env)
                                                                     namemap)
                                        ref-envs))
    :hints (("goal" :use ((:instance svtv-override-triplemaplist-syntax-check-aux-implies-overridekeys-envlists-ok
                           (phase 0)))
             :in-theory (disable svtv-override-triplemaplist-syntax-check-aux-implies-overridekeys-envlists-ok))))


  (local (defthm take-of-svex-alistlist-eval
           (equal (take n (svex-alistlist-eval x a))
                  (svex-alistlist-eval (take n x) a))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-eval
                                           svex-alist-eval)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))))))

  (local (in-theory (disable svtv-override-triplemaplist-syntax-check)))


  (local (defthm svex-alistlist-vars-of-repeat-nil
           (equal (Svex-alistlist-vars (repeat n nil)) nil)
           :hints(("Goal" :in-theory (enable repeat svex-alistlist-vars)))))
  
  (local (defthm subsetp-svex-alistlist-vars-of-take
           (Subsetp-equal (svex-alistlist-vars (take n x))
                          (svex-alistlist-vars x))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-vars take)
                                          (acl2::take-of-too-many))))))

  (local (defthm svex-env-<<=-of-extract-subset
           (implies (and (svex-env-<<= (svex-env-extract keys1 x) y)
                         (subsetp-equal (svarlist-fix keys2) (svarlist-fix keys1)))
                    (svex-env-<<= (svex-env-extract keys2 x) y))
           :hints ((and stable-under-simplificationp
                        (b* ((lit (car (last clause))))
                          `(:expand (,lit)
                            :use ((:instance svex-env-<<=-necc
                                   (var (svex-env-<<=-witness . ,(cdr lit)))
                                   (x (svex-env-extract keys1 x))))
                            :in-theory (disable svex-env-<<=-necc)))))))

  
  (defret <fn>-implies-overridekeys-envlists-ok-of-pipe-env->phase-envs
    :pre-bind (((svtv-spec spec))
               (namemap spec.namemap)
               (in-alists spec.in-alists)
               (test-alists spec.override-test-alists)
               (val-alists spec.override-val-alists)
               (probes spec.probes)
               (outvars (svtv-probealist-outvars spec.probes))
               (my-in-alists (take (len outvars) in-alists)))
    (implies (and ok
                  (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env
                                                       (svtv-spec-phase-outs->pipe-out spec phase-outs))
                  (svex-env-<<= (svex-env-extract (svex-alistlist-vars in-alists) pipe-env)
                                spec-env)
                  (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
                  (no-duplicatesp-each (svex-alist-keys-list test-alists))
                  (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
                  (svarlist-override-p params :test)
                  (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
                  (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                  (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
                  (svex-alistlist-check-monotonic my-in-alists)
                  (<= (len test-alists) (len outvars))
                  (svtv-cyclephaselist-unique-i/o-phase spec.cycle-phases)
                  (svarlist-override-p (Svtv-cyclephaselist-keys spec.cycle-phases) nil))
             (overridekeys-envlists-ok params overridekeys
                                       (svtv-spec-pipe-env->phase-envs spec pipe-env)
                                       (svtv-spec-pipe-env->phase-envs spec spec-env)
                                       phase-outs))
    :hints(("Goal" :in-theory (enable svtv-spec-phase-outs->pipe-out
                                      svtv-spec-pipe-env->phase-envs)))))

(define svtv-spec-override-syntax-checks ((spec svtv-spec-p)
                                          (overridekeys svarlist-p)
                                          (params svarlist-p)
                                          (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  (b* (((svtv-spec spec))
       (namemap spec.namemap)
       (in-alists spec.in-alists)
       (test-alists spec.override-test-alists)
       (val-alists spec.override-val-alists)
       (probes spec.probes)
       (outvars (svtv-probealist-outvars spec.probes))
       (my-in-alists (take (len outvars) in-alists))
       ((base-fsm spec.fsm)))
    (and (svtv-override-triplemaplist-syntax-check
          test-alists val-alists probes triplemaps)
         (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
         (no-duplicatesp-each (svex-alist-keys-list test-alists))
         (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
         (svarlist-override-p params :test)
         (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
         (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
         (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
         (svex-alistlist-check-monotonic my-in-alists)
         (<= (len test-alists) (len outvars))
         (svtv-cyclephaselist-unique-i/o-phase spec.cycle-phases)
         (svarlist-override-p (Svtv-cyclephaselist-keys spec.cycle-phases) nil)
         (svex-alist-check-monotonic spec.initst-alist)
         (svarlist-override-p (svex-alist-keys spec.fsm.nextstate) nil)))
  ///
  (defret svtv-spec-overridekey-envlists-ok-when-override-syntax-checks
    (implies (and ok
                  (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env
                                                       (svtv-spec-phase-outs->pipe-out spec phase-outs))
                  (svex-env-<<= (svex-env-extract (svex-alistlist-vars (svtv-spec->in-alists spec))
                                                  pipe-env)
                                spec-env))
             (overridekeys-envlists-ok params overridekeys
                                       (svtv-spec-pipe-env->phase-envs spec pipe-env)
                                       (svtv-spec-pipe-env->phase-envs spec spec-env)
                                       phase-outs)))

  (defretd <fn>-implies
    (implies ok
             (b* (((svtv-spec spec))
                  (namemap spec.namemap)
                  (in-alists spec.in-alists)
                  (test-alists spec.override-test-alists)
                  (val-alists spec.override-val-alists)
                  (probes spec.probes)
                  (outvars (svtv-probealist-outvars spec.probes))
                  (my-in-alists (take (len outvars) in-alists))
                  ((base-fsm spec.fsm)))
               (and (svtv-override-triplemaplist-syntax-check
                     test-alists val-alists probes triplemaps)
                    (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
                    (no-duplicatesp-each (svex-alist-keys-list test-alists))
                    (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
                    (svarlist-override-p params :test)
                    (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
                    (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                    (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
                    (svex-alistlist-check-monotonic my-in-alists)
                    (<= (len test-alists) (len outvars))
                    (svtv-cyclephaselist-unique-i/o-phase spec.cycle-phases)
                    (svarlist-override-p (Svtv-cyclephaselist-keys spec.cycle-phases) nil)
                    (svex-alist-check-monotonic spec.initst-alist)
                    (svarlist-override-p (svex-alist-keys spec.fsm.nextstate) nil))))))


(defthm svex-envlist-<<=-of-nthcdr
  (implies (svex-envlist-<<= x y)
           (svex-envlist-<<= (nthcdr n x) (nthcdr n y)))
  :hints(("Goal" :in-theory (enable svex-envlist-<<= nthcdr))))

(encapsulate nil
  (local (defun ind (phases x y)
           (if (atom x)
               (list phases y)
             (ind phases
                  (nthcdr (max (len phases) 1) x)
                  (nthcdr (max (len phases) 1) y)))))

  (local (defthm svex-env-<<=-nth-nil
           (implies (and (svex-envlist-<<= x y)
                         (<= (len y) (nfix n)))
                    (svex-env-<<= (nth n x) nil))
           :hints (("goal" :use ((:instance svex-envlist-<<=-implies-nth))
                    :in-theory (disable svex-envlist-<<=-implies-nth)))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0) (not (consp x)))))

  (local (defthm svtv-cycle-output-phase-when-not-outputs-captured
           (implies (not (svtv-cyclephaselist-has-outputs-captured phases))
                    (not (svtv-cycle-output-phase phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                             svtv-cyclephaselist-has-outputs-captured)))))

  (local (defthm svtv-cycle-output-phase-linear
           (implies (svtv-cyclephaselist-has-outputs-captured phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase
                                             svtv-cycle-output-phase)))
           :rule-classes (:rewrite :linear)))
  
  (defthm svex-envlist-phase-outputs-extract-cycle-outputs-monotonic
    (implies (svex-envlist-<<= x y)
             (svex-envlist-<<= (svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                               (svex-envlist-phase-outputs-extract-cycle-outputs phases y)))
    :hints(("Goal" :in-theory (e/d (svex-envlist-phase-outputs-extract-cycle-outputs)
                                   (SVEX-ENV-<<=-NIL-MEANS-SIMILAR-TO-NIL))
            :induct (ind phases x y)
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                     (svex-envlist-phase-outputs-extract-cycle-outputs phases y)
                     (:free (a b c) (svex-envlist-<<= (cons a b) c))
                     (:free (y) (svex-envlist-<<= nil y))))
           (and stable-under-simplificationp
                '(:cases ((svtv-cyclephaselist-has-outputs-captured phases)))))))

(defthm svex-env-<<=-of-svtv-probealist-extract
  (implies (svex-envlist-<<= a b)
           (svex-env-<<= (svtv-probealist-extract probes a)
                         (svtv-probealist-extract probes b)))
  :hints(("Goal" :in-theory (enable svtv-probealist-extract))))

(defthm lhs-eval-monotonic
  (implies (svex-env-<<= x y)
           (4vec-<<= (lhs-eval lhs x) (lhs-eval lhs y)))
  :hints(("Goal" :in-theory (enable lhs-eval lhatom-eval lhrange-eval))))

(defthm lhs-eval-zero-monotonic
  (implies (svex-env-<<= x y)
           (4vec-<<= (lhs-eval-zero lhs x) (lhs-eval-zero lhs y)))
  :hints(("Goal" :in-theory (enable lhs-eval-zero lhatom-eval-zero))))


(defthm svtv-name-lhs-map-eval-monotonic
  (implies (svex-env-<<= x y)
           (svex-env-<<= (svtv-name-lhs-map-eval map x)
                         (svtv-name-lhs-map-eval map y)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval))))


(defthm svtv-name-lhs-map-eval-list-monotonic
  (implies (and (svex-envlist-<<= x y)
                (<= (len x) (len y)))
           (svex-envlist-<<= (svtv-name-lhs-map-eval-list map x)
                              (svtv-name-lhs-map-eval-list map y)))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                    svtv-name-lhs-map-eval-list))))

(defsection svex-env-<<=-of-svtv-spec-phase-outs->pipe-out
  (local (defthm len-equal-0
           (equal (Equal (len x) 0) (atom x))))
  (local (defun ind (phases x y)
           (declare (xargs :measure (len x)))
           (if (atom x)
               y
             (ind phases (nthcdr (max 1 (len phases)) x)
                  (nthcdr (max 1 (len phases)) y)))))
  
  (local (defthm svex-envlist-phase-outputs-extract-cycle-outputs-length-monotonic
           (implies (<= (len x) (len y))
                    (<= (len (svex-envlist-phase-outputs-extract-cycle-outputs phases x))
                        (len (svex-envlist-phase-outputs-extract-cycle-outputs phases y))))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)
                   :induct (ind phases x y)
                   :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases x)
                            (svex-envlist-phase-outputs-extract-cycle-outputs phases y))))))

  (defthm svex-env-<<=-of-svtv-spec-phase-outs->pipe-out
    (implies (and (svex-envlist-<<= phase-outs1 phase-outs2)
                  (<= (len phase-outs1) (len phase-outs2)))
             (svex-env-<<= (svtv-spec-phase-outs->pipe-out spec phase-outs1)
                           (svtv-spec-phase-outs->pipe-out spec phase-outs2)))
    :hints(("Goal" :in-theory (enable svtv-spec-phase-outs->pipe-out)
            :do-not-induct t))))


(defsection overridekeys-envlists-ok-of-svex-envlist-x-override

  (local (defthm member-when-svar-override-p*
           (implies (and (svarlist-override-p* x types)
                         (not (svar-override-p* k types)))
                    (not (member-equal k x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p*)))))

  (local (defthm 4vec-<<=-bitmux-id
           (implies (and (4vec-<<= (4vec-bitmux impl-test impl-val spec-val)
                                   spec-val)
                         (4vec-<<= spec-val spec-val2))
                    (4vec-<<= (4vec-bitmux impl-test impl-val spec-val2)
                              spec-val2))
           :hints(("Goal" :in-theory (enable 4vec-bitmux 4vec-<<=))
                  (bitops::logbitp-reasoning))))

  (local (defthm 4vec-<<=-bitmux-then
           (implies (4vec-<<= then then2)
                    (4vec-<<= (4vec-bitmux test then else)
                              (4vec-bitmux test then2 else)))
           :hints(("Goal" :in-theory (enable 4vec-bitmux 4vec-<<=))
                  (bitops::logbitp-reasoning))))
  
  (local (defthm 4vec-override-mux-<<=-when-<<=-spec-val
           (implies (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref)
                         (4vec-<<= spec-val spec-val2))
                    (4vec-override-mux-<<= impl-test impl-val spec-test spec-val2 spec-ref))
           :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=
                                             4vec-bit?!)))))
  
  (defthm svar-overridekeys-envs-ok-of-svex-env-x-override
    (implies (and (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs)
                  (svarlist-override-p* (alist-keys (svex-env-fix base-ins)) '(nil :val))
                  ;; (svarlist-override-p (alist-keys (svex-env-fix base-ins)) nil)
                  (svarlist-override-p params :test))
             (svar-overridekeys-envs-ok v params overridekeys impl-env (svex-env-x-override spec-env base-ins) spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-ok
                                      svex-env-boundp-iff-member-alist-keys
                                      svex-env-lookup-when-not-boundp
                                      member-of-svarlist-change-override
                                      member-when-svar-override-p-diff
                                      member-when-not-svar-override-p
                                      member-svarlist-change-override-when-not-svar-override-p
                                      4vec-<<=-transitive-1
                                      4vec-<<=-transitive-2))))

  (defthm overridekeys-envs-ok-of-svex-env-x-override
    (implies (and (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)
                  (svarlist-override-p* (alist-keys (svex-env-fix base-ins)) '(nil :val))
                  (svarlist-override-p params :test))
             (overridekeys-envs-ok params overridekeys impl-env (svex-env-x-override spec-env base-ins) spec-outs))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthm svar-overridekeys-envs-ok-when-empty/nonoverride
           (implies (and (svarlist-override-p* (alist-keys (svex-env-fix base-ins)) '(nil :val))
                         (svarlist-override-p params :test))
                    (svar-overridekeys-envs-ok v params overridekeys nil base-ins spec-outs))
           
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-ok
                                      svex-env-boundp-iff-member-alist-keys
                                      svex-env-lookup-when-not-boundp
                                      member-of-svarlist-change-override
                                      member-when-svar-override-p-diff
                                      member-when-not-svar-override-p
                                      member-svarlist-change-override-when-not-svar-override-p
                                      4vec-<<=-transitive-1
                                      4vec-<<=-transitive-2)))))

  (defthm overridekeys-envs-ok-when-empty/nonoverride
    (implies (and (svarlist-override-p* (alist-keys (svex-env-fix base-ins)) '(nil :val))
                  (svarlist-override-p params :test))
             (overridekeys-envs-ok params overridekeys nil base-ins spec-outs))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm overridekeys-envlists-ok-when-empty/nonoverride
    (implies (and (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val))
                  (svarlist-override-p params :test))
             (overridekeys-envlists-ok params overridekeys nil base-ins spec-outs))
    :hints(("Goal" :in-theory (enable overridekeys-envlists-ok  svex-envlist-all-keys
                                      svex-envlist-fix))))
  
  (defthm overridekeys-envlists-ok-of-svex-envlist-x-override
    (implies (and (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)
                  (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val))
                  (svarlist-override-p params :test))
             (overridekeys-envlists-ok params overridekeys impl-envs (svex-envlist-x-override spec-envs base-ins) spec-outs))
    :hints(("Goal" :in-theory (enable overridekeys-envlists-ok svex-envlist-x-override svex-envlist-all-keys
                                      svex-envlist-fix)))))



(define svtv-spec-stimulus-equiv ((impl svtv-spec-p)
                                  (spec svtv-spec-p))
  (b* (((svtv-spec impl))
       ((svtv-spec spec))
       ((base-fsm impl.fsm))
       ((base-fsm spec.fsm)))
    (and (svtv-spec-equiv impl (change-svtv-spec spec :fsm impl.fsm))
         (equal (svex-alist-keys spec.fsm.nextstate)
                (svex-alist-keys impl.fsm.nextstate))))
  ///
  (defequiv svtv-spec-stimulus-equiv)

  (defcong svtv-spec-stimulus-equiv equal (svtv-spec-phase-outs->pipe-out x phase-outs) 1
    :hints(("Goal" :in-theory (enable svtv-spec-phase-outs->pipe-out))))

  (defcong svtv-spec-stimulus-equiv equal (svtv-spec-pipe-env->phase-envs x env) 1
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs))))

  (defcong svtv-spec-stimulus-equiv equal (svtv-spec->initst-alist x) 1)
  (defcong svtv-spec-stimulus-equiv equal (svtv-spec->in-alists x) 1)

  (defcong svtv-spec-stimulus-equiv equal (svtv-spec-override-syntax-checks x overridekeys params triplemaps) 1
    :hints(("Goal" :in-theory (enable svtv-spec-override-syntax-checks)))))


(defsection override-transparency-of-svtv-spec-run
  (local (defthm test/val-intersectp
           (implies (svarlist-override-p params :test)
                    (not (intersectp-equal (svarlist-fix params) (svarlist-change-override overridekeys :val))))
           :hints(("Goal" :in-theory (enable svarlist-change-override svarlist-override-p
                                             svarlist-fix
                                             member-of-svarlist-change-override)))))

  (local (defthm test/nil-intersectp
           (implies (and (svarlist-override-p params :test)
                         (svarlist-override-p nskeys nil))
                    (not (intersectp-equal (svarlist-fix params) nskeys)))
           :hints(("Goal" :in-theory (enable svarlist-change-override svarlist-override-p
                                             svarlist-fix
                                             member-when-svar-override-p-diff)))))

  (local (defthm svex-env-<<=-of-svex-env-x-override
           (implies (svex-env-<<= x y)
                    (svex-env-<<= x (svex-env-x-override y z)))
           :hints(("Goal" :in-theory (enable svex-env-<<=-transitive-1
                                             svex-env-<<=-transitive-2)))))

  (local (defthm max->=-first
           (<= a (max a b))))
  (local (in-theory (disable max)))
  
  (defthm override-transparency-of-svtv-spec-run
    (b* (((svtv-spec spec))
         (in-alists spec.in-alists)
         (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
         (impl-run (svtv-spec-run spec pipe-env)))
      (implies (and (svtv-spec-override-syntax-checks spec overridekeys params triplemaps)
                    (base-fsm-overridekey-transparent-p spec.fsm overridekeys)
                    (base-fsm-partial-monotonic params spec.fsm)

                    (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                    (svex-env-<<= (svex-env-extract (svex-alistlist-vars in-alists) pipe-env)
                                  spec-env)
                    (svex-env-<<= (svex-env-extract (svex-alist-vars spec.initst-alist) pipe-env)
                                  spec-env)

                    (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val)))
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svtv-spec-override-syntax-checks-implies))))

  (local (defthm svex-alist-keys-of-nextstate-under-svtv-spec-stimulus-equiv
           (implies (svtv-spec-stimulus-equiv x y)
                    (equal (SVEX-ALIST-KEYS (BASE-FSM->NEXTSTATE (SVTV-SPEC->FSM x)))
                           (SVEX-ALIST-KEYS (BASE-FSM->NEXTSTATE (SVTV-SPEC->FSM y)))))
           :hints (("goal" :in-theory (enable svtv-spec-stimulus-equiv)))
           :rule-classes (:congruence
                          (:rewrite :corollary
                           (implies (svtv-spec-stimulus-equiv x y)
                                    (equal (equal (SVEX-ALIST-KEYS (BASE-FSM->NEXTSTATE (SVTV-SPEC->FSM x)))
                                                  (SVEX-ALIST-KEYS (BASE-FSM->NEXTSTATE (SVTV-SPEC->FSM y))))
                                           t))))))

  (local (defthm intersectp-params-nextate-when-svtv-spec-override-syntax-checks
           (implies (and (svtv-spec-override-syntax-checks impl overridekeys params triplemaps)
                         (svtv-spec-stimulus-equiv impl spec))
                    (and (not (intersectp-equal (svarlist-fix params)
                                                (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm spec)))))
                         (svarlist-override-p (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm spec))) nil)))
           :hints(("Goal" :in-theory (enable svtv-spec-stimulus-equiv
                                             svtv-spec-override-syntax-checks)))))
  
  (defthm override-transparency-of-svtv-spec-run-abstraction
    (b* (((svtv-spec spec))
         ((svtv-spec impl))
         (in-alists spec.in-alists)
         (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
         (impl-run (svtv-spec-run impl pipe-env)))
      (implies (and (svtv-spec-override-syntax-checks spec overridekeys params triplemaps)
                    (base-fsm-overridekey-transparent-p spec.fsm overridekeys)
                    (base-fsm-partial-monotonic params spec.fsm)
                    (base-fsm-partial-monotonic params impl.fsm)
                    (base-fsm-<<= impl.fsm spec.fsm)
                    (svtv-spec-stimulus-equiv impl spec)
                    
                    (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                    (svex-env-<<= (svex-env-extract (svex-alistlist-vars in-alists) pipe-env)
                                  spec-env)
                    (svex-env-<<= (svex-env-extract (svex-alist-vars spec.initst-alist) pipe-env)
                                  spec-env)
                    
                    (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val)))
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svtv-spec-override-syntax-checks-implies)))))

                    


             
    







