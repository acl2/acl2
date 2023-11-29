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

(include-book "design-fsm")
(include-book "../svex/fixpoint-override")
(include-book "../svex/compose-theory-fixpoint")
(include-book "../svex/compose-theory-ovmonotonicity")
(include-book "../svex/compose-theory-monotonicity")
(include-book "svtv-stobj-export")
;; (include-book "svtv-stobj-pipeline-monotonicity")
(include-book "fsm-override-transparency")
;; (include-book "svtv-spec")
(include-book "../svex/depends")
(local (include-book "../svex/compose-theory-deps"))
(local (include-book "../svex/alist-thms"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (in-theory (disable signed-byte-p)))
(local (std::add-default-post-define-hook :fix))
(local (defthm signed-byte-p-of-loghead
         (implies (natp w)
                  (signed-byte-p (+ 1 w) (loghead w x)))
         :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                                (size w) (size1 w) (i x)))
                  :in-theory (e/d (unsigned-byte-p signed-byte-p)
                                  (unsigned-byte-p-of-loghead))))))

(defsection svex-monotonify-of-svex-concat

  (defthm svex-concat-under-svex-eval-equiv
    (svex-eval-equiv (svex-concat w x y)
                     (svcall concat (svex-quote (2vec (nfix w))) x y))
    :hints(("Goal" :in-theory (enable svex-eval-equiv
                                      svex-apply
                                      svex-eval))))

  (local (defthm svex-mono-eval-when-quotep
           (implies (svex-case x :quote)
                    (equal (svex-mono-eval x env) (svex-quote->val x)))
           :hints(("Goal" :in-theory (enable svex-mono-eval)))))

  (local (defthm equal-of-len
           (implies (syntaxp (quotep n))
                    (equal (Equal (len x) n)
                           (if (eql n 0)
                               (atom x)
                             (and (consp x)
                                  (posp n)
                                  (equal (len (cdr x)) (1- n))))))))

  (local (defret svex-mono-eval-when-match-concat
           (implies matchedp
                    (equal (svex-mono-eval x env)
                           (4vec-concat (2vec width)
                                        (svex-mono-eval lsbs env)
                                        (svex-mono-eval msbs env))))
           :hints(("Goal" :in-theory (enable match-concat
                                             svex-mono-eval
                                             svex-call-mono-eval
                                             svex-fn/args-mono-eval
                                             svex-apply
                                             4veclist-nth-safe
                                             svexlist-mono-eval)))
           :fn match-concat))

  (local (defthm logapp-of-logext
           (implies (and (natp w)
                         (integerp w2)
                         (<= w w2))
                    (equal (logapp w (logext w2 x) y)
                           (logapp w x y)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm 4vec-concat-of-4vec-sign-ext
           (implies (and (natp w)
                         (integerp w2)
                         (<= w w2))
                    (equal (4vec-concat (2vec w) (4vec-sign-ext (2vec w2) x) y)
                           (4vec-concat (2vec w) x y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-sign-ext)))))



  (local (defthm 4vec-concat-of-4vec-zero-ext
           (implies (and (natp w)
                         (integerp w2)
                         (<= w w2))
                    (equal (4vec-concat (2vec w) (4vec-zero-ext (2vec w2) x) y)
                           (4vec-concat (2vec w) x y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext)))))

  (local (defret svex-mono-eval-when-match-ext
           (implies matchedp
                    (equal (svex-mono-eval x env)
                           (if sign-extend-p
                               (4vec-sign-ext (2vec width) (svex-mono-eval lsbs env))
                             (4vec-zero-ext (2vec width) (svex-mono-eval lsbs env)))))
           :hints(("Goal" :in-theory (enable match-ext
                                             svex-mono-eval
                                             svex-call-mono-eval
                                             svex-fn/args-mono-eval
                                             svex-apply
                                             4veclist-nth-safe
                                             svexlist-mono-eval)))
           :fn match-ext))

  (defthm svex-mono-eval-of-svex-concat
    (equal (svex-mono-eval (svex-concat w x y) env)
           (4vec-concat (2vec (nfix w))
                        (svex-mono-eval x env)
                        (svex-mono-eval y env)))
    :hints (("goal" :induct (svex-concat w x y)
             :in-theory (enable svex-apply (:i svex-concat))
             :expand ((svex-concat w x y)
                      (svex-concat 0 x y)
                      (:free (fn args) (svex-mono-eval (svex-call fn args) env))
                      (:free (val) (svex-mono-eval (svex-quote val) env))
                      (:free (fn args) (svex-call-mono-eval (svex-call fn args) env))
                      (:free (fn args) (svex-fn/args-mono-eval fn args env))
                      (:free (a b) (svexlist-mono-eval (cons a b) env))
                      (:free (val) (svex-monotonify (svex-quote val)))))))

  (defthm svex-monotonify-of-svex-concat
    (svex-eval-equiv (svex-monotonify (svex-concat w x y))
                     (svex-concat w (svex-monotonify x) (svex-monotonify y)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))

(define var-decl-map->svar-width-map ((x var-decl-map-p))
  :returns (map svar-width-map-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x) (+ 1 (wire->width (cdar x))))
              (var-decl-map->svar-width-map (cdr x)))
      (var-decl-map->svar-width-map (cdr x))))
  ///
  (defret lookup-of-<fn>
    (equal (hons-assoc-equal v map)
           (and (hons-assoc-equal v (var-decl-map-fix x))
                (cons v (+ 1 (wire->width (cdr (hons-assoc-equal v (var-decl-map-fix x))))))))
    :hints(("Goal" :in-theory (enable var-decl-map-fix))))

  (defthm svex-width-limited-p-of-concat
    (implies (natp w)
             (svex-width-limited-p (+ 1 w) (svcall concat (svex-quote (2vec w)) x 0)))
    :hints(("Goal" :in-theory (enable svex-width-limited-p
                                      svex-apply
                                      4vec-width-p
                                      4vec-concat))))

  (defret svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls
    (implies (and (svex-alist-width-limited-p map acc)
                  (no-duplicatesp-equal (svex-alist-keys alist))
                  (no-duplicatesp-equal (svex-alist-keys acc))
                  (not (intersectp-equal (svex-alist-keys alist)
                                         (svex-alist-keys acc))))
             (svex-alist-width-limited-p map
                                         (svex-alist-truncate-by-var-decls alist x acc)))
    :hints(("Goal" :in-theory (enable svex-alist-truncate-by-var-decls
                                      svex-alist-width-limited-p-rec-when-no-duplicate-keys
                                      svex-alist-keys)
            :induct (svex-alist-truncate-by-var-decls alist x acc))))

  (defret svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls-monotonify
    (implies (and (svex-alist-width-limited-p map (svex-alist-monotonify acc))
                  (no-duplicatesp-equal (svex-alist-keys alist))
                  (no-duplicatesp-equal (svex-alist-keys acc))
                  (not (intersectp-equal (svex-alist-keys alist)
                                         (svex-alist-keys acc))))
             (svex-alist-width-limited-p map
                                         (svex-alist-monotonify
                                          (svex-alist-truncate-by-var-decls alist x acc))))
    :hints(("Goal" :in-theory (e/d (svex-alist-monotonify
                                      svex-alist-truncate-by-var-decls
                                      svex-alist-width-limited-p-rec-when-no-duplicate-keys
                                      svex-alist-keys))
            :induct (svex-alist-truncate-by-var-decls alist x acc))))

  (defthm svex-alist-width-of-svex-alist-truncate-by-var-decls
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (svex-alist-width (svex-alist-truncate-by-var-decls x var-map nil)))
    :hints (("goal" :use ((:instance svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls
                           (acc nil) (alist x) (x var-map)))
             :in-theory (e/d (svex-alist-width-limited-p-rec-when-no-duplicate-keys)
                             (svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls)))))

  (defthm svex-alist-width-of-svex-alist-truncate-by-var-decls-monotonify
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (svex-alist-width (svex-alist-monotonify (svex-alist-truncate-by-var-decls x var-map nil))))
    :hints (("goal" :use ((:instance svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls-monotonify
                           (acc nil) (alist x) (x var-map)))
             :in-theory (e/d (svex-alist-width-limited-p-rec-when-no-duplicate-keys)
                             (svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls-monotonify)))))

  (local (in-theory (enable var-decl-map-fix))))







(local (in-theory (disable fast-alist-clean)))

;; (defthmd svex-alist-keys-of-svex-alist-truncate-by-var-decls
;;   (equal (svex-alist-keys (svex-alist-truncate-by-var-decls x var-decls acc))
;;          (revappend (intersection-equal (svex-alist-keys x) (alist-keys (var-decl-map-fix var-decls)))
;;                     (svex-alist-keys acc)))
;;   :hints(("Goal" :in-theory (enable svex-alist-truncate-by-var-decls
;;                                     svex-alist-keys))))


;; (local (defthm member-of-rev
;;          (iff (member-equal v (rev x))
;;               (member-equal v x))))
;; (local (Defthm no-duplicatesp-equal-of-rev
;;          (implies (no-duplicatesp-equal x)
;;                   (no-duplicatesp-equal (rev x)))
;;          :hints(("Goal" :in-theory (enable rev)))))



(defthm svex-alist-width-of-svtv-normalize-assigns
  (svex-alist-width (flatnorm-res->assigns
                     (svtv-normalize-assigns flatten aliases setup)))
  :hints(("Goal" :in-theory (enable svtv-normalize-assigns
                                    svex-normalize-assigns)
          :do-not-induct t)))




(defthmd svar-override-triplelist->override-alist-of-svarlist-to-override-triples
  (implies (svarlist-override-p x nil)
           (equal (svar-override-triplelist->override-alist
                   (svarlist-to-override-triples x))
                  (svarlist-to-override-alist x)))
  :hints(("Goal" :in-theory (enable svarlist-to-override-alist
                                    svar-change-override
                                    svarlist-override-p
                                    svar-override-p
                                    svar-override-triplelist->override-alist
                                    svarlist-to-override-triples))))



;; (define svtv-override-varlist-muxes-agree ((vars svarlist-p)
;;                                            (impl-env svex-env-p)
;;                                            (spec-env svex-env-p)
;;                                            (spec-outs svex-env-p))
;;   (if (atom vars)
;;       t
;;     (and (b* ((refvar   (svar-change-override (car vars) nil))
;;               (testvar  (svar-change-override (car vars) :test))
;;               (valvar   (svar-change-override (car vars) :val)))
;;            (4vec-override-mux-agrees (svex-env-lookup testvar impl-env)
;;                                      (svex-env-lookup valvar impl-env)
;;                                      (svex-env-lookup testvar spec-env)
;;                                      (svex-env-lookup valvar spec-env)
;;                                      (svex-env-lookup refvar spec-outs)))
;;          (svtv-override-varlist-muxes-agree (cdr vars) impl-env spec-env spec-outs)))
;;   ///
;;   (defthm svar-override-triplelist-muxes-agree-of-svarlist-to-override-triples
;;     (equal (svar-override-triplelist-muxes-agree (svarlist-to-override-triples vars) impl-env spec-env spec-outs)
;;            (svtv-override-varlist-muxes-agree vars impl-env spec-env spec-outs))
;;     :hints(("Goal" :in-theory (enable svar-override-triplelist-muxes-agree
;;                                       svarlist-to-override-triples
;;                                       svar-override-triple-mux-agrees)))))


(local (in-theory (disable hons-dups-p)))

(defthm svex-alist-monotonic-p-implies-monotonic-on-vars
  (implies (svex-alist-monotonic-p x)
           (svex-alist-monotonic-on-vars v x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-on-vars))))

(local (defthm svex-alist-monotonic-p-of-svex-alist-monotonify
         (svex-alist-monotonic-p (svex-alist-monotonify x))
         :hints(("Goal" :in-theory (enable svex-alist-monotonic-p)))))
(local (defthm svex-alist-monotonic-p-of-svex-alist-monotonify-equiv
         (implies (svex-alist-eval-equiv x (svex-alist-monotonify y))
                  (svex-alist-monotonic-p x))))

(local (defthm svex-monotonic-p-of-zerox-var
         (svex-monotonic-p (svcall zerox (svex-quote w) (svex-var name)))
         :hints(("Goal" :in-theory (enable svex-monotonic-p
                                           svex-apply svex-eval)))))

(defthm svex-alist-monotonic-p-of-cons
  (implies (and (svex-alist-monotonic-p x)
                (svex-monotonic-p val))
           (svex-alist-monotonic-p (cons (cons key val) x)))
  :hints (("goal" :expand ((:with svex-alist-monotonic-in-terms-of-lookup
                            (svex-alist-monotonic-p (cons (cons key val) x))))
           :in-theory (enable svex-lookup-of-cons))))

(defthm svex-alist-monotonic-p-nil
  (svex-alist-monotonic-p nil)
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-p))))


(defthm svex-alist-monotonic-p-of-svar-map-truncate-by-var-decls
  (implies (svex-alist-monotonic-p acc)
           (svex-alist-monotonic-p (svar-map-truncate-by-var-decls map decls acc)))
  :hints(("Goal" :in-theory (enable svar-map-truncate-by-var-decls))))

(defthm svex-alist-monotonic-p-of-svtv-normalize-assigns
  (implies (flatnorm-setup->monotonify setup)
           (b* (((flatnorm-res res) (svtv-normalize-assigns flatten aliases setup)))
             (and (svex-alist-monotonic-p res.assigns)
                  (svex-alist-monotonic-p res.delays))))
  :hints(("Goal" :in-theory (enable svtv-normalize-assigns))
         (and stable-under-simplificationp
              '(:in-theory (enable svex-normalize-assigns)))))


(local
 (defthm svex-alist-monotonic-p-of-svtv-normalize-assigns-equiv
   (implies (flatnorm-setup->monotonify setup)
            (b* (((flatnorm-res res) (svtv-normalize-assigns flatten aliases setup)))
              (and (implies (svex-alist-eval-equiv x res.assigns)
                            (svex-alist-monotonic-p x))
                   (implies (svex-alist-eval-equiv x res.delays)
                            (svex-alist-monotonic-p x))
                   (implies (equal x res.delays)
                            (svex-alist-monotonic-p x)))))
   :hints(("Goal" :in-theory (enable svtv-normalize-assigns))
          (and stable-under-simplificationp
               '(:in-theory (enable svex-normalize-assigns))))))




;(local (in-theory (disable SVAR-OVERRIDE-TRIPLELIST-ENV-OK-IN-TERMS-OF-SVEX-OVERRIDE-TRIPLELIST-ENV-OK)))

(defthm svarlist-addr-p-of-svtv-assigns-override-vars
  (implies (svarlist-addr-p (svex-alist-keys assigns))
           (svarlist-addr-p (svtv-assigns-override-vars assigns config)))
  :hints(("Goal" :use svtv-assigns-override-vars-subset-of-keys)))

(local (defthm no-duplicatesp-of-intersection
         (implies (no-duplicatesp-equal x)
                  (no-duplicatesp-equal (intersection-equal x y)))
         :hints(("Goal" :in-theory (enable intersection-equal)))))

(local (defthm no-duplicatesp-of-set-difference
         (implies (no-duplicatesp-equal x)
                  (no-duplicatesp-equal (set-difference-equal x y)))
         :hints(("Goal" :in-theory (enable set-difference-equal)))))

(defthm no-duplicatesp-of-svtv-assigns-override-vars
  (implies (no-duplicatesp-equal (svex-alist-keys assigns))
           (no-duplicatesp-equal (svtv-assigns-override-vars assigns config)))
  :hints(("Goal" :in-theory (enable svtv-assigns-override-vars))))


(local
 (defthm set-difference-equal-self
   (equal (set-difference-equal x x)
          nil)))

(local
 (defthm svex-envs-agree-nil
   (svex-envs-agree nil x y)
   :hints(("Goal" :in-theory (enable svex-envs-agree)))))






;; (defsection svex-partial-monotonic-implies-monotonic-on-vars
;;   (local (defthm svex-env-extract-when-agree-except-non-intersecting
;;            (implies (and (svex-envs-agree-except vars x y)
;;                          (not (intersectp-equal (svarlist-fix params)
;;                                                 (svarlist-fix vars))))
;;                     (equal (svex-env-extract params x)
;;                            (svex-env-extract params y)))
;;            :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix
;;                                              svex-envs-agree-except-implies)))))

;;   (defthm svex-partial-monotonic-implies-monotonic-on-vars
;;     (implies (and (svex-partial-monotonic params x)
;;                   (not (intersectp-equal (svarlist-fix params) (svarlist-fix vars))))
;;              (svex-monotonic-on-vars vars x))
;;     :hints (("goal" :expand ((svex-monotonic-on-vars vars x))
;;              :use ((:instance eval-when-svex-partial-monotonic
;;                     (param-keys params)
;;                     (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars x)))
;;                     (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars x)))))
;;              :in-theory (disable eval-when-svex-partial-monotonic))))

;;   (defthm svexlist-partial-monotonic-implies-monotonic-on-vars
;;     (implies (and (svexlist-partial-monotonic params x)
;;                   (not (intersectp-equal (svarlist-fix params) (svarlist-fix vars))))
;;              (svexlist-monotonic-on-vars vars x))
;;     :hints (("goal" :expand ((svexlist-monotonic-on-vars vars x))
;;              :use ((:instance eval-when-svexlist-partial-monotonic
;;                     (param-keys params)
;;                     (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars x)))
;;                     (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars x)))))
;;              :in-theory (disable eval-when-svexlist-partial-monotonic))))

;;   (defthm svex-alist-partial-monotonic-implies-monotonic-on-vars
;;     (implies (and (svex-alist-partial-monotonic params x)
;;                   (not (intersectp-equal (svarlist-fix params) (svarlist-fix vars))))
;;              (svex-alist-monotonic-on-vars vars x))
;;     :hints (("goal" :expand ((svex-alist-monotonic-on-vars vars x))
;;              :use ((:instance eval-when-svex-alist-partial-monotonic
;;                     (param-keys params)
;;                     (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars x)))
;;                     (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars x)))))
;;              :in-theory (disable eval-when-svex-alist-partial-monotonic))))

;;   (local
;;    (defthm subset-diff-agree-except-lemma
;;      (implies (and (equal (svex-env-extract params env1)
;;                           (svex-env-extract params env2))
;;                    (subsetp (set-difference-equal (svarlist-fix vars2)
;;                                                   (svarlist-fix params))
;;                             (svarlist-fix vars)))
;;               (svex-envs-agree-except vars (svex-env-extract vars2 env1) (svex-env-extract vars2 env2)))
;;      :hints(("Goal" :in-theory (e/d (svex-envs-agree-except-by-witness))
;;              :restrict ((svex-env-lookup-of-svex-env-extract ((vars vars2))))
;;              :use ((:instance svex-env-lookup-of-svex-env-extract
;;                     (v (svex-envs-agree-except-witness vars (svex-env-extract vars2 env1) (svex-env-extract vars2 env2)))
;;                     (vars params)
;;                     (env env1))
;;                    (:instance svex-env-lookup-of-svex-env-extract
;;                     (v (svex-envs-agree-except-witness vars (svex-env-extract vars2 env1) (svex-env-extract vars2 env2)))
;;                     (vars params)
;;                     (env env2)))
;;              :do-not-induct t))))

;;   (defthm svex-monotonic-on-vars-implies-partial-monotonic
;;     (implies (and (svex-monotonic-on-vars vars x)
;;                   (subsetp (set-difference-equal (svex-vars x)
;;                                                  (svarlist-fix params))
;;                            (svarlist-fix vars)))
;;              (svex-partial-monotonic params x))
;;     :hints (("goal" :expand ((:with svex-partial-monotonic-by-eval (svex-partial-monotonic params x)))
;;              :use ((:instance svex-monotonic-on-vars-necc
;;                     (env1 (svex-env-extract (svex-vars x) (mv-nth 0 (svex-partial-monotonic-eval-witness params x))))
;;                     (env2 (svex-env-extract (svex-vars x) (mv-nth 1 (svex-partial-monotonic-eval-witness params x)))))))))

;;   (defthm svexlist-monotonic-on-vars-implies-partial-monotonic
;;     (implies (and (svexlist-monotonic-on-vars vars x)
;;                   (subsetp (set-difference-equal (svexlist-vars x)
;;                                                  (svarlist-fix params))
;;                            (svarlist-fix vars)))
;;              (svexlist-partial-monotonic params x))
;;     :hints (("goal" :expand ((:with svexlist-partial-monotonic-by-eval (svexlist-partial-monotonic params x)))
;;              :use ((:instance svexlist-monotonic-on-vars-necc
;;                     (env1 (svex-env-extract (svexlist-vars x) (mv-nth 0 (svexlist-partial-monotonic-eval-witness params x))))
;;                     (env2 (svex-env-extract (svexlist-vars x) (mv-nth 1 (svexlist-partial-monotonic-eval-witness params x)))))))))

;;   (local (in-theory (enable svexlist-vars-of-svex-alist-vals)))
  
;;   (defthm svex-alist-monotonic-on-vars-implies-partial-monotonic
;;     (implies (and (svex-alist-monotonic-on-vars vars x)
;;                   (subsetp (set-difference-equal (svex-alist-vars x)
;;                                                  (svarlist-fix params))
;;                            (svarlist-fix vars)))
;;              (svex-alist-partial-monotonic params x))
;;     :hints (("goal" :expand ((:with svex-alist-partial-monotonic-by-eval (svex-alist-partial-monotonic params x)))
;;              :use ((:instance svex-alist-monotonic-on-vars-necc
;;                     (env1 (svex-env-extract (svex-alist-vars x) (mv-nth 0 (svex-alist-partial-monotonic-eval-witness params x))))
;;                     (env2 (svex-env-extract (svex-alist-vars x) (mv-nth 1 (svex-alist-partial-monotonic-eval-witness params x))))))))))



;; (defsection svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys


;;   (local (defthm cdr-under-svex-alist-eval-equiv-when-not-consp-car
;;            (implies (not (consp (car y)))
;;                     (svex-alist-eval-equiv (cdr y) y))
;;            :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
;;                                              svex-lookup
;;                                              svex-alist-fix)))))

;;   (local (defthm cdr-under-svex-alist-eval-equiv-when-not-svar-p-caar
;;            (implies (not (svar-p (caar y)))
;;                     (svex-alist-eval-equiv (cdr y) y))
;;            :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
;;                                              svex-lookup
;;                                              svex-alist-fix)))))


;;   (local (defthm svex-alist-eval-equiv-expand-when-same-keys
;;            (implies (and (consp y)
;;                          (consp (car y))
;;                          (svar-p v)
;;                          (equal (caar y) v)
;;                          (not (svex-lookup v (cdr y)))
;;                          (not (svex-lookup v x)))
;;                     (equal (svex-alist-eval-equiv (cons (cons v val) x) y)
;;                            (and (svex-eval-equiv val (cdar y))
;;                                 (svex-alist-eval-equiv x (cdr y)))))
;;            :hints (("goal" :cases ((svex-alist-eval-equiv (cons (cons v val) x) y))
;;                     :in-theory (e/d (svex-lookup-redef))
;;                     :do-not-induct t)
;;                    (and stable-under-simplificationp
;;                         (b* ((lit (assoc 'svex-alist-eval-equiv clause))
;;                              (?wit `(svex-alist-eval-equiv-witness . ,(cdr lit))))
;;                           (if lit
;;                               `(:expand (,lit)
;;                                 :use ((:instance svex-alist-eval-equiv-necc
;;                                        (var ,wit) (x (cons (cons (caar y) val) x)) (y y)))
;;                                 :in-theory (e/d (svex-lookup-redef)

;;                                                 (SVEX-ALIST-EVAL-EQUIV-IMPLIES-IFF-SVEX-LOOKUP-2
;;                                                  SVEX-ALIST-SAME-KEYS-IMPLIES-IFF-SVEX-LOOKUP-2
;;                                                  svex-alist-eval-equiv-necc
;;                                                  svex-alist-eval-equiv-implies-svex-eval-equiv-svex-lookup-2))
;;                                 )
;;                             `(:use ((:instance svex-alist-eval-equiv-necc
;;                                      (var (caar y)) (x (cons (cons (caar y) val) x)) (y y)))
;;                               :in-theory (e/d (svex-lookup-redef)
;;                                               (SVEX-ALIST-EVAL-EQUIV-IMPLIES-IFF-SVEX-LOOKUP-2
;;                                                SVEX-ALIST-SAME-KEYS-IMPLIES-IFF-SVEX-LOOKUP-2
;;                                                svex-alist-eval-equiv-necc
;;                                                svex-alist-eval-equiv-implies-svex-eval-equiv-svex-lookup-2)))))))
;;            :otf-flg t))

;;   (local (defthm svex-width-of-lookup-when-svex-alist-width-aux
;;            (implies (and (svex-alist-width-aux x)
;;                          (svex-lookup k x))
;;                     (svex-width (svex-lookup k x)))
;;            :hints(("Goal" :in-theory (enable svex-lookup-redef
;;                                              svex-alist-width-aux
;;                                              svex-width-sum)))))

;;   (local (defthm svex-width-of-lookup-when-svex-alist-width
;;            (implies (and (svex-alist-width x)
;;                          (svex-lookup k x))
;;                     (svex-width (svex-lookup k x)))
;;            :hints(("Goal" :use ((:instance svex-width-of-lookup-when-svex-alist-width-aux
;;                                  (x (fast-alist-clean (svex-alist-fix x)))))
;;                    :in-theory (e/d (svex-alist-width) (svex-width-of-lookup-when-svex-alist-width-aux))))))

;;   (local (defthm svex-width-of-x
;;            (equal (svex-width (svex-x)) 1)
;;            :hints (("goal" :use ((:instance svex-width-limited-p (width 1) (x (svex-x))))
;;                     :in-theory (enable svex-width-unique)))))


;;   ;; (local
;;   ;;  (defthmd svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys-lemma
;;   ;;    (implies (and (svex-alist-width x)
;;   ;;                  (svex-alist-eval-equiv (svex-alist-extract (svex-alist-keys y) x) y)
;;   ;;                  (no-duplicatesp-equal (svex-alist-keys y)))
;;   ;;             (svex-alist-width y))
;;   ;;    :hints (("goal" :induct (svex-alist-keys y)
;;   ;;             :in-theory (enable svex-alist-keys svex-alist-extract
;;   ;;                                svex-alist-width
;;   ;;                                svex-width-sum)))))

;;   (local (defthm svex-alist-eval-equiv-of-extract-when-svex-alist-eval-equiv
;;            (implies (svex-alist-eval-equiv x y)
;;                     (svex-alist-eval-equiv (svex-alist-extract (svex-alist-keys y) x) y))
;;            :hints (("Goal" :expand ((svex-alist-eval-equiv (svex-alist-extract (svex-alist-keys x) x) x))))))

;;   (defthmd svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys
;;     (implies (and (no-duplicatesp-equal (svex-alist-keys y))
;;                   (svex-alist-eval-equiv x y)
;;                   (svex-alist-width x))
;;              (svex-alist-width y))
;;     :hints (("goal" :use svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys-lemma))))


;; (encapsulate nil
;;   (local (defthm testvar-of-lookup-refvar-member-of-testvars
;;            (implies (member-equal (svar-fix v) (svar-override-triplelist->refvars x))
;;                     (member-equal (svar-override-triple->testvar
;;                                    (svar-override-triplelist-lookup-refvar v x))
;;                                   (svar-override-triplelist->testvars x)))
;;            :hints(("Goal" :in-theory (enable svar-override-triplelist->testvars
;;                                              svar-override-triplelist-lookup-refvar
;;                                              svar-override-triplelist->refvars)))))


;;   (defthm svex-alist-partial-monotonic-of-svar-override-triplelist->override-alist
;;     (svex-alist-partial-monotonic (svar-override-triplelist->testvars x)
;;                                   (svar-override-triplelist->override-alist x))
;;     :hints(("Goal" :in-theory (enable svex-alist-partial-monotonic-by-eval
;;                                       svex-apply
;;                                       svex-eval))
;;            (and stable-under-simplificationp
;;                 (b* ((envs '(svex-alist-partial-monotonic-eval-witness (svar-override-triplelist->testvars x)
;;                                                                        (svar-override-triplelist->override-alist x)))
;;                      (ev1 `(svex-alist-eval (svar-override-triplelist->override-alist x) (mv-nth 0 ,envs)))
;;                      (ev2 `(svex-alist-eval (svar-override-triplelist->override-alist x) (mv-nth 1 ,envs)))
;;                      (key `(svex-env-<<=-witness ,ev1 ,ev2))
;;                      (testvar `(svar-override-triple->testvar (svar-override-triplelist-lookup-refvar ,key x))))
;;                   `(:expand ((svex-env-<<= ,ev1 ,ev2))
;;                     :use ((:instance svex-env-lookup-of-svex-env-extract
;;                            (v ,testvar)
;;                            (vars (svar-override-triplelist->testvars x))
;;                            (env (mv-nth 0 ,envs)))
;;                           (:instance svex-env-lookup-of-svex-env-extract
;;                            (v ,testvar)
;;                            (vars (svar-override-triplelist->testvars x))
;;                            (env (mv-nth 1 ,envs))))
;;                     :in-theory (e/d (svex-apply
;;                                      svex-eval)
;;                                     (svex-env-lookup-of-svex-env-extract))))))))



(local (in-theory (disable bitops::logapp-of-i-0)))

(local (defthm equal-logapp
         (equal (equal (logapp n x y) z)
                (and (integerp z)
                     (equal (loghead n x) (loghead n z))
                     (equal (ifix y) (logtail n z))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthmd self-equal-change-override
         (equal (equal (svar-fix x) (svar-change-override x type))
                (svar-override-p x type))
         :hints(("Goal" :in-theory (enable svar-override-p svar-change-override
                                           svar-overridetype-fix-possibilities)))))

(local (defthmd svar-override-p-when-equal-change-override
         (implies (equal (svar-fix x) (svar-change-override y type))
                  (svar-override-p x type))
         :hints(("Goal" :in-theory (enable svar-override-p svar-change-override
                                           svar-overridetype-fix-possibilities)))))



(local (defthmd svar-override-p-when-member-change-override
         (implies (member-equal (svar-fix x) (svarlist-change-override y type))
                  (svar-override-p x type))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           svar-override-p-when-equal-change-override)))))

(local (defthmd svar-override-p-when-member-change-override-no-fix
         (implies (member-equal x (svarlist-change-override y type))
                  (svar-override-p x type))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           svar-override-p-when-equal-change-override)))))

(local (defthmd member-svar-change-override-of-svarlist-change-override
         (implies (syntaxp (not (and (equal type1 ''nil)
                                     (equal type2 ''nil))))
                  (iff (member-equal (svar-change-override v type1)
                                     (svarlist-change-override x type2))
                       (and (svar-overridetype-equiv type1 type2)
                            (member-equal (svar-change-override v nil)
                                          (svarlist-change-override x nil)))))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           equal-of-svar-change-override)))))

(local
 (defthm intersectp-equal-of-change-override
   (implies (syntaxp (not (and (equal type1 ''nil)
                               (equal type2 ''nil))))
            (iff (intersectp-equal (svarlist-change-override x type1)
                                   (svarlist-change-override y type2))
                 (and (svar-overridetype-equiv type1 type2)
                      (intersectp-equal (svarlist-change-override x nil)
                                        (svarlist-change-override y nil)))))
   :hints(("Goal" :in-theory (enable svarlist-change-override
                                     member-svar-change-override-of-svarlist-change-override)))))


(defsection svex-lookup-of-svarlist-to-override-alist

  (local (in-theory (enable svar-override-p-when-equal-change-override
                            self-equal-change-override)))
  
  (defthmd svex-lookup-of-svarlist-to-override-alist
    (equal (svex-lookup key (svarlist-to-override-alist x))
           (and (member-equal (svar-fix key) (svarlist-change-override x nil))
                (svex-call 'bit?! (list (svex-var (svar-change-override key :test))
                                        (svex-var (svar-change-override key :val))
                                        (svex-var (svar-change-override key nil))))))
    :hints(("Goal" :in-theory (enable svarlist-to-override-alist
                                      svex-lookup-redef
                                      equal-of-svar-change-override
                                      svarlist-change-override)))))


(local (defthmd svex-lookup-when-not-member-keys
         (implies (not (member-equal (svar-fix v) (svex-alist-keys x)))
                  (not (svex-lookup v x)))))

(local (defthm svarlist-nonoverride-p-when-svarlist-override-p
           (implies (and (Svarlist-override-p x type)
                         (not (svar-overridetype-equiv type type2)))
                    (svarlist-nonoverride-p x type2))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p
                                             svarlist-override-p
                                             svar-override-p-when-other)))))

(encapsulate nil

  (local (in-theory (enable svar-override-p-when-equal-change-override
                            self-equal-change-override
                            svex-lookup-of-svarlist-to-override-alist
                            svar-override-p-when-member-change-override
                            member-svar-change-override-of-svarlist-change-override)))

  
  

  
  (defthm svex-alist-ovmonotonic-of-svarlist-to-override-alist
    (svex-alist-ovmonotonic (svarlist-to-override-alist x))
    :hints(("Goal" :in-theory (enable svex-alist-ovmonotonic
                                      svex-apply
                                      svex-eval)
            :expand ((svex-alist-ovmonotonic (svarlist-to-override-alist x))))
           (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-ovmonotonic-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                     ((mv-nth '1 ,call) . env2)))))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
                
           (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-env-<<=-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
           (and stable-under-simplificationp
                '(:use ((:instance svex-env-ov<<=-necc
                         (x env1) (y env2) (v (svar-change-override badkey :test)))
                        (:instance svex-env-ov<<=-necc
                         (x env1) (y env2) (v (svar-change-override badkey :val)))
                        (:instance svex-env-ov<<=-necc
                         (x env1) (y env2) (v (svar-change-override badkey nil))))))))

  (local (defthm 4vec-bit?!-lemma
           (implies (equal (4vec-bit?! x y 0) (4vec-bit?! x z 0))
                    (equal (equal (4vec-bit?! x y a) (4vec-bit?! x z a))
                           t))
           :hints (("goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))
                   (bitops::logbitp-reasoning)
                   (and stable-under-simplificationp
                        '(:in-theory (enable b-ite))))))
                        
  
  (local (defthm eval-bit?!-when-ovsimilar
           (implies (svex-envs-ovsimilar x y)
                    (b* ((test (svar-change-override v :test))
                         (val (svar-change-override v :val))
                         (non (svar-change-override v nil)))
                      (equal (equal (4vec-bit?! (svex-env-lookup test x)
                                                (svex-env-lookup val x)
                                                (svex-env-lookup non x))
                                    (4vec-bit?! (svex-env-lookup test y)
                                                (svex-env-lookup val y)
                                                (svex-env-lookup non y)))
                             t)))
           :hints (("Goal" :use ((:instance svex-envs-ovsimilar-necc (v (svar-change-override v :test)))
                                 (:instance svex-envs-ovsimilar-necc (v (svar-change-override v :val)))
                                 (:instance svex-envs-ovsimilar-necc (v (svar-change-override v nil))))))))
  
  (local (defthm eval-svarlist-to-override-alist-when-ovsimilar
           (implies (svex-envs-ovsimilar env1 env2)
                    (b* ((a (svarlist-to-override-alist x)))
                      (equal (svex-envs-similar
                              (svex-alist-eval a env1)
                              (svex-alist-eval a env2))
                             t)))
           :hints(("Goal" :in-theory (e/d (svex-envs-similar
                                             svex-apply
                                             svex-lookup-of-svarlist-to-override-alist)
                                          (SVAR-OVERRIDE-P-WHEN-MEMBER-CHANGE-OVERRIDE))
                   :expand ((:free (v env) (svex-eval (svex-var v) env)))
                   ))))
  
  (defthm svex-alist-ovcongruent-of-svarlist-to-override-alist
    (svex-alist-ovcongruent (svarlist-to-override-alist x))
    :hints(("Goal" :in-theory (enable svex-alist-ovcongruent))))

  (local (defthm member-svar-change-override-when-svar-override-p
           (implies (and (svarlist-override-p keys type2)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal (svar-change-override x type1) keys)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             equal-of-svar-change-override
                                             svar-override-p-when-other)))))
  
  (local (defthm svex-compose-alist-selfbound-keys-p-of-change-override
           (implies (svarlist-override-p (svex-alist-keys a) nil)
                    (svex-compose-alist-selfbound-keys-p (svarlist-change-override x :test) a))
           :hints(("Goal" :in-theory (e/d (svarlist-change-override
                                             svex-compose-alist-selfbound-keys-p
                                             svex-compose-lookup
                                             svex-lookup-when-not-member-keys)
                                          (member-svex-alist-keys))))))

  
  (defthm svex-alist-<<=-of-svex-alist-compose-when-ovmonotonic
    (implies (and (svex-alist-ovmonotonic x)
                  (svex-alist-<<= a b)
                  (set-equiv (svex-alist-keys a) (svex-alist-keys b))
                  (svarlist-override-p (svex-alist-keys a) nil))
             (svex-alist-<<= (svex-alist-compose x a)
                             (svex-alist-compose x b)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-<<=-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . env)))
                          :in-theory (enable svex-alist-ovmonotonic-necc)))))))
  
  (defthm svex-alist-<<=-of-compose-svarlist-to-override-alist
    (implies (and (svarlist-override-p (svex-alist-keys a) nil)
                  (set-equiv (svex-alist-keys a) (svex-alist-keys b))
                  (svex-alist-<<= a b))
             (svex-alist-<<= (svex-alist-compose (svarlist-to-override-alist x) a)
                             (svex-alist-compose (svarlist-to-override-alist x) b)))
    :hints(("Goal" :use ((:instance svex-alist-<<=-of-svex-alist-compose-when-ovmonotonic
                          (x (svarlist-to-override-alist x))))
            :in-theory (disable svex-alist-<<=-of-svex-alist-compose-when-ovmonotonic)))))




(defthm svex-alist-compose-preserves-ovmonotonic
  (implies (and (svex-alist-ovmonotonic x)
                (svex-alist-ovmonotonic y)
                (svarlist-override-p (svex-alist-keys y) nil))
           (svex-alist-ovmonotonic (svex-alist-compose x y)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))
          (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-ovmonotonic-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                     ((mv-nth '1 ,call) . env2)))
                          :in-theory (enable svex-alist-ovmonotonic-necc)))))))




(defthm svex-env-removekeys-when-not-intersecting
  (implies (not (intersectp-equal (double-rewrite (alist-keys (svex-env-fix x))) (svarlist-fix vars)))
           (equal (svex-env-removekeys vars x)
                  (svex-env-fix x)))
  :hints(("Goal" :in-theory (enable svex-env-removekeys
                                    svex-env-fix))))


(defconst *empty-override-config*
  (make-svtv-assigns-override-config-include :vars nil))


(local
 (defsection delay-compose-lemma
   (local (defthm hons-assoc-equal-of-fast-alist-fork
            (equal (hons-assoc-equal k (fast-alist-fork x y))
                   (or (hons-assoc-equal k y)
                       (hons-assoc-equal k x)))
            :hints(("Goal" :in-theory (enable fast-alist-fork)))))
   (defthm fast-alist-fork-under-svex-envs-equivalent
     (svex-envs-equivalent (fast-alist-fork x y)
                           (append y x))
     :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                       svex-env-boundp
                                       svex-env-lookup)
             :do-not-induct t)))

   (defthmd delay-compose-lemma
     (svex-alist-eval-equiv
      (svex-alist-compose x.delays (fast-alist-fork values (svex-alist-compose override-alist values)))
      (svex-alist-compose (svex-alist-compose x.delays override-alist) values))
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                       svex-eval-equiv)
             :do-not-induct t)))))


(local (defthmd loghead-is-0-when-loghead-equal-0
         (implies (and (equal (loghead n x) 0)
                       (< (nfix m) (nfix n)))
                  (equal (loghead m x) 0))
         :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))

(defthm svar-nonoverride-p-when-svar-addr-p
  (implies (svar-addr-p x)
           (and (svar-override-p x nil)
                (implies (not (svar-overridetype-equiv type nil))
                         (not (svar-override-p x type)))))
  :hints(("Goal" :in-theory (enable svar-addr-p
                                    svar-override-p
                                    loghead-is-0-when-loghead-equal-0
                                    svar-overridetype-fix-possibilities))))

(defthm svarlist-nonoverride-p-when-svarlist-addr-p
  (implies (svarlist-addr-p x)
           (and (svarlist-override-p x nil)
                (implies (and (not (svar-overridetype-equiv type nil))
                              (consp x))
                         (not (svarlist-override-p x type)))))
  :hints(("Goal" :in-theory (enable svarlist-addr-p svarlist-override-p))))


(local (in-theory (disable hons-dups-p)))





(defthmd svar-override-p-when-member
  (implies (and (svarlist-override-p x type)
                (member-equal (svar-fix v) (svarlist-fix x)))
           (svar-override-p v type))
  :hints(("Goal" :in-theory (enable svarlist-override-p))))

(defthmd svar-override-p-when-member-no-fix
  (implies (and (svarlist-override-p x type)
                (member-equal v x))
           (svar-override-p v type))
  :hints(("Goal" :in-theory (enable svarlist-override-p))))

(defthm svarlist-override-p-of-intersection
  (implies (or (svarlist-override-p a type)
               (svarlist-override-p b type))
           (svarlist-override-p (intersection-equal a b) type))
  :hints(("Goal" :in-theory (enable intersection-equal
                                    svarlist-override-p
                                    svar-override-p-when-member-no-fix))))

(defthm svarlist-override-p-of-set-diff
  (implies (svarlist-override-p a type)
           (svarlist-override-p (set-difference-equal a b) type))
  :hints(("Goal" :in-theory (enable svarlist-override-p))))

(defthm svarlist-override-p-of-svtv-assigns-override-vars
  (implies (svarlist-override-p (svex-alist-keys assigns) type)
           (svarlist-override-p (svtv-assigns-override-vars assigns config) type))
  :hints(("Goal" :in-theory (enable svtv-assigns-override-vars))))


;; (defsection vars-of-svex-alist-compose-override-triplelist
;;   (local (defthm member-svar-override-triplelist-lookup-refvar
;;            (implies (member-equal (svar-fix var) (svar-override-triplelist->refvars triples))
;;                     (member-equal (svar-override-triplelist-lookup-refvar var triples)
;;                                   (svar-override-triplelist-fix triples)))
;;            :hints(("Goal" :in-theory (enable svar-override-triplelist-fix
;;                                              svar-override-triplelist-lookup-refvar
;;                                              svar-override-triplelist->refvars)))))

;;   (local (defthm member-testvar-of-testvars-when-member-triple
;;            (implies (and (member-equal (svar-override-triple-fix trip)
;;                                        (svar-override-triplelist-fix triples)))
;;                     (member-equal (svar-override-triple->testvar trip)
;;                                   (svar-override-triplelist->testvars triples)))
;;            :hints(("Goal" :in-theory (enable svar-override-triplelist->testvars
;;                                              svar-override-triplelist-fix)))))

;;   (local (defthm member-valvar-of-valvars-when-member-triple
;;            (implies (and (member-equal (svar-override-triple-fix trip)
;;                                        (svar-override-triplelist-fix triples)))
;;                     (member-equal (svar-override-triple->valvar trip)
;;                                   (svar-override-triplelist->valvars triples)))
;;            :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
;;                                              svar-override-triplelist-fix)))))

;;   (defthmd svar-override-triplelist-override-vars-under-set-equiv
;;     (set-equiv (svar-override-triplelist-override-vars x)
;;                (append (svar-override-triplelist->testvars x)
;;                        (svar-override-triplelist->valvars x)))
;;     :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
;;                                       svar-override-triplelist->testvars
;;                                       svar-override-triplelist-override-vars)
;;             :induct t)
;;            (and stable-under-simplificationp
;;                 '(:in-theory (enable acl2::set-unequal-witness-rw)))))

;;   (local (in-theory (enable svar-override-triplelist-override-vars-under-set-equiv)))

;;   (defthm-svex-vars-flag vars-of-svex-compose-override-triplelist
;;     (defthm vars-of-svex-compose-override-triplelist
;;       (implies (and (not (member-equal v (svex-vars x)))
;;                     (not (member-equal v (svar-override-triplelist-override-vars triples))))
;;                (not (member-equal v (svex-vars (svex-compose x (svar-override-triplelist->override-alist triples))))))
;;       :hints ('(:expand ((svex-vars x)
;;                          (:free (env) (svex-compose x env)))))
;;       :flag svex-vars)
;;     (defthm vars-of-svexlist-compose-override-triplelist
;;       (implies (and (not (member-equal v (svexlist-vars x)))
;;                     (not (member-equal v (svar-override-triplelist-override-vars triples))))
;;                (not (member-equal v (svexlist-vars (svexlist-compose x (svar-override-triplelist->override-alist triples))))))
;;       :hints ('(:expand ((svexlist-vars x)
;;                          (:free (env) (svexlist-compose x env)))))
;;       :flag svexlist-vars))

;;   (defthm vars-of-svex-alist-compose-override-triplelist
;;     (implies (and (not (member-equal v (svex-alist-vars x)))
;;                   (not (member-equal v (svar-override-triplelist-override-vars triples))))
;;              (not (member-equal v (svex-alist-vars (svex-alist-compose x (svar-override-triplelist->override-alist triples))))))
;;     :hints(("Goal" :in-theory (enable svex-alist-vars svex-alist-compose)))))

(defsection vars-of-svex-alist-compose-override-alist

  (local (in-theory (enable svex-lookup-of-svarlist-to-override-alist
                            member-svar-change-override-of-svarlist-change-override
                            svar-override-p-when-member-change-override
                            svar-override-p-when-member-change-override-no-fix)))
  
  (defthm-svex-vars-flag vars-of-svex-compose-override-alist
    (defthm vars-of-svex-compose-override-alist
      (implies (and (not (member-equal v (svex-vars x)))
                    (not (member-equal v (svarlist-change-override keys :test)))
                    (not (member-equal v (svarlist-change-override keys :val))))
               (not (member-equal v (svex-vars (svex-compose x (svarlist-to-override-alist keys))))))
      :hints ('(:expand ((svex-vars x)
                         (:free (env) (svex-compose x env)))))
      :flag svex-vars)
    (defthm vars-of-svexlist-compose-override-alist
      (implies (and (not (member-equal v (svexlist-vars x)))
                    (not (member-equal v (svarlist-change-override keys :test)))
                    (not (member-equal v (svarlist-change-override keys :val))))
               (not (member-equal v (svexlist-vars (svexlist-compose x (svarlist-to-override-alist keys))))))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (env) (svexlist-compose x env)))))
      :flag svexlist-vars))

  (defthm vars-of-svex-alist-compose-override-alist
    (implies (and (not (member-equal v (svex-alist-vars x)))
                    (not (member-equal v (svarlist-change-override keys :test)))
                    (not (member-equal v (svarlist-change-override keys :val))))
             (not (member-equal v (svex-alist-vars (svex-alist-compose x (svarlist-to-override-alist keys))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars svex-alist-compose)))))


(defthm svex-env-<<=-of-reduce-nonoverride-when-ov<<=
  (implies (and (svex-env-ov<<= x y)
                (svarlist-override-p vars nil))
           (svex-env-<<= (svex-env-reduce vars x) (svex-env-reduce vars y)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))
          (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-env-<<=-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . key)))))))
          (and stable-under-simplificationp
               '(:use ((:instance svex-env-ov<<=-necc
                        (v key)))
                 :in-theory (enable MEMBER-WHEN-NOT-SVAR-OVERRIDE-P
                                    svar-override-p-when-other)))))



(defthm svex-alist-ovmonotonic-when-monotonic
  (implies (and (svarlist-override-p (svex-alist-vars x) nil)
                (svex-alist-monotonic-p x))
           (svex-alist-ovmonotonic x))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))
          (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-ovmonotonic-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                     ((mv-nth '1 ,call) . env2)))))))
          (and stable-under-simplificationp
               '(:use ((:instance svex-alist-monotonic-p-necc
                        (env1 (svex-env-reduce (svex-alist-vars x) env1))
                        (env2 (svex-env-reduce (svex-alist-vars x) env2))))
                 :in-theory (e/d (svexlist-vars-of-svex-alist-vals)
                                 (svex-alist-monotonic-p-necc))))))


(local (defthm svarlist-nonoverride-p-of-change-override
         (equal (svarlist-nonoverride-p (svarlist-change-override x type1) type2)
                (or (atom x)
                    (not (svar-overridetype-equiv type1 type2))))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           svarlist-nonoverride-p)))))

(define flatnorm-add-overrides ((x flatnorm-res-p)
                                (overridekeys svarlist-p))
  :returns (new-x flatnorm-res-p)
  (b* (((flatnorm-res x))
       (alist (svarlist-to-override-alist overridekeys))
       ((acl2::with-fast alist)))
    (change-flatnorm-res x :assigns (svex-alist-compose x.assigns alist)
                         :delays (svex-alist-compose x.delays alist)))
  ///
  (defret svex-alist-keys-of-delays-of-<fn>
    (equal (svex-alist-keys (flatnorm-res->delays new-x))
           (svex-alist-keys (flatnorm-res->delays x))))

  (defret svex-alist-keys-of-assigns-of-<fn>
    (equal (svex-alist-keys (flatnorm-res->assigns new-x))
           (svex-alist-keys (flatnorm-res->assigns x))))

  (defthm svex-alist-width-of-flatnorm-add-overrides
    (b* (((flatnorm-res x))
         ((flatnorm-res new-x) (flatnorm-add-overrides x keys)))
      (implies (svarlist-override-p (svex-alist-vars x.assigns) nil)
               (equal (svex-alist-width new-x.assigns)
                      (svex-alist-width x.assigns)))))

  (defret svex-alist-ovmonotonic-of-<fn>
    (b* (((flatnorm-res x))
         ((flatnorm-res new-x)))
      (and (implies
            (svex-alist-ovmonotonic x.assigns)
            (svex-alist-ovmonotonic new-x.assigns))
           (implies
            (svex-alist-ovmonotonic x.delays)
            (svex-alist-ovmonotonic new-x.delays)))))

  (defret svex-alist-ovcongruent-of-<fn>
    (b* (((flatnorm-res x))
         ((flatnorm-res new-x)))
      (and (implies
            (svex-alist-ovcongruent x.assigns)
            (svex-alist-ovcongruent new-x.assigns))
           (implies
            (svex-alist-ovcongruent x.delays)
            (svex-alist-ovcongruent new-x.delays)))))

  (defret svex-alist-vars-of-<fn>-assigns
    (b* (((flatnorm-res x))
         ((flatnorm-res new-x)))
      (and (implies (and (not (member-equal v (svex-alist-vars x.assigns)))
                         (not (member-equal v (svarlist-change-override overridekeys :test)))
                         (not (member-equal v (svarlist-change-override overridekeys :val))))
                    (not (member-equal v (svex-alist-vars new-x.assigns)))))))

  (defret svex-alist-vars-of-<fn>-delays
    (b* (((flatnorm-res x))
         ((flatnorm-res new-x)))
      (and (implies (and (not (member-equal v (svex-alist-vars x.delays)))
                         (not (member-equal v (svarlist-change-override overridekeys :test)))
                         (not (member-equal v (svarlist-change-override overridekeys :val))))
                    (not (member-equal v (svex-alist-vars new-x.delays))))))))


;; (defcong svex-envs-similar equal (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint) 2
;;   :hints(("Goal" :in-theory (enable svar-override-triplelist-muxes-agree
;;                                     svar-override-triple-mux-agrees))))

;; (defcong svex-envs-similar equal (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint) 3
;;   :hints(("Goal" :in-theory (enable svar-override-triplelist-muxes-agree
;;                                     svar-override-triple-mux-agrees))))

;; (defcong svex-envs-similar equal (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint) 4
;;   :hints(("Goal" :in-theory (enable svar-override-triplelist-muxes-agree
;;                                     svar-override-triple-mux-agrees))))










;; (defthm svex-env-muxtests-subsetp-of-append-spec-env-non-testvars
;;   (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix a))))
;;            (equal (svex-env-muxtests-subsetp vars (append a spec-env) impl-env)
;;                   (svex-env-muxtests-subsetp vars spec-env impl-env)))
;;   :hints(("Goal" :in-theory (enable svex-env-muxtests-subsetp
;;                                     svarlist-fix
;;                                     svex-env-boundp-iff-member-alist-keys))))

;; (defthm svex-env-muxtests-subsetp-of-append-impl-env-non-testvars
;;   (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix a))))
;;            (equal (svex-env-muxtests-subsetp vars spec-env (append a impl-env))
;;                   (svex-env-muxtests-subsetp vars spec-env impl-env)))
;;   :hints(("Goal" :in-theory (enable svex-env-muxtests-subsetp
;;                                     svarlist-fix
;;                                     svex-env-boundp-iff-member-alist-keys))))




(defthmd vars-of-svex-alist-compose-strong
  (implies (and (not (member-equal v (set-difference-equal (svex-alist-vars x) (svex-alist-keys y))))
                (not (member-equal v (svex-alist-vars y))))
           (not (member-equal v (svex-alist-vars (svex-alist-compose x y)))))
  :hints(("Goal" :in-theory (e/d (svex-alist-vars svex-alist-compose
                                                  vars-of-svex-compose-strong)
                                 (member-svex-alist-keys))
          :induct (len x))))


;; (define svex-override-triplelist-muxes-agree ((triples svex-override-triplelist-p)
                                              

(defsection overridekey-transparent-p-of-compose

  
  
  (defthm-svex-compose-flag svex-overridekey-transparent-p-of-compose-when-nonoverride
    (defthm svex-overridekey-transparent-p-of-compose-when-nonoverride
      (implies (and (svarlist-override-p (svex-vars x) nil)
                    (svex-alist-overridekey-transparent-p a overridekeys subst))
               (svex-overridekey-transparent-p (svex-compose x a)
                                               overridekeys subst))
      :hints ('(:expand ((svex-compose x a)
                         (:free (x) (svarlist-override-p (list x) nil)))
                :in-theory (enable SVEX-OVERRIDEKEY-TRANSPARENT-P-WHEN-CONST
                                   svex-overridekey-transparent-p-when-args-transparent
                                   svex-overridekey-transparent-p-when-non-override-var
                                   svar-override-p-when-other)))
      :flag svex-compose)
    (defthm svexlist-overridekey-transparent-p-of-compose-when-nonoverride
      (implies (and (svarlist-override-p (svexlist-vars x) nil)
                    (svex-alist-overridekey-transparent-p a overridekeys subst))
               (svexlist-overridekey-transparent-p (svexlist-compose x a)
                                                    overridekeys subst))
      :hints ('(:expand ((svexlist-compose x a)
                         (svexlist-vars x)
                         (:free (car cdr) (svexlist-overridekey-transparent-p (cons car cdr) overridekeys subst)))))
      :flag svexlist-compose))

  (defthm svex-alist-overridekey-transparent-p-of-compose-when-nonoverride
    (implies (and (svarlist-override-p (svex-alist-vars x) nil)
                  (svex-alist-overridekey-transparent-p a overridekeys subst))
             (svex-alist-overridekey-transparent-p (svex-alist-compose x a)
                                                   overridekeys subst))
    :hints (("goal" :induct (svex-alist-compose x a)
             :in-theory (enable svex-alist-compose svex-acons)
             :expand ((:free (car cdr) (svex-alist-overridekey-transparent-p (cons car cdr) overridekeys subst))
                      (svex-alist-vars x)))))

  (local (defthm not-svex-lookup-of-svar-change-override
           (implies (and (svarlist-override-p (svex-alist-keys a) type1)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (svex-lookup (svar-change-override k type2) a)))
           :hints(("Goal" :in-theory (enable svex-lookup-redef
                                             svarlist-override-p
                                             svex-alist-keys)))))

  (local (defthm svex-overridekey-transparent-p-of-override-mux-of-lookup
           (implies (and (svex-alist-overridekey-transparent-p a overridekeys a)
                         (svex-lookup v a)
                         (svar-override-p v nil)
                         (member-equal (svar-fix v) (svarlist-change-override overridekeys nil))
                         (subsetp-equal (svarlist-change-override overridekeys nil) (svex-alist-keys a)))
                    (svex-overridekey-transparent-p
                     (svex-call 'bit?! (list (svex-var (svar-change-override v :test))
                                             (svex-var (svar-change-override v :val))
                                             (svex-lookup v a)))
                     overridekeys a))
           :hints ((and stable-under-simplificationp
                        (B* ((lit (car (last clause))))
                          `(:expand ((:with svex-overridekey-transparent-p ,lit)
                                     (:free (v a) (svex-eval (svex-var v) a)))
                            :in-theory (enable svex-apply
                                               svar-overridekeys-envs-agree
                                               4vec-bit?!-agree-when-overridekeys-envs-agree)
                            :use ((:instance svex-overridekey-transparent-p-necc
                                   (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                                   (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                                   (subst a)
                                   (x (svex-lookup v a))))))))))
  
  (defthm-svex-compose-flag svex-overridekey-transparent-p-of-compose-override-alist
    (defthm svex-overridekey-transparent-p-of-compose-override-alist
      (implies (and (svarlist-override-p (svex-vars x) nil)
                    (svarlist-override-p (svex-alist-keys a) nil)
                    (subsetp-equal (svarlist-change-override overridekeys nil) (svex-alist-keys a))
                    (svex-alist-overridekey-transparent-p a overridekeys a))
               (svex-overridekey-transparent-p
                (svex-compose
                 (svex-compose x (svarlist-to-override-alist overridekeys))
                 a)
                overridekeys a))
      :hints ('(:expand ((:free (a) (svex-compose x a))
                         (:free (fn args) (svex-compose (svex-call fn args) a))
                         (:free (x y) (svexlist-compose (cons x y) a))
                         (:free (v) (svex-compose (svex-var v) a))
                         (svexlist-compose nil a)
                         (:free (x) (svarlist-override-p (list x) nil)))
                :in-theory (enable SVEX-OVERRIDEKEY-TRANSPARENT-P-WHEN-CONST
                                   svex-overridekey-transparent-p-when-args-transparent
                                   svex-overridekey-transparent-p-when-non-override-var
                                   svar-override-p-when-other
                                   svex-lookup-of-svarlist-to-override-alist)))
      :flag svex-compose)
    (defthm svexlist-overridekey-transparent-p-of-compose-override-alist
      (implies (and (svarlist-override-p (svexlist-vars x) nil)
                    (svarlist-override-p (svex-alist-keys a) nil)
                    (subsetp-equal (svarlist-change-override overridekeys nil) (svex-alist-keys a))
                    (svex-alist-overridekey-transparent-p a overridekeys a))
               (svexlist-overridekey-transparent-p
                (svexlist-compose
                 (svexlist-compose x (svarlist-to-override-alist overridekeys)) a)
                                                    overridekeys a))
      :hints ('(:expand ((:free (a) (svexlist-compose x a))
                         (:free (a x y) (svexlist-compose (cons x y) a))
                         (svexlist-vars x)
                         (:free (car cdr) (svexlist-overridekey-transparent-p (cons car cdr) overridekeys a)))))
      :flag svexlist-compose))

  (defthm svex-alist-overridekey-transparent-p-of-compose-override-alist
    (implies (and (svarlist-override-p (svex-alist-vars x) nil)
                  (svarlist-override-p (svex-alist-keys a) nil)
                  (subsetp-equal (svarlist-change-override overridekeys nil) (svex-alist-keys a))
                  (svex-alist-overridekey-transparent-p a overridekeys a))
             (svex-alist-overridekey-transparent-p
              (svex-alist-compose
               (svex-alist-compose x (svarlist-to-override-alist overridekeys)) a)
              overridekeys a))
    :hints (("goal" :induct (svex-alist-compose x a)
             :in-theory (enable svex-alist-compose svex-acons)
             :expand ((:free (car cdr) (svex-alist-overridekey-transparent-p (cons car cdr) overridekeys a))
                      (svex-alist-vars x))))))



(defsection netevalcomp-p-of-least-fixpoint
  (local (defthm SVEX-LOOKUP-OF-SVARLIST-X-SUBST2
           (equal (svex-lookup v (svarlist-x-subst x))
                  (and (member (svar-fix v) (svarlist-fix x))
                       (svex-x)))
           :hints(("Goal" :in-theory (enable svex-lookup-redef
                                             svarlist-x-subst)))))
  (local (defthm svex-alist-extract-of-svarlist-x-subst
           (equal (svex-alist-extract x (svarlist-x-subst y))
                  (svarlist-x-subst x))
           :hints(("Goal" :in-theory (enable svex-alist-extract
                                             svex-lookup-iff-member-svex-alist-keys
                                             svarlist-x-subst)
                   :induct t
                   :expand ((svarlist-fix x))))))

  (local (defthm svex-alist-reduce-of-svarlist-x-subst
           (equal (svex-alist-reduce x (svarlist-x-subst y))
                  (svarlist-x-subst (intersection-equal (svarlist-fix x) (svarlist-fix y))))
           :hints(("Goal" :in-theory (e/d (svex-alist-reduce
                                             svex-lookup-iff-member-svex-alist-keys)
                                          (member-svex-alist-keys))
                   :induct t
                   :expand ((svarlist-fix x)
                            (:free (a b) (svarlist-x-subst (cons a b))))))))

  (local (defthm intersection-equal-when-superset
           (implies (subsetp-equal x y)
                    (equal (intersection-equal x y)
                           (true-list-fix x)))))

  (defthm netevalcomp-p-of-svarlist-x-subst
    (netevalcomp-p (svarlist-x-subst (svex-alist-keys x)) x)
    :hints (("goal" :use ((:instance netevalcomp-p-of-compose-netcomp
                           (x (svex-identity-subst (svex-alist-keys x)))
                           (y x)))
             :in-theory (disable netevalcomp-p-of-compose-netcomp))))


  (local (include-book "../svex/compose-theory-compose-steps"))

  (local (defthm netcomp-p-of-neteval-ordering-compile
           (netcomp-p (neteval-ordering-compile ordering x) x)
           :hints (("goal" :use ((:instance netcomp-p-suff
                                  (ordering ordering)
                                  (comp (neteval-ordering-compile ordering x))
                                  (decomp x)))))))

  (local (defthm append-under-svex-alist-compose-equiv
           (implies (subsetp-equal (svex-alist-keys x) (svex-alist-keys y))
                    (svex-alist-compose-equiv (append y x) y))
           :hints(("Goal" :in-theory (e/d (svex-alist-compose-equiv
                                             svex-compose-lookup
                                             svex-lookup-iff-member-svex-alist-keys)
                                          (member-svex-alist-keys))))))
  
  (defthm netevalcomp-p-of-compose-netcomp-with-netevalcomp
    (implies (and (netevalcomp-p evalcomp x)
                  (netcomp-p netcomp x)
                  (set-equiv (svex-alist-keys evalcomp) (svex-alist-keys x)))
             (netevalcomp-p (svex-alist-compose netcomp evalcomp) x))
    :hints (("goal" :expand ((netevalcomp-p evalcomp x)
                             ;; (netcomp-p netcomp x)
                             )
             :use ((:instance netevalcomp-p-of-compose-netcomp
                    (y x) (x (svex-alist-compose netcomp (neteval-ordering-compile (netevalcomp-p-witness evalcomp x) x)))))
             :in-theory (disable netevalcomp-p-of-compose-netcomp))))
  
  (defthm netevalcopm-p-of-svex-alist-fixpoint-iterate
    (netevalcomp-p (svex-alist-fixpoint-iterate n x (svarlist-x-subst (svex-alist-keys x))) x)
    :hints(("Goal" :in-theory (enable svex-alist-fixpoint-iterate))))
  
  (defthm netevalcomp-p-of-least-fixpoint
    (netevalcomp-p (svex-alist-least-fixpoint  x) x)
    :hints(("Goal" :in-theory (enable svex-alist-least-fixpoint)))))


(define flatnorm->ideal-fsm ((x flatnorm-res-p))
  :returns (fsm base-fsm-p)
  :non-executable t
  :parents (least-fixpoint)
  :short "Returns the fixpoint FSM derived from the assignment network and state updates (delays) given by the input."
  :guard (And (svex-alist-width (flatnorm-res->assigns x))
              (not (hons-dups-p (svex-alist-keys (flatnorm-res->assigns x)))))
  (b* (((flatnorm-res x))
       (values (svex-alist-least-fixpoint x.assigns)))
    (make-base-fsm :values values :nextstate (svex-alist-compose x.delays values)))
  ///

  ;; (local (defthmd svex-alist-compose-is-pairlis$
  ;;          (equal (svex-alist-compose x a)
  ;;                 (pairlis$ (svex-alist-keys x)
  ;;                           (svexlist-compose (svex-alist-vals x) a)))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-vals
  ;;                                            svexlist-compose
  ;;                                            svex-alist-keys
  ;;                                            svex-alist-compose
  ;;                                            svex-acons)))))

  ;; (local (defthmd svexlist-compose-of-svexlist-compose
  ;;          (svexlist-eval-equiv (svexlist-compose (svexlist-compose x a) b)
  ;;                               (svexlist-compose x (append (svex-alist-compose a b) b)))
  ;;          :hints(("Goal" :in-theory (enable svexlist-eval-equiv)))))
  
  ;; (local (defthm svex-alist-compose-of-svex-alist-compose-eval-equiv!!
  ;;          (svex-alist-eval-equiv!!
  ;;           (svex-alist-compose (svex-alist-compose x a) b)
  ;;           (svex-alist-compose x (append (svex-alist-compose a b) b)))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-compose-is-pairlis$
  ;;                                            svexlist-compose-of-svexlist-compose
  ;;                                            svex-alist-eval-equiv!!)))))
           
           
  
  (defthm flatnorm->ideal-fsm-with-overrides-override-transparent
    (b* (((flatnorm-res x))
         (override-flatnorm (flatnorm-add-overrides x overridekeys))
         (override-fsm (flatnorm->ideal-fsm override-flatnorm)))
      (implies (and (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width x.assigns)
                    (svarlist-override-p overridekeys nil)
                    (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys x.assigns))
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil))
               (base-fsm-overridekey-transparent-p override-fsm overridekeys)))
    :hints(("Goal" :in-theory (enable base-fsm-overridekey-transparent-p
                                      flatnorm-add-overrides))))

  (defthm flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition-values
    (b* (((flatnorm-res x))
         (override-keys (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
         (override-flatnorm (flatnorm-add-overrides x override-keys))
         ((base-fsm ideal-fsm) (flatnorm->ideal-fsm override-flatnorm))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)

                    (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                    (svex-alist-width x.assigns)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil))
               (svex-alist-<<= approx-fsm.values ideal-fsm.values)))
    ;; (implies
    ;;  (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.delays)
    ;;  (svex-env-<<= (svex-alist-eval approx-fsm.nextstate env)
    ;;                (svex-alist-eval ideal-fsm.nextstate env))))))
    :hints(("Goal" :in-theory (e/d (flatnorm-add-overrides
                                      phase-fsm-composition-p
                                      svtv-flatnorm-apply-overrides
                                      svar-override-triplelist->override-alist-of-svarlist-to-override-triples)
                                   (netevalcomp-p-implies-<<=-fixpoint))
            :use ((:instance netevalcomp-p-implies-<<=-fixpoint
                   (network
                    (b* (((flatnorm-res x))
                         (triples
                          (svarlist-to-override-triples
                           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
                      (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))))
                   (comp (base-fsm->values approx-fsm)))))))


  (local (defthm fast-alist-clean-under-svex-alist-eval-equiv
           (svex-alist-eval-equiv (fast-alist-clean x) x)
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv svex-lookup)))))

  (local (defthm svex-envs-agree-except-of-append-eval-when-removekeys-equiv
           (implies (svex-alist-eval-equiv (svex-alist-removekeys vars a)
                                           (svex-alist-removekeys vars b))
                    (svex-envs-agree-except vars
                                            (append (svex-alist-eval a env1) env2)
                                            (append (svex-alist-eval b env1) env2)))
           :hints ((and stable-under-simplificationp
                        (b* ((lit (car (last clause)))
                             (?wit `(svex-envs-agree-except-witness . ,(cdr lit))))
                          `(:expand ((:with svex-envs-agree-except-by-witness ,lit))
                            :use ((:instance SVEX-ALIST-EVAL-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ALIST-EVAL-1
                                   (alist (svex-alist-removekeys vars a))
                                   (alist-equiv (svex-alist-removekeys vars b))
                                   (env env1))
                                  (:instance svex-envs-equivalent-necc
                                   (k ,wit)
                                   (x (svex-env-removekeys vars (svex-alist-eval a env1)))
                                   (y (svex-env-removekeys vars (svex-alist-eval b env1)))))
                            :in-theory (disable svex-alist-eval-equiv-implies-svex-envs-equivalent-svex-alist-eval-1
                                                svex-envs-equivalent-necc
                                                svex-envs-similar-implies-equal-svex-env-lookup-2
                                                svex-envs-equivalent-implies-equal-svex-env-boundp-2)))))))



  (local (defthm svex-alist-<<=-of-compose-when-monotonic-on-vars
           (implies (and (svex-alist-monotonic-on-vars vars x)
                         (svex-alist-compose-<<= a b)
                         (svex-alist-eval-equiv (svex-alist-removekeys vars a)
                                                (svex-alist-removekeys vars b)))
                    (svex-alist-<<= (svex-alist-compose x a)
                                    (svex-alist-compose x b)))
           :hints ((and stable-under-simplificationp
                        (b* ((lit (car (last clause)))
                             (?wit `(svex-alist-<<=-witness . ,(cdr lit))))
                          `(:expand (,lit)
                            :in-theory (enable svex-alist-monotonic-on-vars-necc)))))))



  (local (defthm svex-alist-removekeys-of-all-keys
           (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix keys))
                    (svex-alist-eval-equiv (svex-alist-removekeys keys x) nil))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup-when-not-member-keys)))))

  (local (defthm svex-alist-<<=-of-nextstate-when-equiv
           (implies (svex-alist-eval-equiv! (base-fsm->nextstate x)
                                            (svex-alist-compose a b))
                    (iff (svex-alist-<<=  (base-fsm->nextstate x) y)
                         (svex-alist-<<= (svex-alist-compose a b) y)))))

  (defthm flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition-nextstate
    (b* (((flatnorm-res x))
         (overridekeys
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
         (override-flatnorm (flatnorm-add-overrides x overridekeys))
         ((base-fsm ideal-fsm) (flatnorm->ideal-fsm override-flatnorm))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)

                    (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                    (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.delays)

                    (svex-alist-width x.assigns)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil))
               (svex-alist-<<= approx-fsm.nextstate ideal-fsm.nextstate)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svar-override-triplelist->override-alist-of-svarlist-to-override-triples
                                    flatnorm-add-overrides)
                                   (SVEX-ALIST-EVAL-EQUIV-IMPLIES-EQUAL-SVEX-ALIST-<<=-1
                                    svtv-assigns-override-vars-subset-of-keys
                                    svar-override-triplelist->override-alist-monotonic-on-vars
                                    flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition-values
                                    netevalcomp-p-implies-<<=-fixpoint))
            :use ((:instance svar-override-triplelist->override-alist-monotonic-on-vars
                   (x (b* (((flatnorm-res x)))
                        (svarlist-to-override-triples
                         (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
                   (vars (svex-alist-keys (flatnorm-res->assigns x))))
                  (:instance svtv-assigns-override-vars-subset-of-keys
                   (assigns (flatnorm-res->assigns x))
                   (config (phase-fsm-config->override-config config)))
                  flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition-values))))


  (defthm flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition
    (b* (((flatnorm-res x))
         (overridekeys
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
         (override-flatnorm (flatnorm-add-overrides x overridekeys))
         (ideal-fsm (flatnorm->ideal-fsm override-flatnorm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)

                    (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                    (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.delays)

                    (svex-alist-width x.assigns)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil))
               (base-fsm-<<= approx-fsm ideal-fsm)))
    :hints(("Goal" :in-theory (e/d (base-fsm-<<=)
                                   (flatnorm->ideal-fsm)))))



  ;; 3. approximate-fsm with overrides evaluated on exact env >>= approximate-fsm with overrides evaluated on lesser env.
  ;;    -- this actually doesn't have to do with this function particularly and could be moved somewhere else
  (local (defthm svex-compose-alist-selfbound-keys-when-no-intersect
           (implies (not (intersectp-equal (svarlist-fix keys) (svex-alist-keys x)))
                    (svex-compose-alist-selfbound-keys-p keys x))
           :hints(("Goal" :in-theory (enable svex-compose-alist-selfbound-keys-p svex-compose-lookup)))))

  (defthm svar-override-triplelist->testvars-of-svarlist-to-override-triples
    (equal (Svar-override-triplelist->testvars (svarlist-to-override-triples keys))
           (svarlist-change-override keys :test))
    :hints(("Goal" :in-theory (enable svarlist-change-override
                                      svarlist-to-override-triples
                                      svar-override-triplelist->testvars))))

  (local (defthm intersectp-nonoverride-of-svarlist-change-override
           (implies (and (svarlist-override-p x nil)
                         (not (svar-overridetype-equiv nil type)))
                    (not (intersectp-equal x (svarlist-change-override y type))))
           :hints(("Goal" :in-theory (enable svarlist-override-p intersectp-equal
                                             MEMBER-SVARLIST-CHANGE-OVERRIDE-WHEN-NOT-SVAR-OVERRIDE-P
                                             svar-override-p-when-other)))))
  
  (defthm phase-fsm-composition-ovmonotonic-values
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svex-alist-monotonic-p x.assigns)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil))
               (svex-alist-ovmonotonic
                approx-fsm.values)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svar-override-triplelist->override-alist-of-svarlist-to-override-triples
                                    ovmonotonic-when-netevalcomp-p)
                                   (svar-override-triplelist->override-alist-monotonic-on-vars))
            :use ((:instance svar-override-triplelist->override-alist-monotonic-on-vars
                   (x (b* (((flatnorm-res x)))
                        (svarlist-to-override-triples
                         (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
                   (vars (svex-alist-keys (flatnorm-res->assigns x))))))))

  (local (defthm svarlist-nonoverride-p-when-svarlist-override-p-nil
           (implies (and (svarlist-override-p x nil)
                         (not (svar-overridetype-equiv type nil)))
                    (svarlist-nonoverride-p x type))))

  (local (defthm svar-override-p-when-member-special
           (implies (and (member-equal (svar-fix key) (svarlist-fix vars))
                         (svarlist-override-p vars nil)
                         (not (svar-overridetype-equiv type nil)))
                    (not (svar-override-p key type)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other)))))
  
  (local (defthm svex-envs-similar-of-extract-nonoverride-when-ovsimilar
           (implies (and (svex-envs-ovsimilar env1 env2)
                         (svarlist-override-p vars nil))
                    (equal (svex-envs-similar (svex-env-extract vars env1) (svex-env-extract vars env2))
                           t))
           :hints(("Goal" :in-theory (enable svex-envs-similar
                                             svar-override-p-when-other))
                  (and stable-under-simplificationp
                       (let ((call (acl2::find-call-lst 'svex-envs-similar-witness clause)))
                         (and call
                              `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . key)))))))
                  (and stable-under-simplificationp
                       '(:use ((:instance svex-envs-ovsimilar-necc
                                (x env1) (y env2) (v key))))))))
  
  (local (defthm svex-alist-ovcongruent-p-when-alist-vars-nonoverride
           (implies (svarlist-override-p (svex-alist-vars x) nil)
                    (svex-alist-ovcongruent x))
           :hints(("Goal" :in-theory (e/d (svex-alist-ovcongruent
                                           SVEX-ALIST-EVAL-EQUIVALENT-WHEN-EXTRACT-VARS-SIMILAR)
                                          (SVEX-ENVS-EQUIVALENT-WHEN-SIMILAR-AND-ALIST-KEYS-EQUIV)))
                  (and stable-under-simplificationp
                       (let ((call (acl2::find-call-lst 'svex-alist-ovcongruent-witness clause)))
                         (and call
                              `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                           ((mv-nth '1 ,call) . env2))))))))))
  
  (defthm phase-fsm-composition-ovcongruent-values
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil))
               (svex-alist-ovcongruent
                approx-fsm.values)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svar-override-triplelist->override-alist-of-svarlist-to-override-triples
                                    ovcongruent-when-netevalcomp-p)
                                   (svar-override-triplelist->override-alist-monotonic-on-vars))
            ;; :use ((:instance svar-override-triplelist->override-alist-monotonic-on-vars
            ;;        (x (b* (((flatnorm-res x)))
            ;;             (svarlist-to-override-triples
            ;;              (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
            ;;        (vars (svex-alist-keys (flatnorm-res->assigns x)))))
            )))
    
  
  (defthm svex-alist-ovmonotonic-of-append
    (implies (and (svex-alist-ovmonotonic x)
                  (svex-alist-ovmonotonic y))
             (svex-alist-ovmonotonic (append x y)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable svex-alist-ovmonotonic-necc))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-ovmonotonic-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                     ((mv-nth '1 ,call) . env2)))))))))

  (local (defthmd svex-alist-compose-preserves-ovmonotonic-free
           (implies (and (svex-alist-eval-equiv! z (svex-alist-compose x y))
                         (svex-alist-ovmonotonic x)
                         (svex-alist-ovmonotonic y)
                         (svarlist-override-p (svex-alist-keys y) nil))
                    (svex-alist-ovmonotonic z))))
  
  (defthm phase-fsm-composition-ovmonotonic-nextstate
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svex-alist-monotonic-p x.assigns)
                    (svex-alist-monotonic-p x.delays)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil)
                    (svarlist-override-p (svex-alist-keys x.delays) nil))
               (svex-alist-ovmonotonic
                approx-fsm.nextstate)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svar-override-triplelist->override-alist-of-svarlist-to-override-triples
                                    ovmonotonic-when-netevalcomp-p
                                    svex-alist-compose-preserves-ovmonotonic-free)
                                   (phase-fsm-composition-ovmonotonic-values))
            :use phase-fsm-composition-ovmonotonic-values)))

  (defthm svex-envs-similar-of-append
    (implies (and (svex-envs-similar x1 x2)
                  (svex-envs-similar y1 y2)
                  (set-equiv (alist-keys (svex-env-fix x1))
                             (alist-keys (svex-env-fix x2))))
             (equal (svex-envs-similar (append x1 y1)
                                       (append x2 y2))
                    t))
    :hints (("goal" :do-not-induct t
             :in-theory (e/d (svex-env-boundp-iff-member-alist-keys)
                             (acl2::alist-keys-member-hons-assoc-equal)))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthmd svex-envs-similar-when-equivalent
           (implies (svex-envs-equivalent x y)
                    (equal (svex-envs-similar x y) t))))
  
  (defthm svex-alist-ovcongruent-of-append
    (implies (and (svex-alist-ovcongruent x)
                  (svex-alist-ovcongruent y))
             (svex-alist-ovcongruent (append x y)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable svex-alist-ovcongruent-necc
                                svex-envs-similar-when-equivalent))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-ovcongruent-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                     ((mv-nth '1 ,call) . env2)))))))))

  
  
  (defthm phase-fsm-composition-ovcongruent-nextstate
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil)
                    (svarlist-override-p (svex-alist-keys x.delays) nil))
               (svex-alist-ovcongruent
                approx-fsm.nextstate)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svar-override-triplelist->override-alist-of-svarlist-to-override-triples)
                                   (phase-fsm-composition-ovcongruent-values
                                    ovcongruent-when-netevalcomp-p))
            :use phase-fsm-composition-ovcongruent-values)))

  (defthm phase-fsm-composition-ovmonotonic
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svex-alist-monotonic-p x.assigns)
                    (svex-alist-monotonic-p x.delays)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil)
                    (svarlist-override-p (svex-alist-keys x.delays) nil))
               (base-fsm-ovmonotonic approx-fsm)))
    :hints(("Goal" :in-theory (enable base-fsm-ovmonotonic))))

  (defthm phase-fsm-composition-ovcongruent
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm)))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svarlist-override-p (svex-alist-vars x.assigns) nil)
                    (svarlist-override-p (svex-alist-keys x.assigns) nil)
                    (svarlist-override-p (svex-alist-vars x.delays) nil)
                    (svarlist-override-p (svex-alist-keys x.delays) nil))
               (base-fsm-ovcongruent approx-fsm)))
    :hints(("Goal" :in-theory (enable base-fsm-ovcongruent))))

    (defthm flatnorm->ideal-fsm-with-overrides-is-phase-fsm-composition
      (b* (((flatnorm-res x))
           (overridekeys (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
           (override-flatnorm (flatnorm-add-overrides x overridekeys))
           (override-fsm (flatnorm->ideal-fsm override-flatnorm)))
        (phase-fsm-composition-p override-fsm x config))
      :hints(("Goal" :in-theory (enable phase-fsm-composition-p
                                        flatnorm-add-overrides
                                        svtv-flatnorm-apply-overrides
                                        ))))

    (defthm flatnorm->ideal-fsm-with-overrides-ovmonotonic
      (b* (((flatnorm-res x))
           (overridekeys (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
           (override-flatnorm (flatnorm-add-overrides x overridekeys))
           (override-fsm (flatnorm->ideal-fsm override-flatnorm)))
        (implies (and (svex-alist-monotonic-p x.assigns)
                      (svex-alist-monotonic-p x.delays)
                      (svarlist-override-p (svex-alist-vars x.assigns) nil)
                      (svarlist-override-p (svex-alist-keys x.assigns) nil)
                      (svarlist-override-p (svex-alist-vars x.delays) nil)
                      (svarlist-override-p (svex-alist-keys x.delays) nil))
                 (base-fsm-ovmonotonic override-fsm)))
      :hints (("goal" :in-theory (disable flatnorm->ideal-fsm
                                          flatnorm->ideal-fsm-with-overrides-is-phase-fsm-composition)
               :use flatnorm->ideal-fsm-with-overrides-is-phase-fsm-composition)))

    (defthm flatnorm->ideal-fsm-with-overrides-ovcongruent
      (b* (((flatnorm-res x))
           (overridekeys (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
           (override-flatnorm (flatnorm-add-overrides x overridekeys))
           (override-fsm (flatnorm->ideal-fsm override-flatnorm)))
        (implies (and (svarlist-override-p (svex-alist-vars x.assigns) nil)
                      (svarlist-override-p (svex-alist-keys x.assigns) nil)
                      (svarlist-override-p (svex-alist-vars x.delays) nil)
                      (svarlist-override-p (svex-alist-keys x.delays) nil))
                 (base-fsm-ovcongruent override-fsm)))
      :hints (("goal" :in-theory (disable flatnorm->ideal-fsm
                                          flatnorm->ideal-fsm-with-overrides-is-phase-fsm-composition)
               :use flatnorm->ideal-fsm-with-overrides-is-phase-fsm-composition)))

    (defret alist-keys-of-<fn>
    (b* (((base-fsm fsm))
         ((flatnorm-res x)))
      (and (equal (svex-alist-keys fsm.values) (svex-alist-keys x.assigns))
           (equal (svex-alist-keys fsm.nextstate) (svex-alist-keys x.delays))))))



(define design-flatten-okp ((x design-p))
  :guard (modalist-addr-p (design->modalist x))
  :non-executable t
  (b* (((mv err & & &)
        (ec-call (svtv-design-flatten-fn x nil nil))))
    (not err))
  ///
  (defthm not-err-when-design-flatten-okp
    (implies (design-flatten-okp x)
             (not (mv-nth 0 (svtv-design-flatten x))))
    :hints(("Goal" :in-theory (enable normalize-stobjs-of-svtv-design-flatten)))))

(define design->flatnorm ((x design-p))
  ;; :guard (modalist-addr-p (design->modalist x))
  :returns (flatnorm flatnorm-res-p)
  (b* (((mv & flatten ?moddb aliases)
        (non-exec (svtv-design-flatten x :moddb nil :aliases nil))))
    (non-exec
     (svtv-normalize-assigns flatten aliases
                             (make-flatnorm-setup :monotonify t))))
  ///
  (defret no-duplicate-keys-of-<fn>-assigns
    (no-duplicatesp-equal (svex-alist-keys (flatnorm-res->assigns flatnorm))))

  (defret svex-alist-width-of-<fn>-assigns
    (svex-alist-width (flatnorm-res->assigns flatnorm)))

  (defret svarlist-addr-p-vars-of-<fn>
    (implies (and (modalist-addr-p (design->modalist x))
                  (design-flatten-okp x))
             (b* (((flatnorm-res flatnorm)))
               (and (svarlist-addr-p (svex-alist-vars flatnorm.assigns))
                    (svarlist-addr-p (svex-alist-vars flatnorm.delays))
                    (svarlist-addr-p (svex-alist-keys flatnorm.assigns))
                    (svarlist-addr-p (svex-alist-keys flatnorm.delays))))))

  (defret svarlist-override-p-vars-of-<fn>
    (implies (and (modalist-addr-p (design->modalist x))
                  (design-flatten-okp x))
             (b* (((flatnorm-res flatnorm)))
               (and (svarlist-override-p (svex-alist-vars flatnorm.assigns) nil)
                    (svarlist-override-p (svex-alist-vars flatnorm.delays) nil)
                    (svarlist-override-p (svex-alist-keys flatnorm.assigns) nil)
                    (svarlist-override-p (svex-alist-keys flatnorm.delays) nil)))))

  (defret <fn>-monotonic-p
    (b* (((flatnorm-res flatnorm)))
      (and (svex-alist-monotonic-p flatnorm.assigns)
           (svex-alist-monotonic-p flatnorm.delays)))))

(defthm phase-fsm-composition-ovmonotonic-of-design->flatnorm
  (b* (((flatnorm-res flat) (design->flatnorm x)))
    (implies (and (phase-fsm-composition-p approx-fsm flat config)
                  (modalist-addr-p (design->modalist x))
                  (design-flatten-okp x))
             (base-fsm-ovmonotonic
              approx-fsm)))
  :hints(("Goal" :in-theory (enable base-fsm-ovmonotonic))))

(defthm phase-fsm-composition-ovcongruent-of-design->flatnorm
  (b* (((flatnorm-res flat) (design->flatnorm x)))
    (implies (and (phase-fsm-composition-p approx-fsm flat config)
                  (modalist-addr-p (design->modalist x))
                  (design-flatten-okp x))
             (base-fsm-ovcongruent
              approx-fsm)))
  :hints(("Goal" :in-theory (enable base-fsm-ovcongruent))))


(define design->ideal-fsm ((x design-p)
                           (config phase-fsm-config-p))
  :guard (and (modalist-addr-p (design->modalist x))
              (design-flatten-okp x))
  :returns (ideal-fsm base-fsm-p)
  (b* (((flatnorm-res flatnorm) (design->flatnorm x)))
    (flatnorm->ideal-fsm
     (flatnorm-add-overrides
      flatnorm
       (svtv-assigns-override-vars flatnorm.assigns
                                   (phase-fsm-config->override-config config)))))
  ///
  (defret <fn>-overridekey-transparent
    (b* (((flatnorm-res flatnorm) (design->flatnorm x))
         (overridekeys (svtv-assigns-override-vars flatnorm.assigns
                                   (phase-fsm-config->override-config config))))
      (implies (and (modalist-addr-p (design->modalist x))
                    (design-flatten-okp x))
               (base-fsm-overridekey-transparent-p ideal-fsm overridekeys))))


  (defret <fn>->>=-phase-fsm-composition
    (b* ((flat (design->flatnorm x)))
      (implies (and (phase-fsm-composition-p approx-fsm flat config)
                    (modalist-addr-p (design->modalist x))
                    (design-flatten-okp x))
               (base-fsm-<<= approx-fsm ideal-fsm))))

  (defret <fn>-is-phase-fsm-composition
    (phase-fsm-composition-p ideal-fsm (design->flatnorm x) config))

  (defret <fn>-ovmonotonic
    (b* (((flatnorm-res flat) (design->flatnorm x)))
      (implies (and (modalist-addr-p (design->modalist x))
                    (design-flatten-okp x))
               (base-fsm-ovmonotonic ideal-fsm))))

  (defret <fn>-ovcongruent
    (b* (((flatnorm-res flat) (design->flatnorm x)))
      (implies (and (modalist-addr-p (design->modalist x))
                    (design-flatten-okp x))
               (base-fsm-ovcongruent ideal-fsm))))
  
  (defret alist-keys-of-<fn>
    (b* (((base-fsm ideal-fsm))
         ((flatnorm-res flat) (design->flatnorm x)))
      (and (equal (svex-alist-keys ideal-fsm.values) (svex-alist-keys flat.assigns))
           (equal (svex-alist-keys ideal-fsm.nextstate) (svex-alist-keys flat.delays))))))





