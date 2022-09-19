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

(include-book "design-fsm")
(include-book "../svex/fixpoint-override")
(include-book "../svex/compose-theory-fixpoint")
(include-book "../svex/compose-theory-monotonicity")

(local (include-book "svtv-stobj-pipeline-monotonicity"))
(local (include-book "../svex/alist-thms"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (in-theory (disable signed-byte-p)))

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
    (implies (svex-alist-width-limited-p map acc)
             (svex-alist-width-limited-p map
                                         (svex-alist-truncate-by-var-decls alist x acc)))
    :hints(("Goal" :in-theory (enable svex-alist-width-limited-p
                                      svex-alist-truncate-by-var-decls)
            :induct (svex-alist-truncate-by-var-decls alist x acc))))

  (defret svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls-monotonify
    (implies (svex-alist-width-limited-p map (svex-alist-monotonify acc))
             (svex-alist-width-limited-p map
                                         (svex-alist-monotonify
                                          (svex-alist-truncate-by-var-decls alist x acc))))
    :hints(("Goal" :in-theory (enable svex-alist-width-limited-p
                                      svex-alist-monotonify
                                      svex-alist-truncate-by-var-decls)
            :induct (svex-alist-truncate-by-var-decls alist x acc))))

  (defthm svex-alist-width-of-svex-alist-truncate-by-var-decls
    (svex-alist-width (svex-alist-truncate-by-var-decls x var-map nil))
    :hints (("goal" :use ((:instance svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls
                           (acc nil) (alist x) (x var-map)))
             :in-theory (e/d (svex-alist-width-limited-p)
                             (svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls)))))

  (defthm svex-alist-width-of-svex-alist-truncate-by-var-decls-monotonify
    (svex-alist-width (svex-alist-monotonify (svex-alist-truncate-by-var-decls x var-map nil)))
    :hints (("goal" :use ((:instance svex-alist-width-limited-p-of-svex-alist-truncate-by-var-decls-monotonify
                           (acc nil) (alist x) (x var-map)))
             :in-theory (e/d (svex-alist-width-limited-p)
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

(defthm no-duplicate-keys-of-svex-alist-truncate-by-var-decls
  (implies (and (no-duplicatesp-equal (svex-alist-keys x))
                (no-duplicatesp-equal (svex-alist-keys acc))
                (not (intersectp-equal (svex-alist-keys acc) (svex-alist-keys x))))
           (no-duplicatesp-equal (svex-alist-keys (svex-alist-truncate-by-var-decls x var-decls acc))))
  :hints(("Goal" :in-theory (enable svex-alist-truncate-by-var-decls svex-alist-keys))))



(defthm svex-alist-width-of-svtv-normalize-assigns
  (svex-alist-width (flatnorm-res->assigns
                     (svtv-normalize-assigns flatten aliases setup)))
  :hints(("Goal" :in-theory (enable svtv-normalize-assigns
                                    svex-normalize-assigns)
          :do-not-induct t)))


(define svarlist-to-override-triples ((x svarlist-p))
  :returns (triples svar-override-triplelist-p)
  (if (atom x)
      nil
    (cons (b* ((x1 (car x)))
            (make-svar-override-triple
             :refvar x1
             :valvar (change-svar x1 :override-val t)
             :testvar (change-svar x1 :override-test t)))
          (svarlist-to-override-triples (cdr x))))
  ///
  (defret svar-override-triplelist->refvars-of-<fn>
    (equal (svar-override-triplelist->refvars triples)
           (svarlist-fix x)))


  (local (defret member-non-override-val-valvars-of-<fn>
           (implies (not (svar->override-val v))
                    (not (member-equal v (svar-override-triplelist->valvars triples))))))

  (local (defret member-testvars-when-not-member-of-<fn>
           (implies (and (svarlist-addr-p x)
                         (svar-addr-p v)
                         (not (member-equal (svar-fix v) (svarlist-fix x))))
                    (not (member-equal (svar (svar->name v)
                                             (svar->delay v)
                                             (svar->nonblocking v)
                                             t nil)
                                       (svar-override-triplelist->testvars triples))))
           :hints(("Goal" :in-theory (enable svarlist-addr-p svar-addr-p
                                             svarlist-fix)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable svar-fix-redef))))))

  (local (defret member-valvars-when-not-member-of-<fn>
           (implies (and (svarlist-addr-p x)
                         (svar-addr-p v)
                         (not (member-equal (svar-fix v) (svarlist-fix x))))
                    (not (member-equal (svar (svar->name v)
                                             (svar->delay v)
                                             (svar->nonblocking v)
                                             nil t)
                                       (svar-override-triplelist->valvars triples))))
           :hints(("Goal" :in-theory (enable svarlist-addr-p svar-addr-p
                                             svarlist-fix)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable svar-fix-redef))))))

  (local (defret member-non-override-test-testvars-of-<fn>
           (implies (not (svar->override-test v))
                    (not (member-equal v (svar-override-triplelist->testvars triples))))))

  (local (defret member-override-test-when-svarlist-addr-p
           (implies (and (svar->override-test v)
                         (svarlist-addr-p x))
                    (not (member-equal v (svarlist-fix x))))
           :hints(("Goal" :in-theory (enable svarlist-addr-p svar-addr-p)))))

  (local (defret member-override-val-when-svarlist-addr-p
           (implies (and (svar->override-val v)
                         (svarlist-addr-p x))
                    (not (member-equal v (svarlist-fix x))))
           :hints(("Goal" :in-theory (enable svarlist-addr-p svar-addr-p)))))
  
  (defret no-duplicates-of-<fn>
    (implies (and (no-duplicatesp-equal (svarlist-fix x))
                  (svarlist-addr-p x))
             (and (no-duplicatesp-equal (svar-override-triplelist->valvars triples))
                  (no-duplicatesp-equal (svar-override-triplelist->testvars triples))
                  (not (intersectp-equal (svar-override-triplelist->valvars triples)
                                         (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svarlist-fix x) (svar-override-triplelist->valvars triples)))
                  (not (intersectp-equal (svarlist-fix x) (svar-override-triplelist->testvars triples)))))
    :hints(("Goal" :in-theory (enable svarlist-addr-p
                                      svar-addr-p
                                      svarlist-fix))))

  (defret testvar-non-addr-of-<fn>
    (implies (svar-addr-p v)
             (not (member-equal v (svar-override-triplelist->testvars triples))))
    :hints(("Goal" :in-theory (enable svar-addr-p))))

  (defret testvars-dont-intersect-addr-vars-of-<fn>
    (implies (svarlist-addr-p v)
             (and (not (intersectp-equal (svar-override-triplelist->testvars triples) v))
                  (not (intersectp-equal v (svar-override-triplelist->testvars triples)))))
    :hints(("Goal" :induct (svarlist-addr-p v)
            :in-theory (enable svarlist-addr-p))))

  (defret valvar-non-addr-of-<fn>
    (implies (svar-addr-p v)
             (not (member-equal v (svar-override-triplelist->valvars triples))))
    :hints(("Goal" :in-theory (enable svar-addr-p))))

  (defret valvars-dont-intersect-addr-vars-of-<fn>
    (implies (svarlist-addr-p v)
             (and (not (intersectp-equal (svar-override-triplelist->valvars triples) v))
                  (not (intersectp-equal v (svar-override-triplelist->valvars triples)))))
    :hints(("Goal" :induct (svarlist-addr-p v)
            :in-theory (enable svarlist-addr-p))))

  (defret override-var-non-addr-of-<fn>
    (implies (svar-addr-p v)
             (not (member-equal v (svar-override-triplelist-override-vars triples))))
    :hints(("Goal" :in-theory (enable svar-addr-p
                                      svar-override-triplelist-override-vars))))

  (defret override-vars-dont-intersect-addr-vars-of-<fn>
    (implies (svarlist-addr-p v)
             (and (not (intersectp-equal (svar-override-triplelist-override-vars triples) v))
                  (not (intersectp-equal v (svar-override-triplelist-override-vars triples)))))
    :hints(("Goal" :induct (svarlist-addr-p v)
            :in-theory (enable svarlist-addr-p))))

  (defretd svarlist-to-override-alist-in-terms-of-<fn>
    (equal (svarlist-to-override-alist x)
           (svar-override-triplelist->override-alist triples))
    :hints(("Goal" :in-theory (enable svarlist-to-override-alist
                                      svar-override-triplelist->override-alist)))))
  
(local (in-theory (disable hons-dups-p)))

(defthm svex-alist-monotonic-p-implies-monotonic-on-vars
  (implies (svex-alist-monotonic-p x)
           (svex-alist-monotonic-on-vars v x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-on-vars))))

(defthm svex-alist-monotonic-p-of-svex-alist-monotonify
  (svex-alist-monotonic-p (svex-alist-monotonify x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-p))))

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


(defthm no-duplicate-keys-of-svtv-normalize-assigns-values
  (no-duplicatesp-equal
   (svex-alist-keys
    (flatnorm-res->assigns
     (svtv-normalize-assigns flatten aliases setup))))
  :hints(("Goal" :in-theory (enable svtv-normalize-assigns
                                    svex-normalize-assigns))))


(defthm svarlist-addr-p-of-svtv-normalize-assigns
  (b* (((mv ?err ?res ?moddb ?aliases)
        (svtv-design-flatten design :moddb nil
                             :aliases nil))
       ((flatnorm-res x) (svtv-normalize-assigns flatten aliases flatnorm-setup)))
    (implies (and (not err)
                  (modalist-addr-p (design->modalist design)))
             (and (svarlist-addr-p (svex-alist-keys x.assigns))
                  (svarlist-addr-p (svex-alist-vars x.assigns)))))
  :hints(("Goal" :in-theory (enable svtv-normalize-assigns
                                    svtv-design-flatten))))

(local (in-theory (disable SVAR-OVERRIDE-TRIPLELIST-ENV-OK-IN-TERMS-OF-SVEX-OVERRIDE-TRIPLELIST-ENV-OK)))

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


(defsection svex-partial-monotonic-implies-monotonic-on-vars
  (local (defthm svex-env-extract-when-agree-except-non-intersecting
           (implies (and (svex-envs-agree-except vars x y)
                         (not (intersectp-equal (svarlist-fix params)
                                                (svarlist-fix vars))))
                    (equal (svex-env-extract params x)
                           (svex-env-extract params y)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix
                                             svex-envs-agree-except-implies)))))
  
  (defthm svex-partial-monotonic-implies-monotonic-on-vars
    (implies (and (svex-partial-monotonic params x)
                  (not (intersectp-equal (svarlist-fix params) (svarlist-fix vars))))
             (svex-monotonic-on-vars vars x))
    :hints (("goal" :expand ((svex-monotonic-on-vars vars x))
             :use ((:instance eval-when-svex-partial-monotonic
                    (param-keys params)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars x)))))
             :in-theory (disable eval-when-svex-partial-monotonic))))

  (defthm svexlist-partial-monotonic-implies-monotonic-on-vars
    (implies (and (svexlist-partial-monotonic params x)
                  (not (intersectp-equal (svarlist-fix params) (svarlist-fix vars))))
             (svexlist-monotonic-on-vars vars x))
    :hints (("goal" :expand ((svexlist-monotonic-on-vars vars x))
             :use ((:instance eval-when-svexlist-partial-monotonic
                    (param-keys params)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars x)))))
             :in-theory (disable eval-when-svexlist-partial-monotonic))))

  (defthm svex-alist-partial-monotonic-implies-monotonic-on-vars
    (implies (and (svex-alist-partial-monotonic params x)
                  (not (intersectp-equal (svarlist-fix params) (svarlist-fix vars))))
             (svex-alist-monotonic-on-vars vars x))
    :hints (("goal" :expand ((svex-alist-monotonic-on-vars vars x))
             :use ((:instance eval-when-svex-alist-partial-monotonic
                    (param-keys params)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars x)))))
             :in-theory (disable eval-when-svex-alist-partial-monotonic))))

  (local
   (defthm subset-diff-agree-except-lemma
     (implies (and (equal (svex-env-extract params env1)
                          (svex-env-extract params env2))
                   (subsetp (set-difference-equal (svarlist-fix vars2)
                                                  (svarlist-fix params))
                            (svarlist-fix vars)))
              (svex-envs-agree-except vars (svex-env-extract vars2 env1) (svex-env-extract vars2 env2)))
     :hints(("Goal" :in-theory (e/d (svex-envs-agree-except-by-witness))
             :restrict ((svex-env-lookup-of-svex-env-extract ((vars vars2))))
             :use ((:instance svex-env-lookup-of-svex-env-extract
                    (v (svex-envs-agree-except-witness vars (svex-env-extract vars2 env1) (svex-env-extract vars2 env2)))
                    (vars params)
                    (env env1))
                   (:instance svex-env-lookup-of-svex-env-extract
                    (v (svex-envs-agree-except-witness vars (svex-env-extract vars2 env1) (svex-env-extract vars2 env2)))
                    (vars params)
                    (env env2)))
             :do-not-induct t))))
  
  (defthm svex-monotonic-on-vars-implies-partial-monotonic
    (implies (and (svex-monotonic-on-vars vars x)
                  (subsetp (set-difference-equal (svex-vars x)
                                                 (svarlist-fix params))
                           (svarlist-fix vars)))
             (svex-partial-monotonic params x))
    :hints (("goal" :expand ((:with svex-partial-monotonic-by-eval (svex-partial-monotonic params x)))
             :use ((:instance svex-monotonic-on-vars-necc
                    (env1 (svex-env-extract (svex-vars x) (mv-nth 0 (svex-partial-monotonic-eval-witness params x))))
                    (env2 (svex-env-extract (svex-vars x) (mv-nth 1 (svex-partial-monotonic-eval-witness params x)))))))))
  
  (defthm svexlist-monotonic-on-vars-implies-partial-monotonic
    (implies (and (svexlist-monotonic-on-vars vars x)
                  (subsetp (set-difference-equal (svexlist-vars x)
                                                 (svarlist-fix params))
                           (svarlist-fix vars)))
             (svexlist-partial-monotonic params x))
    :hints (("goal" :expand ((:with svexlist-partial-monotonic-by-eval (svexlist-partial-monotonic params x)))
             :use ((:instance svexlist-monotonic-on-vars-necc
                    (env1 (svex-env-extract (svexlist-vars x) (mv-nth 0 (svexlist-partial-monotonic-eval-witness params x))))
                    (env2 (svex-env-extract (svexlist-vars x) (mv-nth 1 (svexlist-partial-monotonic-eval-witness params x)))))))))

  (defthm svex-alist-monotonic-on-vars-implies-partial-monotonic
    (implies (and (svex-alist-monotonic-on-vars vars x)
                  (subsetp (set-difference-equal (svex-alist-vars x)
                                                 (svarlist-fix params))
                           (svarlist-fix vars)))
             (svex-alist-partial-monotonic params x))
    :hints (("goal" :expand ((:with svex-alist-partial-monotonic-by-eval (svex-alist-partial-monotonic params x)))
             :use ((:instance svex-alist-monotonic-on-vars-necc
                    (env1 (svex-env-extract (svex-alist-vars x) (mv-nth 0 (svex-alist-partial-monotonic-eval-witness params x))))
                    (env2 (svex-env-extract (svex-alist-vars x) (mv-nth 1 (svex-alist-partial-monotonic-eval-witness params x))))))))))





(define flatnorm->ideal-fsm ((x flatnorm-res-p))
  :returns (fsm base-fsm-p)
  :non-executable t
  :guard (And (svex-alist-width (flatnorm-res->assigns x))
              (not (hons-dups-p (svex-alist-keys (flatnorm-res->assigns x)))))
  (b* (((flatnorm-res x))
       (values (svex-alist-least-fixpoint x.assigns)))
    (make-base-fsm :values values :nextstate (svex-alist-compose x.delays x.assigns)))
  ///

  


  (defret value-keys-of-<fn>
    (equal (svex-alist-keys (base-fsm->values fsm))
           (svex-alist-keys (flatnorm-res->assigns x))))
  
  (defret phase-fsm-composition-p-implies-<<=-ideal-fsm
    (b* (((flatnorm-res x))
         ((base-fsm fsm))
         ((base-fsm approx-fsm))
         (spec-values (svex-alist-eval fsm.values ref-env))
         (?spec-nextstate (svex-alist-eval fsm.values ref-env))
         (impl-values (svex-alist-eval approx-fsm.values override-env))
         (?impl-nextstate (svex-alist-eval approx-fsm.values override-env))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
      (implies (and
                ;; assigns well-formed
                (svex-alist-monotonic-p x.assigns)
                (svex-alist-monotonic-p x.delays)
                (no-duplicatesp-equal (svex-alist-keys x.assigns))
                (svex-alist-width x.assigns)

                ;; approx-fsm well formed
                (phase-fsm-composition-p approx-fsm x config)

                ;; override env well formed
                (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
                                        override-env ref-env)
                (svar-override-triplelist-env-ok
                 triples
                 override-env spec-values)

                ;; implies triples well-formed
                (svarlist-addr-p (svex-alist-keys x.assigns))
                (svarlist-addr-p (svex-alist-vars x.assigns)))

               (and 
                (svex-env-<<= impl-values spec-values)
                (svex-env-<<= impl-nextstate spec-nextstate)
                )))
    :hints (("Goal" :use ((:instance svex-alist-eval-override-fixpoint-equivalent-to-reference-fixpoint
                           (triples
                            (svarlist-to-override-triples
                             (svtv-assigns-override-vars (flatnorm-res->assigns x) (phase-fsm-config->override-config config))))
                           (network (flatnorm-res->assigns x)))
                          (:instance svex-alist-<<=-necc
                           (x (base-fsm->values approx-fsm))
                           (y (svex-alist-least-fixpoint
                               (svex-alist-compose
                                (flatnorm-res->assigns x)
                                (svarlist-to-override-alist
                                 (svtv-assigns-override-vars
                                  (flatnorm-res->assigns x)
                                  (phase-fsm-config->override-config config))))))
                           (env override-env)))
             :in-theory (e/d (phase-fsm-composition-p
                              svtv-flatnorm-apply-overrides
                              svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples)
                             (svex-alist-eval-override-fixpoint-equivalent-to-reference-fixpoint
                              SVAR-OVERRIDE-TRIPLELIST-ENV-OK-IN-TERMS-OF-SVEX-OVERRIDE-TRIPLELIST-ENV-OK))
             :do-not-induct t))
    :otf-flg t)


  (local
   (defthmd phase-fsm-composition-p-implies-netevalcomp-p
     (implies (phase-fsm-composition-p phase-fsm flatnorm config)
              (b* (((phase-fsm-config config))
                   ((mv overridden-assigns ?overridden-delays)
                    (svtv-flatnorm-apply-overrides flatnorm config.override-config))
                   ((base-fsm phase-fsm)))
                (netevalcomp-p phase-fsm.values overridden-assigns)))
     :hints (("goal" :in-theory (enable phase-fsm-composition-p)))))


  (local (defthm svex-alist-partial-monotonic-of-compose-monotonic-with-partial-monotonic
           (implies (and (svex-alist-monotonic-p x)
                         (svex-alist-partial-monotonic params a))
                    (svex-alist-partial-monotonic params (svex-alist-compose x a)))
           :hints (("goal" :expand ((:with svex-alist-partial-monotonic-by-eval
                                     (svex-alist-partial-monotonic params (svex-alist-compose x a))))))))


  (defthm svex-alist-partial-monotonic-of-svar-override-triplelist->override-alist
    (svex-alist-partial-monotonic
     (svar-override-triplelist->testvars triples)
     (svar-override-triplelist->override-alist triples))
    :hints(("Goal" :in-theory (enable svar-override-triplelist->override-alist
                                      svar-override-triplelist->testvars))))


  (local (defthm svex-env-extract-of-append-keys-superset
           (implies (subsetp-equal (svarlist-fix keys) (alist-keys (svex-env-fix x)))
                    (equal (svex-env-extract keys (append x y))
                           (svex-env-extract keys x)))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svex-env-boundp-iff-member-alist-keys)))))
  
  (defret phase-fsm-composition-p-implies-<<=-ideal-fsm-weaken
    (b* (((flatnorm-res x))
         ((base-fsm fsm))
         ((base-fsm approx-fsm))
         (spec-values (svex-alist-eval fsm.values ref-env))
         (?spec-nextstate (svex-alist-eval fsm.values ref-env))
         (impl-values (svex-alist-eval approx-fsm.values override-env))
         (?impl-nextstate (svex-alist-eval approx-fsm.values override-env))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
      (implies (and
                ;; assigns well-formed
                (svex-alist-monotonic-p x.assigns)
                (svex-alist-monotonic-p x.delays)
                (no-duplicatesp-equal (svex-alist-keys x.assigns))
                (svex-alist-width x.assigns)

                ;; approx-fsm well formed
                (phase-fsm-composition-p approx-fsm x config)

                ;; override env well formed
                (svar-override-triplelist-env-ok-<<= triples override-env spec-values)
                (svex-env-<<= (svex-env-removekeys
                               (svar-override-triplelist-override-vars triples) override-env)
                              ref-env)

                ;; implies triples well-formed
                (svarlist-addr-p (svex-alist-keys x.assigns))
                (svarlist-addr-p (svex-alist-vars x.assigns)))

               (and 
                (svex-env-<<= impl-values spec-values)
                (svex-env-<<= impl-nextstate spec-nextstate)
                )))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p-implies-netevalcomp-p)
                                   (<fn>
                                    phase-fsm-composition-p-implies-<<=-ideal-fsm
                                    svex-alist-partial-monotonic-when-netevalcomp-p))
            :use ((:instance phase-fsm-composition-p-implies-<<=-ideal-fsm
                   (override-env (b* (((flatnorm-res x)))
                                   (intermediate-override-env2
                                    (svarlist-to-override-triples
                                     (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))
                                    (svar-override-triplelist->testvars
                                     (svarlist-to-override-triples
                                      (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
                                    override-env
                                    ref-env
                                    (svex-alist-eval (base-fsm->values (flatnorm->ideal-fsm x)) ref-env)))))
                  (:instance svex-alist-partial-monotonic-when-netevalcomp-p
                   (network (b* (((phase-fsm-config config))
                                 ((mv overridden-assigns ?overridden-delays)
                                  (svtv-flatnorm-apply-overrides x config.override-config)))
                              overridden-assigns))
                   (comp (base-fsm->values approx-fsm))
                   (params (svar-override-triplelist->testvars
                            (svarlist-to-override-triples
                             (svtv-assigns-override-vars
                              (flatnorm-res->assigns x)
                              (phase-fsm-config->override-config config)))))))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (e/d (svtv-flatnorm-apply-overrides
                                   svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples
                                   svex-env-<<=-transitive-2
                                   svex-env-<<=-transitive-1
                                   eval-when-svex-alist-partial-monotonic
                                   <fn>)
                                  ( phase-fsm-composition-p-implies-<<=-ideal-fsm
                                    svex-alist-partial-monotonic-when-netevalcomp-p)))))
    :otf-flg t)


  ;; We can weaken the conditions involving the override-env above by only
  ;; demanding that the override-env is <<= the ref-env/spec-values --
  (defret phase-fsm-composition-p-implies-<<=-ideal-fsm-of-flatten/normalize
    :pre-bind (((mv ?err ?res ?moddb ?aliases)
                (svtv-design-flatten design :moddb nil
                                     :aliases nil))
               (x (svtv-normalize-assigns flatten aliases flatnorm-setup)))
    (b* (((flatnorm-res x))
         ((base-fsm fsm))
         ((base-fsm approx-fsm))
         (spec-values (svex-alist-eval fsm.values ref-env))
         (?spec-nextstate (svex-alist-eval fsm.values ref-env))
         (impl-values (svex-alist-eval approx-fsm.values override-env))
         (?impl-nextstate (svex-alist-eval approx-fsm.values override-env))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
      (implies (and
                (not err)
                (modalist-addr-p (design->modalist design))
                (flatnorm-setup->monotonify flatnorm-setup)
                
                ;; approx-fsm well formed
                (phase-fsm-composition-p approx-fsm x config)

                ;; override env well formed
                (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
                                        override-env ref-env)
                (svar-override-triplelist-env-ok
                 triples
                 override-env spec-values))

               (and 
                (svex-env-<<= impl-values spec-values)
                (svex-env-<<= impl-nextstate spec-nextstate)
                )))
    :hints(("Goal" :in-theory (disable <fn>))))


  (defret phase-fsm-composition-p-implies-<<=-ideal-fsm-of-flatten/normalize-weaken
    :pre-bind (((mv ?err ?res ?moddb ?aliases)
                (svtv-design-flatten design :moddb nil
                                     :aliases nil))
               (x (svtv-normalize-assigns flatten aliases flatnorm-setup)))
    (b* (((flatnorm-res x))
         ((base-fsm fsm))
         ((base-fsm approx-fsm))
         (spec-values (svex-alist-eval fsm.values ref-env))
         (?spec-nextstate (svex-alist-eval fsm.values ref-env))
         (impl-values (svex-alist-eval approx-fsm.values override-env))
         (?impl-nextstate (svex-alist-eval approx-fsm.values override-env))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
      (implies (and
                (not err)
                (modalist-addr-p (design->modalist design))
                (flatnorm-setup->monotonify flatnorm-setup)
                
                ;; approx-fsm well formed
                (phase-fsm-composition-p approx-fsm x config)

                ;; override env well formed
                (svar-override-triplelist-env-ok-<<= triples override-env spec-values)
                (svex-env-<<= (svex-env-removekeys
                               (svar-override-triplelist-override-vars triples) override-env)
                              ref-env))

               (and 
                (svex-env-<<= impl-values spec-values)
                (svex-env-<<= impl-nextstate spec-nextstate)
                )))
    :hints(("Goal" :in-theory (disable <fn>)
            :do-not-induct t))
    :otf-flg t))
 
