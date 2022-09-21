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
(include-book "svtv-stobj-pipeline-monotonicity")

(local (include-book "../svex/alist-thms"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
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



(defsection svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys


  (local (defthm cdr-under-svex-alist-eval-equiv-when-not-consp-car
           (implies (not (consp (car y)))
                    (svex-alist-eval-equiv (cdr y) y))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup
                                             svex-alist-fix)))))

  (local (defthm cdr-under-svex-alist-eval-equiv-when-not-svar-p-caar
           (implies (not (svar-p (caar y)))
                    (svex-alist-eval-equiv (cdr y) y))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup
                                             svex-alist-fix)))))


  (local (defthm svex-alist-eval-equiv-expand-when-same-keys
           (implies (and (consp y)
                         (consp (car y))
                         (svar-p v)
                         (equal (caar y) v)
                         (not (svex-lookup v (cdr y)))
                         (not (svex-lookup v x)))
                    (equal (svex-alist-eval-equiv (cons (cons v val) x) y)
                           (and (svex-eval-equiv val (cdar y))
                                (svex-alist-eval-equiv x (cdr y)))))
           :hints (("goal" :cases ((svex-alist-eval-equiv (cons (cons v val) x) y))
                    :in-theory (e/d (svex-lookup-redef))
                    :do-not-induct t)
                   (and stable-under-simplificationp
                        (b* ((lit (assoc 'svex-alist-eval-equiv clause))
                             (?wit `(svex-alist-eval-equiv-witness . ,(cdr lit))))
                          (if lit
                              `(:expand (,lit)
                                :use ((:instance svex-alist-eval-equiv-necc
                                       (var ,wit) (x (cons (cons (caar y) val) x)) (y y)))
                                :in-theory (e/d (svex-lookup-redef)
                                                
                                                (SVEX-ALIST-EVAL-EQUIV-IMPLIES-IFF-SVEX-LOOKUP-2
                                                 SVEX-ALIST-SAME-KEYS-IMPLIES-IFF-SVEX-LOOKUP-2
                                                 svex-alist-eval-equiv-necc
                                                 svex-alist-eval-equiv-implies-svex-eval-equiv-svex-lookup-2))
                                )
                            `(:use ((:instance svex-alist-eval-equiv-necc
                                     (var (caar y)) (x (cons (cons (caar y) val) x)) (y y)))
                              :in-theory (e/d (svex-lookup-redef)
                                              (SVEX-ALIST-EVAL-EQUIV-IMPLIES-IFF-SVEX-LOOKUP-2
                                               SVEX-ALIST-SAME-KEYS-IMPLIES-IFF-SVEX-LOOKUP-2
                                               svex-alist-eval-equiv-necc
                                               svex-alist-eval-equiv-implies-svex-eval-equiv-svex-lookup-2)))))))
           :otf-flg t))

  (local (defthm svex-width-of-lookup-when-svex-alist-width
           (implies (and (svex-alist-width x)
                         (svex-lookup k x))
                    (svex-width (svex-lookup k x)))
           :hints(("Goal" :in-theory (enable svex-lookup-redef
                                             svex-alist-width
                                             svex-width-sum)))))

  (local (defthm svex-width-of-x
           (equal (svex-width (svex-x)) 1)
           :hints (("goal" :use ((:instance svex-width-limited-p (width 1) (x (svex-x))))
                    :in-theory (enable svex-width-unique)))))
                         
  
  (local
   (defthmd svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys-lemma
     (implies (and (svex-alist-width x)
                   (svex-alist-eval-equiv (svex-alist-extract (svex-alist-keys y) x) y)
                   (no-duplicatesp-equal (svex-alist-keys y)))
              (svex-alist-width y))
     :hints (("goal" :induct (svex-alist-keys y)
              :in-theory (enable svex-alist-keys svex-alist-extract
                                 svex-alist-width
                                 svex-width-sum)))))

  (local (defthm svex-alist-eval-equiv-of-extract-when-svex-alist-eval-equiv
           (implies (svex-alist-eval-equiv x y)
                    (svex-alist-eval-equiv (svex-alist-extract (svex-alist-keys y) x) y))
           :hints (("Goal" :expand ((svex-alist-eval-equiv (svex-alist-extract (svex-alist-keys x) x) x))))))
  
  (defthmd svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys
    (implies (and (no-duplicatesp-equal (svex-alist-keys y))
                  (svex-alist-eval-equiv x y)
                  (svex-alist-width x))
             (svex-alist-width y))
    :hints (("goal" :use svex-alist-width-when-svex-alist-eval-equiv-and-no-duplicate-keys-lemma))))


(encapsulate nil
  (local (defthm testvar-of-lookup-refvar-member-of-testvars
           (implies (member-equal (svar-fix v) (svar-override-triplelist->refvars x))
                    (member-equal (svar-override-triple->testvar
                                   (svar-override-triplelist-lookup-refvar v x))
                                  (svar-override-triplelist->testvars x)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->testvars
                                             svar-override-triplelist-lookup-refvar
                                             svar-override-triplelist->refvars)))))


  (defthm svex-alist-partial-monotonic-of-svar-override-triplelist->override-alist
    (svex-alist-partial-monotonic (svar-override-triplelist->testvars x)
                                  (svar-override-triplelist->override-alist x))
    :hints(("Goal" :in-theory (enable svex-alist-partial-monotonic-by-eval
                                      svex-apply
                                      svex-eval))
           (and stable-under-simplificationp
                (b* ((envs '(svex-alist-partial-monotonic-eval-witness (svar-override-triplelist->testvars x)
                                                                       (svar-override-triplelist->override-alist x)))
                     (ev1 `(svex-alist-eval (svar-override-triplelist->override-alist x) (mv-nth 0 ,envs)))
                     (ev2 `(svex-alist-eval (svar-override-triplelist->override-alist x) (mv-nth 1 ,envs)))
                     (key `(svex-env-<<=-witness ,ev1 ,ev2))
                     (testvar `(svar-override-triple->testvar (svar-override-triplelist-lookup-refvar ,key x))))
                  `(:expand ((svex-env-<<= ,ev1 ,ev2))
                    :use ((:instance svex-env-lookup-of-svex-env-extract
                           (v ,testvar)
                           (vars (svar-override-triplelist->testvars x))
                           (env (mv-nth 0 ,envs)))
                          (:instance svex-env-lookup-of-svex-env-extract
                           (v ,testvar)
                           (vars (svar-override-triplelist->testvars x))
                           (env (mv-nth 1 ,envs))))
                    :in-theory (e/d (svex-apply
                                     svex-eval)
                                    (svex-env-lookup-of-svex-env-extract))))))))


(defthm svex-alist-compose-preserves-partial-monotonic-when-params-not-composed
  (implies (and (svex-alist-partial-monotonic params x)
                (svex-alist-partial-monotonic params y)
                (not (intersectp-equal (svarlist-fix params) (svex-alist-keys y))))
           (svex-alist-partial-monotonic params (svex-alist-compose x y)))
  :hints ((b* ((lit '(svex-alist-partial-monotonic params (svex-alist-compose x y)))
               (?envs `(svex-alist-partial-monotonic-eval-witness . ,(cdr lit))))
            `(:expand ((:with svex-alist-partial-monotonic-by-eval ,lit))))))




(defthm svex-env-removekeys-when-not-intersecting
  (implies (not (intersectp-equal (double-rewrite (alist-keys (svex-env-fix x))) (svarlist-fix vars)))
           (equal (svex-env-removekeys vars x)
                  (svex-env-fix x)))
  :hints(("Goal" :in-theory (enable svex-env-removekeys
                                    svex-env-fix))))


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

  ;; We want to eventually prove that when we evaluate an approximate-fixpoint
  ;; FSM on an environment with overrides and Xes taking the place of free
  ;; variables, the (non-X) results hold for our ideal, non-override FSM.

  ;; The steps in this derivation:
  ;; 1. ideal-fsm == ideal-fsm with overrides -- svex-alist-eval-override-fixpoint-equivalent-to-reference-fixpoint
  ;; 2. ideal-fsm-with-overrides >>= approximate-fsm with overrides -- netevalcomp-implies-<<=-fixpoint
  ;; 3. approximate-fsm with overrides evaluated on exact env >>= approximate-fsm with overrides evaluated on lesser env.
  ;;               -- this is basically just that a netevalcomp-p has partial monotonicity over everything but the test vars.

  ;; Then the trick for putting them all together is to match envs -- that is,
  ;; construct from the lesser override env of the last step and the reference
  ;; env of the first step an intermediate env that satisfies the requirements
  ;; of the first step's override env.

  ;; 1. ideal-fsm == ideal-fsm with overrides
  (local
   (defthm flatnorm->ideal-fsm-equivalent-to-ideal-fsm-with-overrides-values
     (b* (((flatnorm-res x))
          ((base-fsm ideal-fsm) (flatnorm->ideal-fsm x))
          (override-flatnorm
           (change-flatnorm-res x
                                :assigns (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))
                                :delays (svex-alist-compose x.delays (svar-override-triplelist->override-alist triples))))
          ((base-fsm override-fsm) (flatnorm->ideal-fsm override-flatnorm))
          (override-vars (svar-override-triplelist-override-vars triples))
          (spec-values (svex-alist-eval ideal-fsm.values ref-env))
          (impl-values (svex-alist-eval override-fsm.values override-env)))
       (implies (and
                 ;; since this is just a lemma for later in this encapsulate we'll explicitly bind ref-env to what we need
                 (bind-free '((ref-env . ref-env)) (ref-env))
                     
                 (svex-envs-agree-except override-vars override-env ref-env)
                 (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                 (no-duplicatesp-equal (svex-alist-keys x.assigns))
                 (svex-alist-width x.assigns)
                 (svar-override-triplelist-env-ok triples override-env spec-values)
                 (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys x.assigns))
                 (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys x.assigns)))
                 (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars x.assigns))))
                (svex-envs-equivalent impl-values spec-values)))))


  (local (defthm svex-env-extract-append-when-agree-except-3
           (implies (and (svex-envs-agree-except vars env1 env2)
                         (not (intersectp-equal (svarlist-fix ev-vars) (svarlist-fix vars))))
                    (svex-envs-similar (svex-env-extract ev-vars (append enva envb env1))
                                       (svex-env-extract ev-vars (append enva envb env2))))
           :hints(("Goal" :in-theory (enable svex-envs-similar
                                             svex-envs-agree-except-implies)))))

  (local (defthm append-extract-x-under-svex-envs-similar-3
           (implies (subsetp-equal (svarlist-fix vars) (alist-keys (svex-env-fix x)))
                    (svex-envs-similar (append (svex-env-extract vars x) x y) (append x y)))
           :hints(("Goal" :in-theory (enable svex-envs-similar
                                             svex-env-boundp-iff-member-alist-keys)))))

  (local
   (defthm svex-alist-eval-equivalent-when-extract-vars-similar-double-rw
     (implies
      (double-rewrite (svex-envs-similar (svex-env-extract (svex-alist-vars x) env2)
                                         (svex-env-extract (svex-alist-vars x) env)))
      (equal (svex-envs-equivalent (svex-alist-eval x env2)
                                   (svex-alist-eval x env))
             t))
     :hints (("goal" :in-theory (enable svex-alist-eval-equivalent-when-extract-vars-similar)))))

  (local
   (defthm flatnorm->ideal-fsm-equivalent-to-ideal-fsm-with-overrides-nextstate
     (b* (((flatnorm-res x))
          ((base-fsm ideal-fsm) (flatnorm->ideal-fsm x))
          (override-flatnorm
           (change-flatnorm-res x
                                :assigns (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))
                                :delays (svex-alist-compose x.delays (svar-override-triplelist->override-alist triples))))
          ((base-fsm override-fsm) (flatnorm->ideal-fsm override-flatnorm))
          (override-vars (svar-override-triplelist-override-vars triples))
          (spec-values (svex-alist-eval ideal-fsm.values ref-env))
          (spec-nextstate (svex-alist-eval ideal-fsm.nextstate ref-env))
          (impl-nextstate (svex-alist-eval override-fsm.nextstate override-env)))
       (implies (and (bind-free '((ref-env . ref-env)) (ref-env))
                     (svex-envs-agree-except override-vars override-env ref-env)
                     (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                     (no-duplicatesp-equal (svex-alist-keys x.assigns))
                     (svex-alist-width x.assigns)
                     (svar-override-triplelist-env-ok triples override-env spec-values)
                     (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys x.assigns))
                     (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys x.assigns)))
                     (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars x.assigns)))
                     (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars x.delays))))
                (svex-envs-equivalent impl-nextstate spec-nextstate)))))

  ;; 2. ideal-fsm-with-overrides >>= approximate-fsm with overrides (doesn't matter whether it's with overrides or not...)
  (local
   (defthm flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition-values
     (b* (((flatnorm-res x))
          (triples
           (svarlist-to-override-triples
            (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
          (override-flatnorm
           (change-flatnorm-res x
                                :assigns (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))
                                :delays (svex-alist-compose x.delays (svar-override-triplelist->override-alist triples))))
          ((base-fsm ideal-fsm) (flatnorm->ideal-fsm override-flatnorm))
          ((base-fsm approx-fsm)))
       (implies (and (phase-fsm-composition-p approx-fsm x config)
                    
                     (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                     (svex-alist-width x.assigns)
                     (no-duplicatesp-equal (svex-alist-keys x.assigns))
                     (svarlist-addr-p (svex-alist-vars x.assigns))
                     (svarlist-addr-p (svex-alist-keys x.assigns)))
                (svex-alist-<<= approx-fsm.values ideal-fsm.values)))
     ;; (implies 
     ;;  (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.delays)
     ;;  (svex-env-<<= (svex-alist-eval approx-fsm.nextstate env)
     ;;                (svex-alist-eval ideal-fsm.nextstate env))))))
     :hints(("Goal" :in-theory (enable phase-fsm-composition-p
                                       svtv-flatnorm-apply-overrides
                                       svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples)
             :use ((:instance netevalcomp-p-implies-<<=-fixpoint
                    (network
                     (b* (((flatnorm-res x))
                          (triples
                           (svarlist-to-override-triples
                            (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
                       (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))))
                    (comp (base-fsm->values approx-fsm))))))))


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


  (local (defthmd svex-lookup-when-not-member-keys
           (implies (not (member-equal (svar-fix v) (svex-alist-keys x)))
                    (not (svex-lookup v x)))))
  
  (local (defthm svex-alist-removekeys-of-all-keys
           (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix keys))
                    (svex-alist-eval-equiv (svex-alist-removekeys keys x) nil))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup-when-not-member-keys)))))

  
  (local
   (defthm flatnorm->ideal-fsm-overrides->>=-phase-fsm-composition-nextstate
     (b* (((flatnorm-res x))
          (triples
           (svarlist-to-override-triples
            (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
          (override-flatnorm
           (change-flatnorm-res x
                                :assigns (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))
                                :delays (svex-alist-compose x.delays (svar-override-triplelist->override-alist triples))))
          ((base-fsm ideal-fsm) (flatnorm->ideal-fsm override-flatnorm))
          ((base-fsm approx-fsm)))
       (implies (and (phase-fsm-composition-p approx-fsm x config)
                    
                     (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.assigns)
                     (svex-alist-monotonic-on-vars (svex-alist-keys x.assigns) x.delays)
                    
                     (svex-alist-width x.assigns)
                     (no-duplicatesp-equal (svex-alist-keys x.assigns))
                     (svarlist-addr-p (svex-alist-vars x.assigns))
                     (svarlist-addr-p (svex-alist-keys x.assigns))
                     (svarlist-addr-p (svex-alist-vars x.delays)))
                (svex-alist-<<= approx-fsm.nextstate ideal-fsm.nextstate)))
     :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                     svtv-flatnorm-apply-overrides
                                     svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples)
                                    (
                                     svtv-assigns-override-vars-subset-of-keys
                                     svar-override-triplelist->override-alist-monotonic-on-vars))
             :use ((:instance svar-override-triplelist->override-alist-monotonic-on-vars
                    (x (b* (((flatnorm-res x)))
                         (svarlist-to-override-triples
                          (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
                    (vars (svex-alist-keys (flatnorm-res->assigns x))))
                   (:instance svtv-assigns-override-vars-subset-of-keys
                    (assigns (flatnorm-res->assigns x))
                    (config (phase-fsm-config->override-config config))))))))


  
  ;; 3. approximate-fsm with overrides evaluated on exact env >>= approximate-fsm with overrides evaluated on lesser env.
  ;;    -- this actually doesn't have to do with this function particularly and could be moved somewhere else
  (local (defthm svex-compose-alist-selfbound-keys-when-no-intersect
           (implies (not (intersectp-equal (svarlist-fix keys) (svex-alist-keys x)))
                    (svex-compose-alist-selfbound-keys-p keys x))
           :hints(("Goal" :in-theory (enable svex-compose-alist-selfbound-keys-p svex-compose-lookup)))))

  (defthm phase-fsm-composition-partial-monotonic-values
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svex-alist-monotonic-p x.assigns)
                    (svarlist-addr-p (svex-alist-vars x.assigns))
                    (svarlist-addr-p (svex-alist-keys x.assigns)))
               (svex-alist-partial-monotonic
                (svar-override-triplelist->testvars triples)
                approx-fsm.values)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples
                                    svex-alist-partial-monotonic-when-netevalcomp-p)))))

  (defthm phase-fsm-composition-partial-monotonic-nextstate
    (b* (((flatnorm-res x))
         ((base-fsm approx-fsm))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config)))))
      (implies (and (phase-fsm-composition-p approx-fsm x config)
                    (svex-alist-monotonic-p x.assigns)
                    (svex-alist-monotonic-p x.delays)
                    (svarlist-addr-p (svex-alist-vars x.assigns))
                    (svarlist-addr-p (svex-alist-keys x.assigns))
                    (svarlist-addr-p (svex-alist-vars x.delays)))
               (svex-alist-partial-monotonic
                (svar-override-triplelist->testvars triples)
                approx-fsm.nextstate)))
    :hints(("Goal" :in-theory (e/d (phase-fsm-composition-p
                                    svtv-flatnorm-apply-overrides
                                    svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples
                                    svex-alist-partial-monotonic-when-netevalcomp-p)))))



  (defret svex-alist-keys-of-<fn>-values
    (equal (svex-alist-keys (base-fsm->values fsm))
           (svex-alist-keys (flatnorm-res->assigns x))))

  (defret svex-alist-keys-of-<fn>-nextstate
    (equal (svex-alist-keys (base-fsm->nextstate fsm))
           (svex-alist-keys (flatnorm-res->delays x))))
  

  ;; Now to put all three such steps together.
  
  (defthm flatnorm->ideal-fsm-values-refines-overriden-approximation
    (b* (((flatnorm-res x))
         ((base-fsm ideal-fsm) (flatnorm->ideal-fsm x))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
         ((base-fsm approx-fsm))
         (override-vars (svar-override-triplelist-override-vars triples))
         (spec-values (svex-alist-eval ideal-fsm.values ref-env))
         (impl-values (svex-alist-eval approx-fsm.values override-env)))
      (implies (and (svex-alist-monotonic-p x.assigns)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svex-alist-width x.assigns)
                    (svarlist-addr-p (svex-alist-vars x.assigns))
                    (svarlist-addr-p (svex-alist-keys x.assigns))

                    (phase-fsm-composition-p approx-fsm x config)

                    (svex-env-<<= (svex-env-removekeys override-vars override-env) ref-env)
                    (svar-override-triplelist-env-ok-<<= triples override-env spec-values))
               (svex-env-<<= impl-values spec-values)))
    :hints (("goal" :in-theory (disable flatnorm->ideal-fsm)
             :do-not-induct t)
            (acl2::use-termhint
             (b* (((flatnorm-res x))
                  ((base-fsm ideal-fsm) (flatnorm->ideal-fsm x))
                  ((base-fsm approx-fsm))
                  (triples
                   (svarlist-to-override-triples
                    (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
                  (spec-values (svex-alist-eval ideal-fsm.values ref-env))
                  (testvars (svar-override-triplelist->testvars triples))
                  (intermediate-env (intermediate-override-env2
                                     triples
                                     testvars
                                     override-env
                                     ref-env
                                     spec-values))
                  (override-flatnorm
                   (change-flatnorm-res x
                                        :assigns (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))
                                        :delays (svex-alist-compose x.delays (svar-override-triplelist->override-alist triples))))
                  ((base-fsm ideal-override-fsm) (flatnorm->ideal-fsm override-flatnorm)))
               `(:use ((:instance eval-when-svex-alist-partial-monotonic
                        (param-keys ,(acl2::hq testvars))
                        (env1 override-env)
                        (env2 ,(acl2::hq intermediate-env))
                        (x ,(acl2::hq approx-fsm.values)))
                       (:instance svex-alist-<<=-necc
                        (env ,(acl2::hq intermediate-env))
                        (x ,(acl2::hq approx-fsm.values))
                        (y ,(acl2::hq ideal-override-fsm.values))))
                 :in-theory (e/d (svex-env-<<=-transitive-2
                                  svex-env-<<=-transitive-1)
                                 (eval-when-svex-alist-partial-monotonic
                                  svex-alist-<<=-necc
                                  flatnorm->ideal-fsm))))))
    :otf-flg t)

  (defthm flatnorm->ideal-fsm-nextstate-refines-overriden-approximation
    (b* (((flatnorm-res x))
         ((base-fsm ideal-fsm) (flatnorm->ideal-fsm x))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
         ((base-fsm approx-fsm))
         (override-vars (svar-override-triplelist-override-vars triples))
         (spec-values (svex-alist-eval ideal-fsm.values ref-env))
         (spec-nextstate (svex-alist-eval ideal-fsm.nextstate ref-env))
         (impl-nextstate (svex-alist-eval approx-fsm.nextstate override-env)))
      (implies (and (svex-alist-monotonic-p x.assigns)
                    (svex-alist-monotonic-p x.delays)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svex-alist-width x.assigns)
                    (svarlist-addr-p (svex-alist-vars x.assigns))
                    (svarlist-addr-p (svex-alist-keys x.assigns))
                    (svarlist-addr-p (svex-alist-vars x.delays))

                    (phase-fsm-composition-p approx-fsm x config)
                    
                    (svex-env-<<= (svex-env-removekeys override-vars override-env) ref-env)
                    (svar-override-triplelist-env-ok-<<= triples override-env spec-values))
               (svex-env-<<= impl-nextstate spec-nextstate)))
    :hints (("goal" :in-theory (disable flatnorm->ideal-fsm)
             :do-not-induct t)
            (acl2::use-termhint
             (b* (((flatnorm-res x))
                  ((base-fsm ideal-fsm) (flatnorm->ideal-fsm x))
                  ((base-fsm approx-fsm))
                  (triples
                   (svarlist-to-override-triples
                    (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
                  (spec-values (svex-alist-eval ideal-fsm.values ref-env))
                  (testvars (svar-override-triplelist->testvars triples))
                  (intermediate-env (intermediate-override-env2
                                     triples
                                     testvars
                                     override-env
                                     ref-env
                                     spec-values))
                  (override-flatnorm
                   (change-flatnorm-res x
                                        :assigns (svex-alist-compose x.assigns (svar-override-triplelist->override-alist triples))
                                        :delays (svex-alist-compose x.delays (svar-override-triplelist->override-alist triples))))
                  ((base-fsm ideal-override-fsm) (flatnorm->ideal-fsm override-flatnorm)))
               `(:use ((:instance eval-when-svex-alist-partial-monotonic
                        (param-keys ,(acl2::hq testvars))
                        (env1 override-env)
                        (env2 ,(acl2::hq intermediate-env))
                        (x ,(acl2::hq approx-fsm.nextstate)))
                       (:instance svex-alist-<<=-necc
                        (env ,(acl2::hq intermediate-env))
                        (x ,(acl2::hq approx-fsm.nextstate))
                        (y ,(acl2::hq ideal-override-fsm.nextstate))))
                 :in-theory (e/d (svex-env-<<=-transitive-2
                                  svex-env-<<=-transitive-1)
                                 (eval-when-svex-alist-partial-monotonic
                                  svex-alist-<<=-necc
                                  flatnorm->ideal-fsm))))))
    :otf-flg t)

  (local (defun base-fsm-eval-2-ind (ref-inputs ref-initst ideal-fsm override-inputs override-initst approx-fsm)
           (if (atom ref-inputs)
               (list ref-initst override-initst)
             (base-fsm-eval-2-ind
              (cdr ref-inputs)
              (base-fsm-step (car ref-inputs) ref-initst (base-fsm->nextstate ideal-fsm))
              ideal-fsm
              (cdr override-inputs)
              (base-fsm-step (car override-inputs) override-initst (base-fsm->nextstate approx-fsm))
              approx-fsm))))


  (local (defthm nextstate-keys-when-phase-fsm-composition-p
           (implies (phase-fsm-composition-p approx-fsm x config)
                    (set-equiv (svex-alist-keys (base-fsm->nextstate approx-fsm))
                               (svex-alist-keys (flatnorm-res->delays x))))
           :hints(("Goal" :in-theory (enable phase-fsm-composition-p
                                             svtv-flatnorm-apply-overrides)))))

  (local (defthm svar-override-triplelist-env-ok-<<=-of-append-irrel
           (implies (not (intersectp-equal (svar-override-triplelist-override-vars triples)
                                           (double-rewrite (alist-keys (svex-env-fix a)))))
                    (equal (svar-override-triplelist-env-ok-<<= triples (append a b) c)
                           (svar-override-triplelist-env-ok-<<= triples b c)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-env-ok-<<=
                                             svar-override-triplelist-override-vars
                                             svex-env-boundp-iff-member-alist-keys)))))
  
  (defthm base-fsm-eval-of-flatnorm->ideal-fsm-refines-overridden-approximation
    (b* (((flatnorm-res x))
         (ideal-fsm (flatnorm->ideal-fsm x))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
         (override-vars (svar-override-triplelist-override-vars triples))
         (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
         (impl-values (base-fsm-eval override-inputs override-initst approx-fsm)))
      (implies (and (svex-alist-monotonic-p x.assigns)
                    (svex-alist-monotonic-p x.delays)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svex-alist-width x.assigns)
                    (svarlist-addr-p (svex-alist-vars x.assigns))
                    (svarlist-addr-p (svex-alist-keys x.assigns))
                    (svarlist-addr-p (svex-alist-vars x.delays))
                    (svarlist-addr-p (svex-alist-keys x.delays))

                    (phase-fsm-composition-p approx-fsm x config)

                    (equal (len override-inputs) (len ref-inputs))
                    (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs) ref-inputs)
                    (svar-override-triplelist-envlists-ok-<<= triples override-inputs spec-values)
                    (svex-env-<<= override-initst ref-initst))
               (svex-envlist-<<= impl-values spec-values)))
    :hints(("Goal" :in-theory (e/d (base-fsm-step-env
                                      base-fsm-step
                                      base-fsm-step-outs
                                      svar-override-triplelist-envlists-ok-<<=
                                      svex-envlist-<<=
                                      svex-envlist-removekeys)
                                   (flatnorm->ideal-fsm))
            :induct (base-fsm-eval-2-ind ref-inputs ref-initst (flatnorm->ideal-fsm x) override-inputs override-initst approx-fsm)
            :expand ((:free (fsm) (base-fsm-eval ref-inputs ref-initst fsm))
                     (:free (fsm) (base-fsm-eval override-inputs override-initst fsm))))))


  (defthm base-fsm-final-state-of-flatnorm->ideal-fsm-refines-overridden-approximation
    (b* (((flatnorm-res x))
         (ideal-fsm (flatnorm->ideal-fsm x))
         (triples
          (svarlist-to-override-triples
           (svtv-assigns-override-vars x.assigns (phase-fsm-config->override-config config))))
         (override-vars (svar-override-triplelist-override-vars triples))
         (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
         (spec-finalstate (base-fsm-final-state ref-inputs ref-initst (base-fsm->nextstate ideal-fsm)))
         (impl-finalstate (base-fsm-final-state override-inputs override-initst (base-fsm->nextstate approx-fsm))))
      (implies (and (svex-alist-monotonic-p x.assigns)
                    (svex-alist-monotonic-p x.delays)
                    (no-duplicatesp-equal (svex-alist-keys x.assigns))
                    (svex-alist-width x.assigns)
                    (svarlist-addr-p (svex-alist-vars x.assigns))
                    (svarlist-addr-p (svex-alist-keys x.assigns))
                    (svarlist-addr-p (svex-alist-vars x.delays))
                    (svarlist-addr-p (svex-alist-keys x.delays))

                    (phase-fsm-composition-p approx-fsm x config)

                    (equal (len override-inputs) (len ref-inputs))
                    (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs) ref-inputs)
                    (svar-override-triplelist-envlists-ok-<<= triples override-inputs spec-values)
                    (svex-env-<<= override-initst ref-initst))
               (svex-env-<<= impl-finalstate spec-finalstate)))
    :hints(("Goal" :in-theory (e/d (base-fsm-step-env
                                      base-fsm-step
                                      base-fsm-step-outs
                                      svar-override-triplelist-envlists-ok-<<=
                                      svex-envlist-<<=
                                      svex-envlist-removekeys)
                                   (flatnorm->ideal-fsm))
            :induct (base-fsm-eval-2-ind ref-inputs ref-initst (flatnorm->ideal-fsm x) override-inputs override-initst approx-fsm)
            :expand ((:free (fsm) (base-fsm-final-state ref-inputs ref-initst fsm))
                     (:free (fsm) (base-fsm-final-state override-inputs override-initst fsm)))))))



