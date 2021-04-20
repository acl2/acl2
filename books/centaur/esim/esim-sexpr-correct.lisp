; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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


; esim-sexpr-correct.lisp -- proof that esim-sexpr implements the simple
; semantics of esim
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "esim-sexpr")
(include-book "esim-spec")
(local (include-book "esim-sexpr-support-thms"))
(local (include-book "centaur/4v-sexpr/sexpr-advanced" :dir :system))
(local (in-theory (disable set::double-containment)))
(local (in-theory (disable occmap)))

(defthm hons-assoc-equal-4v-sexpr-alist-extract
  (equal (hons-assoc-equal k (4v-sexpr-alist-extract keys al))
         (and (member-equal k keys)
              (cons k (cdr (hons-assoc-equal k al))))))

(defthm 4v-sexpr-alist-extract-subset
  (implies (subsetp-equal keys keys1)
           (equal (4v-sexpr-alist-extract keys (4v-sexpr-alist-extract keys1 al))
                  (4v-sexpr-alist-extract keys al)))
  :hints (("goal" :in-theory (e/d (subsetp-equal)))))



(defthm 4v-fix-4v-fix
  (equal (4v-fix (4v-fix x))
         (4v-fix x)))


(defthm 4v-sexpr-eval-alist-sexpr-pat-alist-translate
  (equal (4v-sexpr-eval-alist
          (sexpr-pat-alist-translate pat1 pat2 al acc)
          env)
         (4v-pat-alist-translate
          pat1 pat2
          (4v-sexpr-eval-alist al env)
          (4v-sexpr-eval-alist acc env)))
  :hints(("Goal" :in-theory (e/d (sexpr-pat-alist-translate)
                                 (4v-sexpr-eval))
          :expand ((4v-sexpr-eval '(x) env)))))

(defthm 4v-sexpr-eval-alist-4v-sexpr-alist-extract
  (equal (4v-sexpr-eval-alist (4v-sexpr-alist-extract keys al) env)
         (4v-alist-extract keys (4v-sexpr-eval-alist al env)))
  :hints(("Goal" :in-theory (disable 4v-sexpr-eval)
          :expand ((4v-sexpr-eval '(x) env)))))

(defthm 4v-sexpr-eval-of-eapply-sexpr
  (b* (((mv sexpr-nst sexpr-out)
        (eapply-sexpr ;; sig-al st-al i s o
                      x))
       ((mv spec-nst spec-out)
        (eapply-spec env x)))
    (and (equal (4v-sexpr-eval-alist sexpr-nst env)
                spec-nst)
         (equal (4v-sexpr-eval-alist sexpr-out env)
                spec-out)))
  :hints(("Goal" :in-theory (disable* (:ruleset 4v-op-defs)
                                      (:definition 4v-sexpr-eval)
                                      default-car default-cdr
                                      ;var-assoc-key 4vp
                                      ; 4v-sexpr-eval-lookup-in-atom-val-alist
                                      sexpr-var-val-alistp
                                      ; alist-equiv-cdr-x-when-not-consp-car
                                      4v-sexpr-eval-alist
                                      hons-assoc-equal
                                      ; 4v-fix-when-4vp
                                      4v-sexpr-eval-list
                                      4v-sexpr-alist-extract
                                      4v-alist-extract
                                      len nth-with-large-index
                                      (:rules-of-class :type-prescription :here))
          :do-not-induct t
          :expand ((:free (a b) (4v-sexpr-eval (cons a b) env))
                   (4v-sexpr-eval-alist nil env)
                   (:free (a b) (4v-sexpr-eval-alist (cons a b) env))
                   (:free (x a b) (hons-assoc-equal x (cons a b)))
                   (:free (x) (hons-assoc-equal x nil))
                   (:free (a b env) (4v-sexpr-eval-list (cons a b) env))))))





(defthm 4v-alist-extract-append
  (equal (4v-alist-extract (append a b) al)
         (append (4v-alist-extract a al)
                 (4v-alist-extract b al))))

(defthm 4v-sexpr-eval-alist-of-pat->al-id
  (equal (4v-sexpr-eval-alist
          (pat->al keys keys nil)
          al)
         (4v-alist-extract (pat-flatten1 keys) al)))

(defthm 4v-alist-extract-when-not-intersecting-append-1
  (implies (not (intersectp-equal keys (alist-keys al)))
           (4v-env-equiv (4v-alist-extract keys (append al al1))
                         (4v-alist-extract keys al1)))
  :hints(("Goal" :in-theory (disable 4v-env-equiv-to-key-and-env-equiv))))

(defthm 4v-alist-extract-when-not-intersecting-append-2
  (implies (not (intersectp-equal keys (alist-keys al1)))
           (4v-env-equiv (4v-alist-extract keys (append al al1))
                         (4v-alist-extract keys al)))
  :hints(("Goal" :in-theory (disable 4v-env-equiv-to-key-and-env-equiv))))



(defthm 4v-alist-extract-from-atom
  (implies (not (consp al))
           (4v-env-equiv (4v-alist-extract keys al)
                         nil))
  :hints ((witness :ruleset 4v-env-equiv-witnessing)))

(defthm 4v-env-equiv-nil
  (implies (not (consp al))
           (equal (4v-env-equiv nil al) t))
  :hints (("goal" :in-theory (disable 4v-env-equiv-to-key-and-env-equiv))
          (witness :ruleset 4v-env-equiv-witnessing)))


(defthm 4v-alist-extract-when-subset
  (implies (subsetp-equal (alist-keys al) keys)
           (4v-env-equiv (4v-alist-extract keys al)
                         al))
  :hints(("Goal" :do-not-induct t
          :in-theory (disable 4v-fix))
         (witness :ruleset 4v-env-equiv-witnessing)
         (and stable-under-simplificationp
              '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                (alist-keys-member-hons-assoc-equal
                                 4v-fix))))
         (set-reasoning)))



(defthm good-esim-modulep-ins-not-intersecting-states
  (implies (good-esim-modulep mod)
           (and (not (intersectp-equal (pat-flatten1 (mod-state mod))
                                       (pat-flatten1 (gpl :i mod))))
                (not (intersectp-equal (pat-flatten1 (gpl :i mod))
                                       (pat-flatten1 (mod-state mod))))))
  :hints (("goal" :in-theory (enable good-esim-modulep))
          (set-reasoning)))

(add-to-ruleset! good-esim-mod-impl
                 '(good-esim-modulep-ins-not-intersecting-states))


(defthm 4v-alist-extract-append-keys-subset-of-first
  (implies (subsetp-equal keys (alist-keys al1))
           (equal (4v-alist-extract keys (append al1 al2))
                  (4v-alist-extract keys al1)))
  :hints(("Goal" :in-theory (enable subsetp-equal))))

(defthm 4v-alist-extract-append-keys-not-intersect-with-first
  (implies (not (intersectp-equal keys (alist-keys al1)))
           (equal (4v-alist-extract keys (append al1 al2))
                  (4v-alist-extract keys al2)))
  :hints(("Goal" :in-theory (e/d (intersectp-equal)
                                 (intersectp-equal-commute)))))


(defthm 4v-alist-extract-subset-of-keys
  (implies (subsetp-equal keys keys1)
           (equal (4v-alist-extract keys (4v-alist-extract keys1 al))
                  (4v-alist-extract keys al))))

(defthm esim-of-4v-alist-extract-sig-al
  (equal (esim-out mod (4v-alist-extract (pat-flatten1 (gpl :i mod)) sig-al)
                   st-al)
         (esim-out mod sig-al st-al))
  :hints (("goal" :expand ((:free (sig-al) (esim-out mod sig-al st-al)))
           :in-theory (disable esim-fixpoint eapply-spec))))

(defthm esim-of-4v-alist-extract-st-al
  (equal (esim-out mod sig-al (4v-alist-extract (pat-flatten1 (mod-state mod)) st-al))
         (esim-out mod sig-al st-al))
  :hints (("goal" :expand ((:free (sig-al) (esim-out mod sig-al st-al)))
           :in-theory (disable esim-fixpoint eapply-spec good-esim-modulep))))

(defthmd 4v-alist-extract-when-4v-alistp-with-same-keys
  (implies (and (4v-alistp al)
                (equal (alist-keys al) keys)
                (no-duplicatesp-equal (alist-keys al)))
           (equal (4v-alist-extract keys al) al))
  :hints(("Goal" :use ((:instance 4v-alistp-with-same-keys-equal
                                  (a (4v-alist-extract keys al))
                                  (b al))))))


(defthm 4v-alistp-4v-sexpr-eval-alist
  (4v-alistp (4v-sexpr-eval-alist al env)))

(add-to-ruleset good-esim-mod-impl
                '(no-duplicatesp-equal-ins-of-good-module
                  no-duplicatesp-equal-sts-of-good-module
                  no-duplicatesp-equal-outs-of-good-module
                  good-esim-modulep-outs-subset-of-driven))

(defthm 4v-alist-extract-of-eapply-spec
  (implies (and (good-esim-modulep mod)
                ;primitivep
                (gpl :x mod))
           (equal (4v-alist-extract (pat-flatten1 (gpl :o mod))
                                    (mv-nth 1 (eapply-spec al (gpl :x mod))))
                  (mv-nth 1 (eapply-spec al (gpl :x mod)))))
  :hints(("Goal" :in-theory (e/d* (4v-alist-extract-when-4v-alistp-with-same-keys
                                   good-esim-primitivep)
                                  ((:ruleset good-esim-mod-impl)
                                   4v-sexpr-eval))
          :expand ((good-esim-modulep mod)))))


(defthm 4v-alist-extract-of-esim-outs
  (implies (good-esim-modulep mod)
           (equal (4v-alist-extract (pat-flatten1 (gpl :o mod))
                                    (esim-out mod sig-al st-al))
                  (esim-out mod sig-al st-al)))
  :hints (("goal" :expand ((:free (sig-al) (esim-out mod sig-al st-al)))
           :in-theory (disable esim-fixpoint eapply-spec good-esim-modulep
                               esim-fixpoint-p 4v-alist-extract))))

(in-theory (disable mod-state))


(defquant esim-sexpr-correct-modp (mod)
  (forall env (b* ((sexpr-out (4v-sexpr-alist-extract
                               (pat-flatten1 (gpl :o mod))
                               (esim-sexpr-general-out mod)))
                   (spec-out  (esim-out mod env env)))
                (4v-env-equiv (4v-sexpr-eval-alist sexpr-out env)
                              spec-out))))






(defthmd append-4v-alist-extract
  (equal (append (4v-alist-extract k1 a)
                 (4v-alist-extract k2 a))
         (4v-alist-extract (append k1 k2) A)))

(defthm eapply-spec-of-appended-extracts
  (implies (and (good-esim-modulep mod)
                (gpl :x mod)) ;; primitivep
           (b* (((mv nst1 out1)
                 (eapply-spec
                  (append (4v-alist-extract (pat-flatten1 (gpl :i mod)) env)
                          (4v-alist-extract (pat-flatten1 (mod-state mod))
                                            env))
                  (gpl :x mod)))
                ((mv nst2 out2) (eapply-spec env (gpl :x mod))))
             (and (equal nst1 nst2)
                  (equal out1 out2))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d** (good-esim-modulep
                              good-esim-primitivep
                              4v-sexpr-vars-list-append
                              eapply-spec cons-equal
                              4v-sexpr-eval-alist-when-agree-on-keys
                              4v-alists-agree-remove-4v-alist-extract
                              4v-alists-agree-self
                              hons-subset-subsetp-equal
                              4v-sexpr-vars-list-append
                              set-equiv-implies-equal-subsetp-1
                              set-equiv-is-an-equivalence
                              subsetp-append1
                              append-4v-alist-extract))
           :expand ((good-esim-modulep mod)))))

;; theorem about 4v-alists-agree and stuff
(defthm esim-sexpr-correct-modp-primitive
  (implies (and (gpl :x mod) ;;primitivep
                (good-esim-modulep mod))
           (esim-sexpr-correct-modp mod))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (esim-sexpr-general-out)
                           (eapply-sexpr good-esim-modulep eapply-spec)))
          (witness :ruleset esim-sexpr-correct-modp-witnessing)))


(defthm esim-of-4v-4v-sexpr-alist-extract-sig-al
  (implies (good-esim-modulep mod)
           (equal (esim-out mod (append
                                 (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                                   sig-al)
                                 al2)
                        st-al)
                  (esim-out mod sig-al st-al)))
  :hints(("Goal" :in-theory (e/d () (esim-fixpoint good-esim-modulep
                                                   eapply-spec))
          :expand ((:free (sig-al) (esim-out mod sig-al st-al))))))

(defthm esim-of-4v-4v-sexpr-alist-extract-st-al
  (implies (good-esim-modulep mod)
           (equal (esim-out mod sig-al
                        (append
                         (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                           al1)
                         al2))
                  (esim-out mod sig-al al2)))
  :hints(("Goal" :in-theory (e/d () (esim-fixpoint good-esim-modulep
                                                   eapply-spec))
          :expand ((:free (st-al) (esim-out mod sig-al st-al))))))


(defthm 4v-sexpr-eval-of-esim-sexpr-out-when-esim-correct-modp1
  (implies (and (esim-sexpr-correct-modp mod)
                (good-esim-modulep mod))
           (b* ((sexpr-out (esim-sexpr-out mod sig-al st-al))
                (spec-out  (esim-out mod
                                     (4v-sexpr-eval-alist sig-al env)
                                     (4v-sexpr-eval-alist st-al env))))
             (4v-env-equiv (4v-sexpr-eval-alist sexpr-out env)
                           spec-out)))
  :hints(("Goal" :in-theory
          (e/d (esim-sexpr-out)
               (eapply-spec eapply-sexpr
                            esim-out esim-out-in-terms-of-least-fixpoint
                            good-esim-modulep esim-sexpr-general-out
                            4v-sexpr-eval 4v-lookup))
          :use ((:instance esim-sexpr-correct-modp-necc
                           (env (append (4v-alist-extract
                                         (pat-flatten1 (gpl :i mod))
                                         (4v-sexpr-eval-alist sig-al env))
                                        (4v-alist-extract
                                         (pat-flatten1 (mod-state mod))
                                         (4v-sexpr-eval-alist st-al env))))))
          :do-not-induct t)))


(defthm alist-keys-4v-sexpr-alist-extract
  (equal (alist-keys (4v-sexpr-alist-extract keys al))
         (append keys nil)))

(defthm alist-keys-eapply-sexpr
  (implies (and (good-esim-modulep mod)
                (gpl :x mod)) ;; primitivep
           (equal (alist-keys (mv-nth 1 (eapply-sexpr (gpl :x mod))))
                  (pat-flatten1 (gpl :o mod))))
  :hints (("goal" :in-theory '(eapply-sexpr
                               make-fast-alist
                               good-esim-modulep
                               good-esim-primitivep
                               alist-keys-4v-sexpr-alist-extract
                               append-right-id))))


(defthm alist-keys-4v-sexpr-compose-alist
  (equal (alist-keys (4v-sexpr-compose-alist al env))
         (alist-keys al)))




(defthm alist-keys-eapply-spec-out
  (implies (and (good-esim-modulep mod)
                (gpl :x mod)) ;; primitivep
           (equal (alist-keys (mv-nth 1 (eapply-spec al (gpl :x mod))))
                  (pat-flatten1 (gpl :o mod))))
  :hints (("goal" :in-theory '(eapply-spec
                               make-fast-alist
                               good-esim-modulep
                               good-esim-primitivep
                               alist-keys-4v-sexpr-eval-alist
                               append-right-id))))


(defthm alist-keys-esim-out
  (implies (good-esim-modulep mod)
           (equal (alist-keys (esim-out mod sig-al st-al))
                  (pat-flatten1 (gpl :o mod))))
  :hints (("goal" :in-theory (disable eapply-spec esim-fixpoint
                                      good-esim-modulep)
           :expand ((esim-out mod sig-al st-al)))))



(defthm 4v-alistp-eapply-spec
  (4v-alistp (mv-nth 1 (eapply-spec al x)))
  :hints(("Goal" :in-theory '(eapply-spec 4v-alistp-4v-sexpr-eval-alist
                                          make-fast-alist))))

(defthm 4v-alistp-esim-out
  (4v-alistp (esim-out mod sig-al st-al))
  :hints (("goal" :in-theory (disable eapply-spec esim-fixpoint)
           :expand ((esim-out mod sig-al st-al)))))

(defthm 4v-sexpr-eval-of-esim-sexpr-out-when-esim-correct-modp
  (implies (and (esim-sexpr-correct-modp mod)
                (good-esim-modulep mod))
           (b* ((sexpr-out (esim-sexpr-out mod sig-al st-al))
                (spec-out  (esim-out mod
                                     (4v-sexpr-eval-alist sig-al env)
                                     (4v-sexpr-eval-alist st-al env))))
             (equal (4v-sexpr-eval-alist sexpr-out env)
                    spec-out)))
  :hints(("Goal" :in-theory
          (disable esim-sexpr-out esim-out
                   esim-out-in-terms-of-least-fixpoint
                   4v-sexpr-eval-alist 4v-lookup)
          :use ((:instance 4v-alistp-with-same-keys-equal
                           (a (4v-sexpr-eval-alist
                               (esim-sexpr-out mod sig-al st-al) env))
                           (b (esim-out mod
                                        (4v-sexpr-eval-alist sig-al env)
                                        (4v-sexpr-eval-alist st-al env)))))
          :do-not-induct t)))

(defthm 4v-sexpr-eval-of-esim-sexpr-general-out-when-esim-sexpr-correct-modp
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-modp mod))
           (b* ((sexpr-out (4v-sexpr-alist-extract
                            (pat-flatten1 (gpl :o mod))
                            (esim-sexpr-general-out mod)))
                (spec-out (esim-out mod env env)))
             (4v-env-equiv (4v-sexpr-eval-alist sexpr-out env)
                           spec-out)))
  :hints (("goal" :use esim-sexpr-correct-modp-necc
           :in-theory (disable esim-sexpr-general-out esim-out
                                      esim-out-in-terms-of-least-fixpoint
                                      4v-sexpr-eval-alist
                                      4v-env-equiv-to-key-and-env-equiv
                                      4v-lookup))))







(defthm alist-vals-append
  (equal (alist-vals (append a b))
         (append (alist-vals a) (alist-vals b))))

(defthm alist-vals-4v-sexpr-vars-list
  (set-equiv (4v-sexpr-vars-list (append a b))
              (append (4v-sexpr-vars-list a) (4v-sexpr-vars-list b))))

(defthm 4v-sexpr-vars-of-esim-sexpr-out
  (implies (and (not (member-equal x (4v-sexpr-vars-list
                                      (alist-vals
                                       (4v-sexpr-alist-extract
                                        (pat-flatten1 (gpl :i mod))
                                        ins)))))
                (not (member-equal x (4v-sexpr-vars-list
                                      (alist-vals
                                       (4v-sexpr-alist-extract
                                        (pat-flatten1 (mod-state mod))
                                        sts))))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals
                                  (esim-sexpr-out mod ins sts))))))
  :hints(("Goal" :in-theory (e/d () (esim-sexpr-general-out eapply-sexpr)))))



(defthm 4v-lookup-4v-sexpr-eval-alist
  (equal (4v-lookup key (4v-sexpr-eval-alist al env))
         (4v-sexpr-eval (cdr (hons-assoc-equal key al)) env)))



(defun hons-assoc-equal-sexpr-pat-alist-translate-ind (op np al acc)
  (if op
      (if (atom op)
          (list np acc)
        (list (hons-assoc-equal-sexpr-pat-alist-translate-ind
               (cdr op) (cdr np) al acc)
              (hons-assoc-equal-sexpr-pat-alist-translate-ind
               (car op) (car np) al
               (sexpr-pat-alist-translate
                (cdr op) (cdr np) al nil))
              (hons-assoc-equal-sexpr-pat-alist-translate-ind
               (car op) (car np) al
               (sexpr-pat-alist-translate
                (cdr op) (cdr np) al acc))))
    acc))






(defun esim-occ-single (occ sig-al st-al)
  (b* ((o (gpl :o occ))
       (i (gpl :i occ))
       (op (gpl :op occ))
       (iop (gpl :i op))
       (oop (gpl :o op))
       (inal (4v-pat-alist-translate i iop sig-al nil))
       (stal (4v-pat-alist-translate (occ-state occ)
                                     (mod-state op)
                                     st-al nil))
       (oa (esim-out op inal stal)))
    (4v-pat-alist-translate oop o oa nil)))






(defthm esim-occ-to-esim-occ-single
  (alist-equiv
   (esim-occ occ sig-al st-al)
   (append (esim-occ-single occ sig-al st-al)
           sig-al))
  :hints(("Goal" :in-theory (e/d (alist-equiv-iff-agree-on-bad-guy)
                                 (esim-out esim-out-in-terms-of-least-fixpoint
                                  mod-internals hons-set-diff
                                  4v-pat-alist-translate
                                  good-esim-occp
                                  hons-assoc-equal-4v-pat-alist-translate
                                  pat->al)))))

(defthm 4v-sexpr-eval-alist-is-pat-alist-translate
  (implies (similar-patternsp (double-rewrite a)
                              (double-rewrite b))
           (equal (4v-sexpr-eval-alist (pat->al a b acc) env)
                  (4v-pat-alist-translate
                   b a env (4v-sexpr-eval-alist acc env))))
  :hints(("Goal" :in-theory (e/d () (4v-sexpr-eval 4v-fix)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (4v-sexpr-eval) (4v-fix))))))

(defthm esim-sexpr-occ-out-meaning
  (implies (and (good-esim-occp occ)
                (esim-sexpr-correct-modp (gpl :op occ)))
           (equal (4v-sexpr-eval-alist (esim-sexpr-occ-out occ) env)
                  (esim-occ-single occ env env)))
  :hints(("Goal" :in-theory (e/d (esim-sexpr-occ-out)
                                 (esim-out
                                  esim-out-in-terms-of-least-fixpoint
                                  esim-sexpr-out
                                  4v-sexpr-eval
                                  4v-env-equiv-to-key-and-env-equiv))
          :expand ((esim-sexpr-occ-out occ)))))


(defthmd 4v-sexpr-eval-of-lookup-when-eval-alist
  (implies (equal (4v-sexpr-eval-alist al1 env)
                  al2)
           (equal (4v-sexpr-eval (cdr (hons-assoc-equal k al1)) env)
                  (4v-lookup k al2))))

(defthm esim-sexpr-occ-out-meaning1
  (implies (and (good-esim-occp occ)
                (esim-sexpr-correct-modp (gpl :op occ)))
           (equal (4v-sexpr-eval (cdr (hons-assoc-equal k (esim-sexpr-occ-out occ)))
                                 env)
                  (4v-lookup k (esim-occ-single occ env env))))
  :hints (("goal" :use ((:instance 4v-sexpr-eval-of-lookup-when-eval-alist
                         (al1 (esim-sexpr-occ-out occ))
                         (al2 (esim-occ-single occ env env))))
           :in-theory (e/d ()
                           (esim-sexpr-out esim-sexpr-occ-out
                            good-esim-occp esim-occ-single 4v-fix
                            4v-env-equiv-to-key-and-env-equiv)))))



(defexample 4v-sexpr-equiv-eval-alist-ex
  :pattern (4v-sexpr-eval-alist x env)
  :templates (env)
  :instance-rulename 4v-sexpr-equiv-instancing)

(encapsulate
  nil
  (local
   (progn
     (defthm hons-assoc-equal-4v-and-sexpr-pat-alist-translate1
       (implies (hons-assoc-equal key (4v-pat-alist-translate a b al2 acc))
                (hons-assoc-equal key (sexpr-pat-alist-translate a b al acc)))
       :hints(("Goal" :in-theory (e/d (sexpr-pat-alist-translate)
                                      (4v-fix similar-patternsp)))))

     (defthm hons-assoc-equal-4v-and-sexpr-pat-alist-translate2
       (implies (not (hons-assoc-equal key (4v-pat-alist-translate a b al2 acc)))
                (not (hons-assoc-equal key (sexpr-pat-alist-translate a b al acc))))
       :hints(("Goal" :in-theory (e/d (sexpr-pat-alist-translate)
                                      (4v-fix similar-patternsp)))))))

  (defthm hons-assoc-equal-esim-sexpr-occ-out
    (iff (hons-assoc-equal key (esim-occ-single occ sig-al st-al))
         (hons-assoc-equal key (esim-sexpr-occ-out occ)))
    :hints(("Goal" :in-theory (e/d () (esim-sexpr-out
                                       esim-out-in-terms-of-least-fixpoint
                                       esim-out))
            :expand ((esim-sexpr-occ-out occ))))))

(include-book "centaur/4v-sexpr/sexpr-fixpoint-top" :dir :system)

(defexample 4v-sexpr-fixpointp-4v-lookup-ex
  :pattern (4v-lookup key al)
  :templates (key)
  :instance-rulename 4v-sexpr-fixpointp-instancing)

(defexample 4v-sexpr-fixpointp-hons-assoc-equal-ex
  :pattern (hons-assoc-equal key al)
  :templates (key)
  :instance-rulename 4v-sexpr-fixpointp-instancing)


(defthm esim-occ-single-when-fixpoint
  (implies (and (4v-sexpr-fixpointp (esim-sexpr-occ-out occ)
                                    fixpoint)
                (good-esim-occp occ)
                (esim-sexpr-correct-modp (gpl :op occ)))
           (4v-env-equiv (append (esim-occ-single
                                  occ
                                  (append (4v-sexpr-eval-alist fixpoint env) env)
                                  (append (4v-sexpr-eval-alist fixpoint env) env))
                                 (4v-sexpr-eval-alist fixpoint env))
                         (4v-sexpr-eval-alist fixpoint env)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable esim-sexpr-occ-out esim-occ-single
                               4v-sexpr-eval 4v-fix (4v-fix)
                               good-esim-modulep similar-patternsp))
          (witness :ruleset (4v-env-equiv-witnessing
                             4v-sexpr-fixpointp-4v-lookup-ex))
          (witness :ruleset (4v-sexpr-equiv-eval-alist-ex)))
  :otf-flg t)

(defthm 4v-sexpr-fixpointp-nil
  (4v-sexpr-fixpointp nil x)
  :hints ((witness :ruleset 4v-sexpr-fixpointp-witnessing)))


(defthm 4v-sexpr-fixpointp-append
  (implies (not (intersectp-equal (alist-keys a) (alist-keys b)))
           (iff (4v-sexpr-fixpointp (append a b) fixpoint)
                (and (4v-sexpr-fixpointp a fixpoint)
                     (4v-sexpr-fixpointp b fixpoint))))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset (4v-sexpr-fixpointp-witnessing
                             4v-sexpr-fixpointp-hons-assoc-equal-ex))
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal))))
          (set-reasoning)))






(defthm hons-assoc-equal-esim-sexpr-occ-out-when-output
  (implies (good-esim-occp occ)
           (iff (hons-assoc-equal key (esim-sexpr-occ-out occ))
                (member-equal key (pat-flatten1 (gpl :o occ)))))
  :hints(("Goal" :in-theory (e/d () (esim-sexpr-out))
          :expand ((esim-sexpr-occ-out occ))))
  :otf-flg t)

(defthm member-implies-lookup-in-occmap
  (implies (member-equal occ occs)
           (hons-assoc-equal (gpl :u occ) (occmap1 occs))))

(local (in-theory (enable consp-of-hons-assoc-equal)))

(encapsulate nil
  (local
   (defthm fal-extract-cdr
     (implies (or (not (member-equal (caar al) keys))
                  (not (consp (car al))))
              (equal (fal-extract keys (cdr al))
                     (fal-extract keys al)))
     :hints(("Goal" :in-theory (enable fal-extract)))))

  (defthmd vals-of-extract-of-keys-when-no-duplicates
    (implies (no-duplicatesp-equal (alist-keys al))
             (equal (alist-vals (fal-extract (alist-keys al) al))
                    (alist-vals al)))
    :hints(("Goal" :in-theory (enable alist-keys fal-extract)))))
(local
 (progn
   (defthm no-intersect-collect
     (implies (and (not (intersectp-equal (collect-signal-list :o occs)
                                          sigs))
                   (member-equal occ occs))
              (and (not (intersectp-equal (pat-flatten1 (gpl :o occ))
                                          sigs))
                   (not (intersectp-equal sigs (pat-flatten1 (gpl :o occ)))))))

   (defthm different-occs-no-overlap
     (implies (and (no-duplicatesp-equal
                    (collect-signal-list :o occs))
                   (member-equal occ1 occs)
                   (member-equal occ2 occs)
                   (not (equal occ1 occ2)))
              (not (intersectp-equal (pat-flatten1 (gpl :o occ1))
                                     (pat-flatten1 (gpl :o occ2)))))
     :hints (("goal" :induct (len occs))))

   (defthm different-occs-no-overlap-rw
     (implies (and (good-esim-modulep mod)
                   (member-equal occ1 (mod-occs mod))
                   (member-equal occ2 (mod-occs mod))
                   (not (equal occ1 occ2)))
              (not (intersectp-equal (pat-flatten1 (gpl :o occ1))
                                     (pat-flatten1 (gpl :o occ2)))))
     :hints(("Goal" :in-theory (e/d (occmap-when-no-occs)
                                    (member-equal-of-alist-vals-under-iff))
             :expand ((good-esim-modulep mod)))))))

(defthm esim-sexpr-occ-out-of-nil
  (equal (esim-sexpr-occ-out nil) nil)
  :hints (("goal" :expand ((esim-sexpr-occ-out nil)
                           (:free (x) (sexpr-pat-alist-translate nil nil x nil)))
           :in-theory (disable (esim-sexpr-occ-out)))))

(defthm lookups-in-esim-sexpr-occs-out
  (implies (and (hons-assoc-equal key (esim-sexpr-occs-out mod occs))
                (hons-assoc-equal key (esim-sexpr-occ-out (esim-get-occ occ mod)))
                (good-esim-modulep mod))
           (equal (hons-assoc-equal key (esim-sexpr-occs-out mod occs))
                  (hons-assoc-equal key (esim-sexpr-occ-out
                                         (esim-get-occ occ mod)))))
  :hints (("goal" :induct (len occs)
           :in-theory (disable* esim-sexpr-occ-out
                               different-occs-no-overlap-rw
                               good-esim-modulep
                               similar-patternsp
                               good-esim-occp
                               default-car default-cdr
                               member-equal
                               ;var-assoc-key
                               lookup-in-esim-sexpr-occs-out
                               (:rules-of-class :type-prescription :here))
           :expand ((esim-sexpr-occs-out mod occs)))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal occ (occmap mod)))))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))
          (and stable-under-simplificationp
               '(:use ((:instance different-occs-no-overlap-rw
                                  (occ1 (esim-get-occ occ mod))
                                  (occ2 (esim-get-occ (car occs) mod))))))
          (set-reasoning)))

(defthm alist-keys-esim-sexpr-occ-out
  (implies (good-esim-occp occ)
           (equal (alist-keys (esim-sexpr-occ-out occ))
                  (pat-flatten1 (gpl :o occ))))
  :hints(("Goal" :in-theory (disable esim-sexpr-out)
          :expand ((esim-sexpr-occ-out occ)))))


(defthm fal-extract-nil
  (equal (fal-extract keys nil) nil)
  :hints(("Goal" :in-theory (enable fal-extract))))

(defthm alist-keys-esim-sexpr-occs-out
  (implies (good-esim-modulep mod)
           (equal (alist-keys (esim-sexpr-occs-out mod occs))
                  (collect-signal-list
                   :o (occs-for-names occs mod))))
  :hints (("goal" :in-theory (e/d (occmap-when-no-occs fal-extract)
                                  (esim-sexpr-occ-out))
           :induct (len occs)
           :expand ((esim-sexpr-occs-out mod occs)))))

(defthm signal-list-not-intersecting-pat
  (implies (and (not (member-equal occ occs))
                (good-esim-modulep mod))
           (not (intersectp-equal
                 (collect-signal-list
                  :o (occs-for-names occs mod))
                 (pat-flatten1 (gpl :o (esim-get-occ occ mod))))))
  :hints (("goal" :induct (len occs)
           :in-theory (enable fal-extract))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal occ (occmap mod)))))))


(defthm fixpointp-for-occs-impl-fixpointp-for-single-occ
  (implies (and (4v-sexpr-fixpointp (esim-sexpr-occs-out mod occs)
                                    fixpoint)
                (member-equal occ occs)
                (no-duplicatesp-equal occs)
                (good-esim-modulep mod))
           (4v-sexpr-fixpointp (esim-sexpr-occ-out (esim-get-occ occ mod))
                               fixpoint))
  :hints (("goal" :induct (len occs)
           :expand ((esim-sexpr-occs-out mod occs)
                    (member-equal occ occs))
           :in-theory (e/d* (occmap-when-no-occs
                             fal-extract)
                            (esim-sexpr-occ-out
                             esim-sexpr-occ-out-meaning
                             good-esim-modulep
                             default-car default-cdr
                             append
                             (:rules-of-class :type-prescription :here)
                             true-listp-member-equal
                             member-equal)))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))))



(encapsulate nil
  (local (in-theory (disable* esim-sexpr-occ-out esim-occ-single
                              4v-sexpr-eval 4v-fix (4v-fix$inline)
                              good-esim-modulep similar-patternsp
                              default-car default-cdr
                              ; 4v-sexpr-fixpointp-is-alt1
                              esim-occ-single-when-fixpoint
                              good-esim-occp
                              (:rules-of-class
                               :type-prescription :here))))
  (defthm esim-occ-single-when-fixpoint1
    (implies (and (4v-sexpr-fixpointp (esim-sexpr-occ-out occ)
                                      fixpoint)
                  (good-esim-occp occ)
                  (subsetp-equal (pat-flatten1 (gpl :o occ))
                                 (alist-keys fixpoint))
                  (esim-sexpr-correct-modp (gpl :op occ)))
             (4v-env-equiv (append (esim-occ-single
                                    occ
                                    (append (4v-sexpr-eval-alist fixpoint env) env)
                                    (append (4v-sexpr-eval-alist fixpoint env) env))
                                   (4v-sexpr-eval-alist fixpoint env)
                                   env)
                           (append (4v-sexpr-eval-alist fixpoint env)
                                   env)))
    :hints (("goal" :do-not-induct t
             :use esim-occ-single-when-fixpoint
             :in-theory (enable hons-assoc-equal-when-not-member-alist-keys))
            (witness :ruleset (4v-env-equiv-witnessing
                               4v-env-equiv-4v-lookup-ex))
            (and stable-under-simplificationp
                 '(:in-theory (e/d* (hons-assoc-equal-iff-member-alist-keys)
                                    (alist-keys-member-hons-assoc-equal))))
            (witness :ruleset set-reasoning-no-consp))
    :otf-flg t))


(defun esim-sexpr-correct-occsp (occs)
  (or (atom occs)
      (and (esim-sexpr-correct-modp (gpl :op (car occs)))
           (esim-sexpr-correct-occsp (cdr occs)))))



(defthm esim-occ-single-nil
  (equal (esim-occ-single nil a b)
         nil)
  :hints(("Goal" :in-theory (disable esim-sexpr))))


(defthm esim-sexpr-correct-modp-occmap1
  (implies (and (esim-sexpr-correct-occsp occs)
                (hons-assoc-equal occ (occmap1 occs)))
           (esim-sexpr-correct-modp
            (gpl :op (cdr (hons-assoc-equal occ (occmap1 occs)))))))

(defthm esim-sexpr-correct-modp-occmap
  (implies (and (esim-sexpr-correct-occsp (gpl :occs mod))
                (hons-assoc-equal occ (occmap mod)))
           (esim-sexpr-correct-modp
            (gpl :op (esim-get-occ occ mod))))
  :hints(("Goal" :in-theory (enable occmap))))

(defthm esim-fixpoint-p-occs-esim-occs
  (implies (and (4v-sexpr-fixpointp
                 (esim-sexpr-occs-out mod occs)
                 fixpoint)
                (good-esim-modulep mod)
                (no-duplicatesp-equal occs)
                (subsetp-equal (collect-signal-list
                                :o (occs-for-names occs mod))
                               (alist-keys fixpoint))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (4v-env-equiv
            (esim-occs mod occs
                       (append (4v-sexpr-eval-alist fixpoint env) env)
                       (append (4v-sexpr-eval-alist fixpoint env) env))
            (append (4v-sexpr-eval-alist fixpoint env) env)))
  :hints (("goal" :induct (len occs)
           :in-theory (e/d (fal-extract)
                           (esim-occ esim-sexpr-occ-out
                                     esim-occ-single
                                     4v-sexpr-eval
                                     esim-occs-equiv-when-fixpoint
                                     good-esim-modulep
                                     good-esim-occp
                                     esim-wf-signals
                                     occs-<=-impl-occs-fixed
                                     input-subset-bound-impl-esim-wf-signals
                                     4v-env-equiv-to-key-and-env-equiv
                                     hons-assoc-equal
                                     default-cdr default-car))
           :expand ((:free (a b)
                           (esim-occs mod occs a b))
                    (esim-sexpr-occs-out mod occs)))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))))



(defthm keys-equiv-sexpr-fixpoint-with-varmap
  (keys-equiv (sexpr-fixpoint-with-varmap ups map)
              ups)
  :hints (("goal" :in-theory (disable good-sexpr-varmap))
          (witness :ruleset keys-equiv-witnessing)))

(defthm 4v-sexpr-fixpoint-lower-boundp-sexpr-fixpoint-with-varmap-rw
  (implies (4v-sexpr-alist-equiv ups ups1)
           (and (4v-sexpr-fixpoint-lower-boundp
                 ups1 (sexpr-fixpoint-with-varmap ups map))
                (4v-sexpr-fixpointp
                 ups1 (sexpr-fixpoint-with-varmap ups map)))))



(defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv
  (sexpr-fixpoint-with-varmap ups map) 1
  :hints (("goal" :use ((:instance 4v-sexpr-least-fixpoint-unique
                                   (update-fns ups)
                                   (lb1 (sexpr-fixpoint-with-varmap
                                         ups map))
                                   (lb2 (sexpr-fixpoint-with-varmap
                                         ups-equiv map)))
                        (:instance sexpr-fixpoint-with-varmap-least-fixpointp
                                   (ups ups-equiv)))))
  :rule-classes nil)



(defthm 4v-sexpr-vars-esim-sexpr-occ-out
  (implies (and (not (member-equal v (pat-flatten1 (gpl :i occ))))
                (not (member-equal v (pat-flatten1 (occ-state occ))))
                (good-esim-occp occ))
           (not (member-equal
                 v
                 (4v-sexpr-vars-list
                  (alist-vals (esim-sexpr-occ-out occ))))))
  :hints(("Goal" :in-theory (disable esim-sexpr-out))))

(defthm 4v-sexpr-vars-esim-sexpr-occs-out
  (implies (and (not (member-equal v (collect-signal-list
                                      :i (occs-for-names occs mod))))
                (not (member-equal v (pat-flatten1 (mod-state mod))))
                (good-esim-modulep mod)
                (not (gpl :x mod)))
           (not (member-equal
                 v
                 (4v-sexpr-vars-list
                  (alist-vals (esim-sexpr-occs-out mod occs))))))
  :hints(("Goal" :in-theory (e/d (fal-extract) (esim-sexpr-occ-out)))))






(defthm 4v-sexpr-fixpointp-esim-sexpr-fixpoint
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (4v-sexpr-fixpointp
            (esim-sexpr-occs-out
             mod (alist-keys (occmap mod)))
            (esim-sexpr-fixpoint-out mod)))
  :hints (("goal" :expand ((esim-sexpr-fixpoint-out mod))
           :in-theory (disable good-sexpr-varmap))))

(defthm 4v-sexpr-fixpoint-lower-boundp-esim-sexpr-fixpoint
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (4v-sexpr-fixpoint-lower-boundp
            (esim-sexpr-occs-out
             mod (alist-keys (occmap mod)))
            (esim-sexpr-fixpoint-out mod)))
  :hints (("goal" :expand ((esim-sexpr-fixpoint-out mod))
           :in-theory (disable good-sexpr-varmap))))



(defthm subset-pat-when-subset-collect
  (implies (and (subsetp-equal (collect-signal-list
                                :o (occs-for-names occs mod))
                               lst)
                (member-equal occ occs))
           (subsetp-equal (pat-flatten1 (gpl :o (esim-get-occ occ mod)))
                          lst))
  :hints(("Goal" :in-theory (enable fal-extract))))

(defun cdr-occs-ind (mod occs)
  (if (or (atom occs) (atom (gpl :occs mod)))
      nil
    (cdr-occs-ind mod (cdr occs))))

(defthmd esim-sexpr-occs-out-when-no-occs
  (implies (atom (gpl :occs mod))
           (equal (esim-sexpr-occs-out mod occs)
                  'out-fns))
  :hints (("goal" :expand ((esim-sexpr-occs-out mod occs)))))

(defthm 4v-sexpr-fixpointp-implies-esim-fixpoint-p-occs
  (implies (and (4v-sexpr-fixpointp
                 (esim-sexpr-occs-out mod occs)
                 fixpoint)
                (subsetp-equal
                 (collect-signal-list
                  :o (occs-for-names occs mod))
                 (alist-keys fixpoint))
                (no-duplicatesp-equal occs)
                (good-esim-modulep mod)
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (esim-fixpoint-p-occs
            mod occs
            (append (4v-sexpr-eval-alist fixpoint env) env)
            (append (4v-sexpr-eval-alist fixpoint env) env)))
  :hints(("Goal" :in-theory (e/d (occmap-when-no-occs
                                  esim-sexpr-occs-out-when-no-occs
                                  fal-extract)
                                 (esim-sexpr-occ-out
                                  good-esim-modulep
                                  4v-sexpr-eval
                                  good-esim-occp
                                  esim-wf-signals
                                  esim-occ esim-occ-single))
          :induct (len occs)
          :expand ((esim-sexpr-occs-out mod occs))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal (car occs) (occmap mod))))))
  :otf-flg t)


(defthm 4v-sexpr-fixpointp-implies-esim-fixpoint-p
  (implies (and (4v-sexpr-fixpointp
                 (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                 fixpoint)
                (subsetp-equal
                 (collect-signal-list :o (mod-occs mod))
                 (alist-keys fixpoint))
                (good-esim-modulep mod)
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (esim-fixpoint-p
            mod (append (4v-sexpr-eval-alist fixpoint env) env)
            (append (4v-sexpr-eval-alist fixpoint env) env)))
  :hints(("Goal" :in-theory (e/d (good-esim-modulep
                                  occmap-when-no-occs)
                                 (esim-fixpoint-p-occs
                                  esim-sexpr-occs-out))
          :do-not-induct t)))

(defthm 4v-pat-alist-translate-append-alists-when-not-intersect
  (implies (and (similar-patternsp (double-rewrite a) (double-rewrite b))
                (not (intersectp-equal (pat-flatten1 a)
                                       (alist-keys al1))))
           (equal (4v-pat-alist-translate
                   a b (append al1 al2) acc)
                  (4v-pat-alist-translate
                   a b al2 acc))))

(defthm esim-occ-single-append-fixpoint-sigs
  (implies (and (not (intersectp-equal
                      (pat-flatten1 (occ-state occ))
                      (alist-keys fixpoint)))
                (good-esim-occp occ))
           (equal (esim-occ-single occ
                                   sigs (append fixpoint st))
                  (esim-occ-single occ sigs st)))
  :hints (("goal" :in-theory (disable esim-out
                                      esim-out-in-terms-of-least-fixpoint)
           :do-not-induct t)))


(defthm not-intersecting-mod-state-impl-occ-state
  (implies (and (not (gpl :x mod))
                (not (intersectp-equal x (pat-flatten1 (mod-state mod)))))
           (not (intersectp-equal x (pat-flatten1 (occ-state (esim-get-occ occ mod))))))
  :hints ((set-reasoning)))


(defthm eval-of-esim-sexpr-occs-when-esim-fixpoint-p
  (implies (and (esim-fixpoint-p-occs mod occs (append fixpoint st) st)
                (good-esim-modulep mod)
                (not (gpl :x mod))
                (not (intersectp-equal
                      (pat-flatten1 (mod-state mod))
                      (alist-keys fixpoint)))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (4v-env-equiv
            (append (4v-sexpr-eval-alist
                     (esim-sexpr-occs-out mod occs)
                     (append fixpoint st))
                    fixpoint st)
            (append fixpoint st)))
  :hints(("Goal" :in-theory (disable esim-sexpr-occ-out
                                     good-esim-modulep
                                     esim-occ esim-occ-single
                                     4v-sexpr-eval
                                     esim-wf-signals
                                     4v-env-equiv-to-key-and-env-equiv
                                     esim-fixpoint-p-occs-when-<=
                                     default-car default-cdr)
          :induct (len occs)
          :expand ((esim-sexpr-occs-out mod occs))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal (car occs) (occmap mod))))))
  :otf-flg t)




(defthm not-subset-of-keys-when-member-and-not-assoc
  (implies (and (member-equal x a)
                (not (hons-assoc-equal x b)))
           (not (subsetp-equal a (alist-keys b))))
  :hints(("Goal" :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal)))
         (set-reasoning)))

;; here fixpoint is an _evaluated_ fixpoint for occs under env, where think of
;; env as covering input and previous-state variables while fixpoint covers
;; internal/output signals.
(defthm eval-of-esim-sexpr-occs-when-esim-fixpoint-p-1
  (implies (and (esim-fixpoint-p-occs mod occs (append fixpoint env) env)
                (good-esim-modulep mod)
                (not (gpl :x mod))
                (subsetp-equal
                 (collect-signal-list
                  :o (occs-for-names occs mod))
                 (alist-keys fixpoint))
                (not (intersectp-equal
                      (pat-flatten1 (mod-state mod))
                      (alist-keys fixpoint)))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (4v-env-equiv
            (append (4v-sexpr-eval-alist
                     (esim-sexpr-occs-out mod occs)
                     (append fixpoint env))
                    fixpoint)
            fixpoint))
  :hints(("Goal" :in-theory (e/d* (fal-extract)
                                 (esim-sexpr-occ-out
                                  good-esim-modulep
                                  esim-occ esim-occ-single
                                  good-esim-occp
                                  esim-wf-signals
                                  default-car default-cdr
                                  (:rules-of-class :type-prescription :here)
; 4v-env-equiv-when-4v-alist-<=-both-ways
                                  esim-fixpoint-p-occs-when-<=
                                  keys-equiv-when-alist-keys
                                  (:type-prescription 4v-fix$inline)
                                  4v-sexpr-eval
                                  ;alist-equiv-append-atom
                                  esim-fixpoint-p-occs
                                  4v-fix))
          :expand ((esim-fixpoint-p-occs mod occs (append fixpoint env) env)
                   (esim-sexpr-occs-out mod occs))
          :induct (len occs)
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))
         (witness :ruleset (4v-env-equiv-witnessing
                            4v-env-equiv-4v-lookup-ex)))
  :otf-flg t)

(defthm 4v-pat-alist-translate-append-alists-when-not-intersect-2
  (implies (and (similar-patternsp (double-rewrite a)
                                   (double-rewrite b))
                (not (intersectp-equal (pat-flatten1 a)
                                       (alist-keys al2))))
           (equal (4v-pat-alist-translate a b (append al1 al2) acc)
                  (4v-pat-alist-translate a b al1 acc))))

(defthm esim-occ-single-append-sigs-second-non-intersecting
  (implies (and (not (intersectp-equal (alist-keys st)
                                       (pat-flatten1 (gpl :i occ))))
                (good-esim-occp occ))
           (equal (esim-occ-single occ (append sigs st) st)
                  (esim-occ-single occ sigs st)))
  :hints(("Goal" :in-theory (e/d () (esim-out esim-out-in-terms-of-least-fixpoint))
          :do-not-induct t)))

;; variation in which here fixpoint covers both internal and input signals, st
;; covers states
(defthm eval-of-esim-sexpr-occs-when-esim-fixpoint-p-2
  (implies (and (esim-fixpoint-p-occs mod occs fixpoint st)
                (good-esim-modulep mod)
                (not (gpl :x mod))
                (subsetp-equal
                 (collect-signal-list
                  :o (occs-for-names occs mod))
                 (alist-keys fixpoint))
                (not (intersectp-equal
                      (collect-signal-list
                       :i (occs-for-names occs mod))
                      (alist-keys st)))
                (not (intersectp-equal
                      (pat-flatten1 (mod-state mod))
                      (alist-keys fixpoint)))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (4v-env-equiv
            (append (4v-sexpr-eval-alist
                     (esim-sexpr-occs-out mod occs)
                     (append fixpoint st))
                    fixpoint)
            fixpoint))
  :hints(("Goal" :in-theory (e/d (fal-extract)
                                 (esim-sexpr-occ-out
                                  good-esim-modulep
                                  esim-occ esim-occ-single
                                  good-esim-occp
                                  esim-wf-signals
                                  default-car default-cdr
; 4v-env-equiv-when-4v-alist-<=-both-ways
                                  esim-fixpoint-p-occs-when-<=
                                  keys-equiv-when-alist-keys
                                  (:type-prescription 4v-fix$inline)
                                  4v-sexpr-eval
                                  esim-fixpoint-p-occs
                                  4v-fix))
          :expand ((esim-fixpoint-p-occs mod occs fixpoint st)
                   (esim-sexpr-occs-out mod occs))
          :induct (len occs)
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal (car occs) (occmap mod))))))
  :otf-flg t)

(defthm alist-keys-esim-occ-single
  (implies (good-esim-occp occ)
           (equal (alist-keys (esim-occ-single occ sigs sts))
                  (pat-flatten1 (gpl :o occ))))
  :hints(("Goal" :in-theory (e/d (esim-occ-single)
                                 (hons-assoc-equal-esim-sexpr-occ-out
                                  esim-out esim-out-in-terms-of-least-fixpoint)))))

(defthm subsetp-flatten-of-collected1
  (implies (member-equal occ occs)
           (subsetp-equal (pat-flatten1 (gpl k (esim-get-occ occ mod)))
                          (collect-signal-list k (occs-for-names occs mod))))
  :hints (("goal" :induct t :in-theory (enable member-equal fal-extract))
          (and stable-under-simplificationp
               '(:in-theory (enable gpl fal-extract)))))

(defthm subsetp-flatten-of-collected
  (subsetp-equal (pat-flatten1 (gpl k (esim-get-occ occ mod)))
                 (collect-signal-list k (mod-occs mod)))
  :hints (("goal" :use ((:instance subsetp-flatten-of-collected1
                                   (occs (alist-keys (occmap mod)))))
           :in-theory (e/d (gpl)
                           (subsetp-flatten-of-collected1)))))


(defthm occ-state-subset-of-occs-state
  (implies (member-equal occ occs)
           (subsetp-equal (pat-flatten1 (occ-state occ))
                          (pat-flatten1 (occs-state occs))))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthm occ-state-subset-of-mod-state
  (implies (and (member-equal occ (gpl :occs mod))
                (not (gpl :x mod)))
           (subsetp-equal (pat-flatten1 (occ-state occ))
                          (pat-flatten1 (mod-state mod))))
  :hints(("Goal" :in-theory (enable mod-state))))

(defthm member-equal-lookup-in-occmap
  (implies (hons-assoc-equal occ (occmap1 occs))
           (member-equal (cdr (hons-assoc-equal occ (occmap1 occs)))
                         occs)))

(defthm hons-assoc-equal-occmap-means-member-occs
  (implies (hons-assoc-equal occ (occmap mod))
           (member-equal (cdr (hons-assoc-equal occ (occmap mod)))
                         (gpl :occs mod)))
  :hints(("Goal" :in-theory (enable occmap))))

(defthm occ-state-subset-of-mod-state1
  (implies (not (gpl :x mod))
           (subsetp-equal (pat-flatten1 (occ-state (esim-get-occ occ mod)))
                          (pat-flatten1 (mod-state mod))))
  :hints(("Goal" :in-theory (enable mod-state)
          :cases ((hons-assoc-equal occ (occmap mod))))))

(defthm 4v-pat-alist-translate-extract-when-keys-subset
  (implies (and (subsetp-equal (pat-flatten1 ins1) keys)
                (similar-patternsp (double-rewrite ins1)
                                   (double-rewrite ins)))
           (equal (4v-pat-alist-translate
                   ins1 ins (4v-alist-extract keys al) nil)
                  (4v-pat-alist-translate ins1 ins al nil)))
  :hints(("Goal" :in-theory (e/d (subsetp-equal) (4v-fix)))))

(defthm similar-patterns-occ-state
  (equal (similar-patternsp (occ-state occ) (mod-state (gpl :op occ)))
         t))

(encapsulate
  nil
  (local (in-theory (Disable* esim-occ-single esim-wf-signals
                              esim-occ good-esim-occp
                              good-esim-modulep
                              4v-fix
                              default-car default-cdr
                              esim-fixpoint-p-occs-when-<=
; 4v-env-equiv-when-4v-alist-<=-both-ways
                              4v-env-equiv-to-key-and-env-equiv
                              4v-alists-agree
                              fal-extract
                              collect-signal-list
                              good-esim-modulep-ins-not-intersecting-states
                              4v-alist-extract
; good-esim-modulep-st-subset-not-intersecting-inputs
                              hons-assoc-equal-esim-sexpr-occ-out
                              good-esim-modulep-outs-subset-of-driven
                              4v-alist-extract-when-subset
                              (:rules-of-class :type-prescription :here))))

  (defthm 4v-pat-alist-translate-generalization
    (implies (and (4v-alists-agree
                   inputs-only fixpoint0 env)
                  (subsetp-equal
                   (pat-flatten1 ins1) collected-inputs)
                  (subsetp-equal collected-inputs
                                 (append outs inputs-only)))
             (equal (4v-pat-alist-translate
                     ins1 ins (append (4v-alist-extract
                                       outs fixpoint0)
                                      (4v-alist-extract
                                       collected-inputs env))
                     nil)
                    (4v-pat-alist-translate
                     ins1 ins fixpoint0 nil)))
    :hints (("goal"
             :induct t
             :do-not-induct t)
            (witness :ruleset 4v-alists-agree-hons-assoc-equal-ex)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys
                                    pat-flatten1)
                                   (alist-keys-member-hons-assoc-equal))))
            (witness :ruleset set-reasoning-no-consp)))

  (defthm 4v-pat-alist-translate-lemma
    (implies (and (good-esim-modulep mod)
                  (not (gpl :x mod))
                  (4v-alists-agree
                   (pat-flatten1 (gpl :i mod))
                   fixpoint0 env))
             (equal
              (4v-pat-alist-translate
               (gpl :i (esim-get-occ occ mod))
               ins
               (append (4v-alist-extract
                        (collect-signal-list :o (mod-occs mod))
                        fixpoint0)
                       (4v-alist-extract
                        (collect-signal-list :i (mod-occs mod))
                        env))
               nil)
              (4v-pat-alist-translate
               (gpl :i (esim-get-occ occ mod))
               ins
               fixpoint0
               nil)))
    :hints(("Goal" :expand ((good-esim-modulep mod))
            :in-theory (e/d (occmap-when-no-occs)
                            (4v-pat-alist-translate-generalization))
            :use ((:instance 4v-pat-alist-translate-generalization
                             (inputs-only (pat-flatten1 (gpl :i mod)))
                             (ins1 (gpl :i (esim-get-occ occ mod)))
                             (collected-inputs
                              (collect-signal-list :i (mod-occs mod)))
                             (outs
                              (collect-signal-list :o (mod-occs mod))))))
           (and stable-under-simplificationp
                '(:cases ((hons-assoc-equal occ (occmap mod)))))))

  (defthm esim-occ-single-lemma
    (implies (and (good-esim-modulep mod)
                  (not (gpl :x mod))
                  (4v-alists-agree
                   (pat-flatten1 (gpl :i mod))
                   env fixpoint0))
             (equal (esim-occ-single
                     (esim-get-occ occ mod)
                     (append (4v-alist-extract
                              (collect-signal-list
                               :o (mod-occs mod))
                              fixpoint0)
                             (4v-alist-extract
                              (collect-signal-list
                               :i (mod-occs mod))
                              env))
                     (4v-alist-extract
                      (pat-flatten1 (mod-state mod))
                      env))
                    (esim-occ-single
                     (esim-get-occ occ mod)
                     fixpoint0 env)))
    :hints (("goal" :in-theory (e/d (esim-occ-single
                                     4v-alists-agree-commute)
                                    (esim-out esim-out-in-terms-of-least-fixpoint
                                              occ-state))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((hons-assoc-equal occ (occmap mod)))))
            ;; (witness :ruleset (4v-env-equiv-witnessing
            ;;                    4v-env-equiv-lookup-ex))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
            ;;                        (alist-keys-member-hons-assoc-equal))))
            ;; (witness :ruleset set-reasoning-no-consp)
            ))

  (local (in-theory (disable hons-assoc-equal)))
  (defthm esim-fixpoint-p-occs-lemma
    (implies (and (good-esim-modulep mod)
                  (not (gpl :x mod))
                  (4v-alists-agree
                   (pat-flatten1 (gpl :i mod))
                   env fixpoint0))
             (iff (esim-fixpoint-p-occs mod occs
                                        (append (4v-alist-extract
                                                 (collect-signal-list
                                                  :o (mod-occs mod))
                                                 fixpoint0)
                                                (4v-alist-extract
                                                 (collect-signal-list
                                                  :i (mod-occs mod))
                                                 env))
                                        (4v-alist-extract
                                         (pat-flatten1 (mod-state mod))
                                         env))
                  (esim-fixpoint-p-occs mod occs fixpoint0 env)))
    :hints (("goal" :induct (len occs)
             :expand ((:free (sigs sts)
                             (esim-fixpoint-p-occs mod occs sigs sts)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))
            (witness :ruleset (4v-env-equiv-witnessing
                               4v-env-equiv-4v-lookup-ex))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                   (alist-keys-member-hons-assoc-equal))))
            (witness :ruleset set-reasoning-no-consp))))

(local
 (defthm 4v-alists-agree-lemma1
   (implies (and (not (intersectp-equal inkeys outkeys))
                 (set-equiv outkeys (alist-keys fixpoint))
                 (subsetp-equal inkeys inkeys1))
            (iff (4v-alists-agree
                  inkeys
                  (append fixpoint
                          (4v-alist-extract inkeys1 env))
                  fp0)
                 (4v-alists-agree inkeys env fp0)))
   :hints(("Goal" :in-theory (e/d* (4v-alists-agree
;; hons-assoc-equal-iff-member-alist-keys
                                    )
                                   (4v-fix ; 4v-lookup
                                    4v-alists-agree
; alist-keys-member-hons-assoc-equal
; subsetp-car-member
                                    default-car default-cdr
                                    consp-of-hons-assoc-equal
                                    subsetp-trans
                                    subsetp-when-atom-left
                                    hons-assoc-equal
; 4v-fix-when-4vp
                                    (:rules-of-class :type-prescription :here)))
           :expand ((:free (env) (4v-alists-agree inkeys env fp0)))
           :induct (len inkeys))
;; (witness :ruleset set-reasoning-no-consp)
          )))

(defthm alist-equiv-append-when-keys-nil
  (implies (set-equiv nil (alist-keys a))
           (alist-equiv (append a b) b))
  :hints (("goal" :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                  (alist-keys-member-hons-assoc-equal)))
          (witness :ruleset alist-equiv-witnessing)
          (set-reasoning)))

(defcong 4v-env-equiv iff (4v-alists-agree keys a b) 2
  :hints(("Goal" :in-theory (e/d () (4v-lookup)))))

(defthm 4v-alists-agree-extract-supserset
  (implies (subsetp-equal keys keys1)
           (iff (4v-alists-agree keys (4v-alist-extract keys1 env) b)
                (4v-alists-agree keys env b)))
  :hints(("Goal" :in-theory (disable 4v-fix))))

(defthm 4v-alists-agree-rewrite
  (implies (and (good-esim-modulep mod)
                (set-equiv
                 (collect-signal-list :o (mod-occs mod))
                 (alist-keys fixpoint)))
           (iff (4v-alists-agree
                 (pat-flatten1 (gpl :i mod))
                 (append fixpoint
                         (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                           env))
                 fp0)
                (4v-alists-agree
                 (pat-flatten1 (gpl :i mod))
                 env fp0)))
  :hints(("Goal" :expand (good-esim-modulep mod)
          :in-theory (e/d (occmap-when-no-occs) (4v-fix))
          :do-not-induct t)))


(defthm good-esim-modp-state-not-intersecting-ins
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (not (intersectp-equal (pat-flatten1 (mod-state mod))
                                  (collect-signal-list
                                   :i (mod-occs mod)))))
  :hints (("goal" :expand (good-esim-modulep mod)
           :in-theory (e/d* (occmap-when-no-occs)
                            ((:ruleset good-esim-mod-impl)
                             good-esim-modulep
                             collect-signal-list
                             no-duplicatesp-equal-non-cons)))
          (set-reasoning)))

(defthm good-esim-modp-state-not-intersecting-outs
  (implies (good-esim-modulep mod)
           (not (intersectp-equal (pat-flatten1 (mod-state mod))
                                  (collect-signal-list
                                   :o (mod-occs mod)))))
  :hints (("goal" :expand (good-esim-modulep mod)
           :in-theory (e/d* (occmap-when-no-occs)
                            ((:ruleset good-esim-mod-impl)
                             good-esim-modulep
                             collect-signal-list
                             no-duplicatesp-equal-non-cons)))))

(add-to-ruleset good-esim-mod-impl
                '(good-esim-modp-state-not-intersecting-ins
                  good-esim-modp-state-not-intersecting-outs))

;; (defthm hons-assoc-equal-esim-sexpr-occ-out
;;   (implies (good-esim-occp occ)
;;            (iff (hons-assoc-equal k (esim-sexpr-occ-out occ))
;;                 (member-equal k (pat-flatten (gpl :o occ) nil))))
;;   :hints(("Goal" :in-theory (disable esim-sexpr good-esim-occp))))

(defthm hons-assoc-equal-esim-sexpr-occs-out
  (implies (good-esim-modulep mod)
           (iff (hons-assoc-equal k (esim-sexpr-occs-out mod occs))
                (member-equal k (collect-signal-list
                                 :o (occs-for-names occs mod)))))
  :hints(("Goal" :in-theory (e/d (occmap-when-no-occs
                                  fal-extract)
                                 (esim-sexpr-occ-out
                                  good-esim-modulep))
          :induct (len occs)
          :expand ((esim-sexpr-occs-out mod occs)))
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-eval-append-when-second-covers
    (implies (subsetp-equal (4v-sexpr-vars x) keys)
             (equal (4v-sexpr-eval
                     x (append al1
                               (4v-alist-extract keys al2)
                               al3))
                    (4v-sexpr-eval x (append al1 al2))))
    :flag sexpr
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (env) (4v-sexpr-eval x env)))))))
  (defthm 4v-sexpr-eval-list-append-when-second-covers
    (implies (subsetp-equal (4v-sexpr-vars-list x) keys)
             (equal (4v-sexpr-eval-list
                     x (append al1
                               (4v-alist-extract keys al2)
                               al3))
                    (4v-sexpr-eval-list x (append al1 al2))))
    :flag sexpr-list)
  :hints (("goal" :in-theory (e/d* (subsetp-equal)
                                   (sexpr-eval-list-norm-env-when-ground-args-p
                                    nth-with-large-index
                                    member-of-cons
                                    4v-sexpr-eval
                                    4v-sexpr-eval-when-agree-on-keys
                                    4v-alists-agree
                                    append alist-equiv-append-when-keys-nil
                                    set-equiv-asym
                                    subsetp-cons-2
                                    subsetp-car-member
                                    default-car default-cdr
                                    member-equal
                                    4v-fix (:ruleset 4v-op-defs))))))

(defthm 4v-sexpr-eval-alist-append-when-second-covers
  (implies (subsetp-equal (4v-sexpr-vars-list (alist-vals x)) keys)
           (equal (4v-sexpr-eval-alist
                   x (append al1
                             (4v-alist-extract keys al2)
                             al3))
                  (4v-sexpr-eval-alist x (append al1 al2))))
  :hints(("Goal" :in-theory (e/d () (4v-sexpr-eval))
          :induct (len x))))

(defthm esim-sexpr-occs-out-vars-subset-of-collect-ins
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (subsetp-equal
            (4v-sexpr-vars-list
             (alist-vals (esim-sexpr-occs-out mod occs)))
            (append
             (collect-signal-list :i (occs-for-names occs mod))
             (pat-flatten1 (mod-state mod)))))
  :hints ((set-reasoning)))

;; BOZO this shouldn't be necessary, rework the above theorems to fix it
(local (in-theory (disable commutativity-of-append-under-set-equiv)))

(defthm eval-alist-append-collect-i-state
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (4v-sexpr-eval-alist
                   (esim-sexpr-occs-out mod occs)
                   (append al1
                           (4v-alist-extract
                            (collect-signal-list
                             :i (occs-for-names occs mod))
                            env)
                           (4v-alist-extract
                            (pat-flatten1 (mod-state mod))
                            env)))
                  (4v-sexpr-eval-alist
                   (esim-sexpr-occs-out mod occs)
                   (append al1 env))))
  :hints (("goal" :in-theory (e/d ()
                                  (4v-sexpr-eval-alist-append-when-second-covers
                                   4v-sexpr-eval))
           :use ((:instance 4v-sexpr-eval-alist-append-when-second-covers
                            (al3 nil)
                            (al2 env)
                            (keys (append
                                   (collect-signal-list :i (occs-for-names occs mod))
                                   (pat-flatten1 (mod-state mod))))
                            (x (esim-sexpr-occs-out mod occs))))
           :do-not-induct t)))


(defexample 4v-alists-agree-lookup-ex
  :pattern (4v-lookup key al)
  :templates (key)
  :instance-rulename 4v-alists-agree-instancing)

(encapsulate
  nil
  (local (in-theory (e/d* ()
                          (esim-fixpoint-p-occs
                           esim-sexpr-occs-out
                           good-esim-modulep not
                           4v-sexpr-eval 4v-fix
                           ;set-equiv-trans
                           set-equiv-implies-key-and-env-equiv-4v-alist-extract-1
                           intersectp-equal-non-cons-1
                           intersectp-equal-non-cons
                           4v-alist-extract-when-subset
                           ; 4v-env-equiv-when-4v-alist-<=-both-ways
                           4v-env-equiv-to-key-and-env-equiv
                           eval-of-esim-sexpr-occs-when-esim-fixpoint-p-2
                           eval-of-esim-sexpr-occs-when-esim-fixpoint-p-1
                           esim-fixpoint-p-occs-when-<=
                           esim-wf-signals fal-extract
                           lookups-in-esim-sexpr-occs-out
                           alist-equiv-append-when-keys-nil
                           append ; 4v-sexpr-eval-lookup-in-atom-val-alist
                           4v-alist-extract
                           ;alist-equiv-append-atom
                           4v-sexpr-eval-possibilities
                           ; 4v-sexpr-fixpoint-lower-boundp-atom-ups
                           4v-alists-agree-commute
                           4v-alists-agree
                           4v-sexpr-eval-alist
                           set-equiv-asym pat-flatten
                           ; 4v-fix-when-4vp
                           esim-sexpr-correct-occsp
                           member-when-atom member-equal
                           alist-vals-when-atom
                           collect-signal-list
                           occmap-when-no-occs
                           hons-assoc-equal
                           alist-keys-when-atom
                           default-car default-cdr
                           esim-occ
                           ;var-assoc-key
                           (:rules-of-class :type-prescription :here)))))
  (defthm 4v-sexpr-fixpointp-lower-boundp-implies-esim-fixpoint-lower-boundp
    (implies (and (4v-sexpr-fixpoint-lower-boundp
                   (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                   fixpoint)
                  (set-equiv
                   (collect-signal-list :o (mod-occs mod))
                   (alist-keys fixpoint))
                  (and (good-esim-modulep mod) (not (gpl :x mod)))
                  (esim-sexpr-correct-occsp (gpl :occs mod)))
             (all-fixpoints-greater
              mod
              (append (4v-sexpr-eval-alist fixpoint env)
                      (4v-alist-extract
                       (pat-flatten1 (gpl :i mod))
                       env))
              env))
    :hints(("Goal" :do-not-induct t)
           (witness :ruleset all-fixpoints-greater-witnessing)
           (and stable-under-simplificationp
                '(:use ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
                                   (ups (esim-sexpr-occs-out mod (alist-keys
                                                                  (occmap mod))))
                                   (lb fixpoint)
                                   (env env)
                                   (fp (4v-alist-extract
                                        (alist-keys (esim-sexpr-occs-out
                                                     mod (alist-keys (occmap mod))))
                                        fixpoint0))))))
           (and stable-under-simplificationp
                '(:use ((:instance
                         eval-of-esim-sexpr-occs-when-esim-fixpoint-p-2
                         (fixpoint (append
                                    (4v-alist-extract
                                     (collect-signal-list :o (mod-occs mod))
                                     fixpoint0)
                                    (4v-alist-extract
                                     (collect-signal-list :i (mod-occs mod))
                                     env)))
                         (st (4v-alist-extract
                              (pat-flatten1 (mod-state mod))
                              env))
                         (occs (alist-keys (occmap mod)))))))
           (witness :ruleset (4v-env-equiv-witnessing
                              4v-env-equiv-4v-lookup-ex
                              4v-alist-<=-witnessing
                              4v-alist-<=-lookup-ex
                              4v-alists-agree-lookup-ex)))))





(defthm 4v-alists-agree-append-keys
  (iff (4v-alists-agree (append j k) a b)
       (and (4v-alists-agree j a b)
            (4v-alists-agree k a b)))
  :hints(("Goal" :in-theory (disable 4v-fix 4v-alists-agree-commute
                                     default-car default-cdr
                                     ;; 4v-fix-when-4vp
                                     ))))


(defthmd esim-occ-single-when-4v-alists-agree
  (implies (and (good-esim-occp occ)
                (4v-alists-agree (pat-flatten1 (gpl :i occ)) sigs1 sigs2)
                (4v-alists-agree (pat-flatten1 (occ-state occ)) sts1 sts2))
           (equal (esim-occ-single occ sigs1 sts1)
                  (esim-occ-single occ sigs2 sts2)))
  :hints(("Goal" :in-theory (e/d (4v-pat-alist-translate-when-4v-alists-agree
                                  esim-occ-single)
                                 (good-esim-occp
                                  esim-out esim-out-in-terms-of-least-fixpoint)))))


(Defthm 4v-alists-agree-occ-state-when-mod-state
  (implies (and (4v-alists-agree (pat-flatten1 (mod-state mod)) a b)
                (not (gpl :x mod)))
           (4v-alists-agree (pat-flatten1 (occ-state (esim-get-occ occ mod)))
                            a b))
  :hints(("Goal" :in-theory (enable 4v-alists-agree-subset))))

(defthm gpl-u-occmap-lookup
  (equal (gpl :u (cdr (hons-assoc-equal occ (occmap mod))))
         (and (hons-assoc-equal occ (occmap mod))
              occ))
  :hints(("Goal" :in-theory (enable occmap))))

(Defthm hons-assoc-equal-esim-occ-single
  (implies (good-esim-occp occ)
           (iff (hons-assoc-equal k (esim-occ-single occ sigs sts))
                (member-equal k (pat-flatten1 (gpl :o occ)))))
  :hints(("Goal" :in-theory (e/d (esim-occ-single) (esim-out esim-out-in-terms-of-least-fixpoint good-esim-occp)))))


(defthmd esim-fixpoint-p-occs-when-4v-alists-agree-with-sts
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (4v-alists-agree (collect-signal-list :i (occs-for-names occs mod))
                                 sigs1 sigs2)
                (4v-alists-agree (collect-signal-list :o (occs-for-names occs mod))
                                 sigs1 sigs2)
                (4v-alists-agree (pat-flatten1 (mod-state mod)) sts1 sts2))
           (iff (esim-fixpoint-p-occs mod occs sigs1 sts1)
                (esim-fixpoint-p-occs mod occs sigs2 sts2)))
  :hints (("goal" :induct (len occs)
           :in-theory (e/d* (esim-fixpoint-p-occs
                             esim-occ-single-when-4v-alists-agree
                             fal-extract)
                            (esim-occ-single
                             good-esim-occp similar-patternsp
                             esim-wf-signals
                             esim-occ-single-when-4v-alists-agree
                             esim-occ 4v-fix
                             default-car default-cdr
                             hons-assoc-equal
                             ; 4v-fix-when-4vp
                             4v-alists-agree
                             member-equal member-when-atom
                             alist-equiv-append-when-keys-nil
                             good-esim-modulep
                             occmap-when-no-occs
                             member-pat-flatten-gpl-of-lookup
                             esim-fixpoint-p-occs-when-<=
                             append 4v-env-equiv-to-key-and-env-equiv
                             pat-flatten
                             (:rules-of-class :type-prescription :here))))
          (and stable-under-simplificationp
               '(:use ((:instance esim-occ-single-when-4v-alists-agree
                                  (occ (esim-get-occ (car occs) mod))))))
          (witness :ruleset (4v-env-equiv-witnessing
                             4v-env-equiv-4v-lookup-ex
                             4v-alists-agree-lookup-ex))))


(encapsulate nil
  (local (in-theory (disable*
                     (:ruleset good-esim-mod-impl)
                     4v-sexpr-fixpointp-implies-esim-fixpoint-p
                     good-esim-modulep
                     ; 4v-sexpr-fixpointp-is-alt1
                     esim-fixpoint-p-occs
                     esim-sexpr-occs-out
                     4v-sexpr-eval 4v-fix
                     esim-fixpoint-p-occs-when-<=
                     esim-occ hons-assoc-equal
                     4v-fix default-car default-cdr
                     good-esim-modulep-ins-not-intersecting-states
                     ; good-esim-modulep-st-subset-not-intersecting-inputs
                     subsetp-car-member
                     subsetp-when-atom-left
                     alist-keys-when-atom
                     pat-flatten
                     append fal-extract
                     good-esim-occp
                     esim-fixpoint-p-occs
                     4v-alists-agree set-equiv-asym
                     (:rules-of-class :type-prescription :here))))
  (defthm 4v-sexpr-fixpointp-implies-esim-fixpoint-p-2
    (implies (and (4v-sexpr-fixpointp
                   (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                   fixpoint)
                  (set-equiv
                   (collect-signal-list :o (mod-occs mod))
                   (alist-keys fixpoint))
                  (good-esim-modulep mod) (not (gpl :x mod))
                  (esim-sexpr-correct-occsp (gpl :occs mod)))
             (esim-fixpoint-p
              mod
              (append (4v-sexpr-eval-alist fixpoint env)
                      (4v-alist-extract
                       (pat-flatten1 (gpl :i mod)) env))
              env))
    :hints (("goal"
             :use ((:instance 4v-sexpr-fixpointp-implies-esim-fixpoint-p)
                   (:instance esim-fixpoint-p-occs-when-4v-alists-agree-with-sts
                              (occs (alist-keys (occmap mod)))
                              (sigs1 (APPEND (4V-SEXPR-EVAL-ALIST FIXPOINT ENV)
                                             ENV))
                              (sigs2 (APPEND (4V-SEXPR-EVAL-ALIST FIXPOINT ENV)
                                             (4V-ALIST-EXTRACT (PAT-FLATTEN1 (GPL :I MOD))
                                                               ENV)))
                              (sts1 (APPEND (4V-SEXPR-EVAL-ALIST FIXPOINT ENV)
                                            ENV))
                              (sts2 env)))
             :do-not-induct t)
            (witness :ruleset 4v-alists-agree-witnessing)
            (and stable-under-simplificationp
                 '(:expand
                   ((good-esim-modulep mod))
                   :in-theory (e/d
                               (hons-assoc-equal-iff-member-alist-keys
                                occmap-when-no-occs)
                               (alist-keys-member-hons-assoc-equal))))
            (set-reasoning))
    :otf-flg t))


(defthm 4v-sexpr-fixpoint-lower-boundp-implies-esim-fixpoint-lower-boundp
  (implies (and (4v-sexpr-fixpoint-lower-boundp
                 (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                 fixpoint)
                (set-equiv
                 (collect-signal-list :o (mod-occs mod))
                 (alist-keys fixpoint))
                (good-esim-modulep mod) (not (gpl :x mod))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (all-fixpoints-greater
            mod
            (append (4v-sexpr-eval-alist fixpoint env)
                    (4v-alist-extract
                     (pat-flatten1 (gpl :i mod))
                     env))
            env)))

;; redundant
(defthm 4v-sexpr-fixpointp-implies-esim-fixpoint-p-2
    (implies (and (4v-sexpr-fixpointp
                   (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                   fixpoint)
                  (set-equiv
                   (collect-signal-list :o (mod-occs mod))
                   (alist-keys fixpoint))
                  (good-esim-modulep mod) (not (gpl :x mod))
                  (esim-sexpr-correct-occsp (gpl :occs mod)))
             (esim-fixpoint-p
              mod
              (append (4v-sexpr-eval-alist fixpoint env)
                      (4v-alist-extract
                       (pat-flatten1 (gpl :i mod)) env))
              env)))

(defthm 4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
  (implies (and (4v-sexpr-fixpointp
                 (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                 fixpoint)
                (4v-sexpr-fixpoint-lower-boundp
                 (esim-sexpr-occs-out mod (alist-keys (occmap mod)))
                 fixpoint)
                (set-equiv
                   (collect-signal-list :o (mod-occs mod))
                   (alist-keys fixpoint))
                (good-esim-modulep mod) (not (gpl :x mod))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (equal (4v-env-equiv (append (4v-sexpr-eval-alist fixpoint env)
                                        (4v-alist-extract
                                         (pat-flatten1 (gpl :i mod)) env))
                                (esim-least-fixpoint
                                 mod
                                 (4v-alist-extract
                                  (pat-flatten1 (gpl :i mod)) env)
                                 env))
                  t))
  :hints (("goal"
           :use ((:instance esim-least-fixpoint-unique
                            (fixpoint1 (append (4v-sexpr-eval-alist fixpoint env)
                                               (4v-alist-extract
                                                (pat-flatten1 (gpl :i mod))
                                                env)))
                            (fixpoint2 (esim-least-fixpoint
                                        mod
                                        (4v-alist-extract
                                         (pat-flatten1 (gpl :i mod)) env)
                                        env))
                            (st-al env))
                 (:instance least-fixpointp-esim-least-fixpoint
                            (sig-al (4v-alist-extract
                                     (pat-flatten1 (gpl :i mod)) env))
                            (st-al env)))
           :in-theory (disable least-fixpointp-esim-least-fixpoint
                               good-esim-modulep
                               esim-fixpoint-p 4v-fix
                               hons-assoc-equal
                               esim-sexpr-occs-out
                               4v-alist-extract
                               4v-alists-agree
                               esim-wf-signals-impl-esim-occs-incr
                               4v-alist-extract-when-subset
                               pat-flatten
                               4v-alistp
                               set-equiv-asym default-car default-cdr
                               subsetp-when-atom-left
                               keys-equiv-when-alist-keys
                               input-subset-bound-impl-esim-wf-signals
                               alist-keys-when-atom
                               esim-fixpoint
                               append
                               esim-wf-signals
                               4v-sexpr-eval-alist)
           :do-not-induct t)
          (witness :ruleset (4v-alists-agree-witnessing
                             4v-alists-agree-lookup-ex)))
  :otf-flg t)


(defthm alist-keys-sexpr-fixpoint-with-varmap
  (implies (good-sexpr-varmap varmap ups)
           (set-equiv (alist-keys (sexpr-fixpoint-with-varmap ups varmap))
                       (alist-keys ups))))

(defthm alist-keys-esim-sexpr-fixpoint-out
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (set-equiv (alist-keys (esim-sexpr-fixpoint-out mod))
                       (collect-signal-list :o (mod-occs mod))))
  :hints(("Goal" :expand ((esim-sexpr-fixpoint-out mod))
          :in-theory (disable esim-sexpr-occs-out
                              esim-sexpr-occs-out
                              sexpr-fixpoint-with-varmap))))

(defthm esim-sexpr-fixpoint-gives-esim-least-fixpoint
  (implies (and (good-esim-modulep mod) (not (gpl :x mod))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (4v-env-equiv (append (4v-sexpr-eval-alist
                                  (esim-sexpr-fixpoint-out mod)
                                  env)
                                 (4v-alist-extract
                                  (pat-flatten1 (gpl :i mod)) env))
                         (esim-least-fixpoint
                          mod
                          (4v-alist-extract (pat-flatten1 (gpl :i mod)) env)
                          env)))
  :hints(("Goal" :in-theory
          (e/d () (4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                   good-esim-modulep
                   esim-sexpr-correct-occsp
                   4v-sexpr-eval-alist
                   extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                   esim-fixpoint-p-occs-when-<=
                   esim-fixpoint-p
                   esim-sexpr-fixpoint-out
                   4v-alist-extract))
          :use ((:instance 4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                           (fixpoint (esim-sexpr-fixpoint-out mod))))
          :do-not-induct t)))

(defthm hons-assoc-equal-esim-sexpr-fixpoint-out
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (iff (hons-assoc-equal key (esim-sexpr-fixpoint-out mod))
                (member-equal key (collect-signal-list :o (mod-occs mod)))))
  :hints (("goal" :expand ((esim-sexpr-fixpoint-out mod)))))

(defthm good-esim-modulep-not-member-ins-and-outs
  (implies (and (Good-esim-modulep mod)
                (member-equal x (pat-flatten1 (gpl :i mod))))
           (not (member-equal x (pat-flatten1 (gpl :o mod)))))
  :hints (("goal" :expand ((good-esim-modulep mod))
           :in-theory (disable* (:ruleset good-esim-mod-impl)
                                good-esim-modulep))
          (set-reasoning)))

(add-to-ruleset good-esim-mod-impl
                '(good-esim-modulep-not-member-ins-and-outs))

(defthm 4v-sexpr-eval-fixpoint-lemma
  (implies
   (and (good-esim-modulep mod)
        (not (gpl :x mod))
        (esim-sexpr-correct-occsp (gpl :occs mod)))
   (key-and-env-equiv
    (4v-alist-extract
     (pat-flatten1 (gpl :o mod))
     (4v-sexpr-eval-alist (esim-sexpr-fixpoint-out mod)
                          env0))
    (4v-alist-extract
     (pat-flatten1 (gpl :o mod))
     (esim-least-fixpoint mod
                          (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                            env0)
                          env0))))
  :hints (("goal" :use ((:instance esim-sexpr-fixpoint-gives-esim-least-fixpoint
                                   (env env0)))
           :in-theory (e/d (key-and-env-equiv)
                           (esim-sexpr-fixpoint-gives-esim-least-fixpoint
                            4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                            4v-env-equiv-to-key-and-env-equiv
                            4v-sexpr-eval-alist
                            4v-sexpr-eval
                            esim-fixpoint-p-occs-when-<=
                            esim-fixpoint-equiv-when-mod-fixpoint
                            esim-fixpoint-p
                            esim-sexpr-fixpoint-out
                            good-esim-modulep 4v-fix)))
          (witness :ruleset (4v-env-equiv-witnessing
                             4v-env-equiv-lookup-ex))))


(defthm 4v-sexpr-eval-fixpoint-lemma2
  (implies
   (and (good-esim-modulep mod) (not (gpl :x mod))
        (esim-sexpr-correct-occsp (gpl :occs mod)))
   (4v-alists-agree
    (collect-signal-list :o (mod-occs mod))
    (append (4v-sexpr-eval-alist (esim-sexpr-fixpoint-out mod)
                                 env0)
            env0)
    (esim-least-fixpoint mod
                         (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                           env0)
                         env0)))
  :hints (("goal" :use ((:instance esim-sexpr-fixpoint-gives-esim-least-fixpoint
                                   (env env0)))
           :in-theory (e/d* ()
                            ((:rules-of-class :definition :here)
                             esim-sexpr-fixpoint-gives-esim-least-fixpoint
                             4v-sexpr-least-fixpointp-implies-esim-least-fixpoint)
                            (4v-lookup hons-get)))
          (witness :ruleset (4v-env-equiv-witnessing
                             4v-env-equiv-4v-lookup-ex
                             4v-alists-agree-witnessing
                             4v-alists-agree-lookup-ex))))


(defthm 4v-sexpr-eval-fixpoint-lemma2.5
  (implies
   (and (good-esim-modulep mod) (not (gpl :x mod))
        (esim-sexpr-correct-occsp (gpl :occs mod)))
   (4v-alists-agree
    (collect-signal-list :i (mod-occs mod))
    (append (4v-sexpr-eval-alist (esim-sexpr-fixpoint-out mod)
                                 env0)
            env0)
    (esim-least-fixpoint mod
                         (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                           env0)
                         env0)))
  :hints (("goal" :use ((:instance 4v-sexpr-eval-fixpoint-lemma2)
                        (:instance least-fixpointp-esim-least-fixpoint
                                   (sig-al (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                           env0))
                                   (st-al env0)))
           :in-theory (e/d* (hons-assoc-equal-iff-member-alist-keys
                             hons-assoc-equal-when-not-member-alist-keys
                             occmap-when-no-occs)
                            ((:rules-of-class :definition :here)
                             (:rules-of-class :type-prescription :here)
                             (:ruleset good-esim-mod-impl)
                             occmap-when-no-occs
                             alist-keys-member-hons-assoc-equal
                             least-fixpointp-esim-least-fixpoint
                             4v-sexpr-eval-fixpoint-lemma2
                             esim-sexpr-fixpoint-gives-esim-least-fixpoint
                             4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                             subsetp-when-atom-left
                             subsetp-trans
                             intersectp-equal-non-cons
                             intersectp-equal-non-cons-1
                             alist-keys-when-atom
                             alist-vals-when-atom
                             no-duplicatesp-equal-non-cons
                             ; no-duplicatesp-equal-when-high-duplicity
                             ;no-duplicatesp-equal-when-duplicity-badguy1
                             consp-append
                             default-car default-cdr hons-assoc-equal
                             ; good-esim-modulep-st-subset-not-intersecting-inputs
                             good-esim-modulep-ins-not-intersecting-states)
                            (4v-lookup hons-get))
           :expand ((good-esim-modulep mod)))
          (witness :ruleset (4v-alists-agree-witnessing
                             4v-alists-agree-lookup-ex))
          (set-reasoning)))


(defthmd all-fixpoints-greater-when-4v-alists-agree
  (implies (and (4v-alists-agree (pat-flatten1 (mod-state mod)) st1 st2)
                (good-esim-modulep mod) (not (gpl :x mod)))
           (iff (all-fixpoints-greater mod fixpoint st1)
                (all-fixpoints-greater mod fixpoint st2)))
  :hints (("goal" :in-theory (disable esim-fixpoint-p-occs
                                      good-esim-modulep
                                      esim-wf-signals
                                      4v-env-equiv-to-key-and-env-equiv))
          (witness :ruleset (all-fixpoints-greater-witnessing
                             all-fixpoints-greater-fixpoint-ex))
          (and stable-under-simplificationp
               '(:use ((:instance esim-fixpoint-p-occs-when-4v-alists-agree-with-sts
                                  (occs (alist-keys (occmap mod)))
                                  (sigs1 fixpoint0)
                                  (sigs2 fixpoint0)
                                  (sts1 st1) (sts2 st2)))))))

(defthmd esim-least-fixpoint-when-4v-alists-agree
  (implies (and (4v-alists-agree (pat-flatten1 (mod-state mod)) st1 st2)
                (subsetp-equal (alist-keys ins)
                               (pat-flatten1 (gpl :i mod)))
                (good-esim-modulep mod) (not (gpl :x mod)))
           (4v-env-equiv (esim-least-fixpoint mod ins st1)
                         (esim-least-fixpoint mod ins st2)))
  :hints (("goal" :use ((:instance esim-least-fixpoint-unique
                                   (fixpoint1 (esim-least-fixpoint mod ins
                                                                   st1))
                                   (fixpoint2 (esim-least-fixpoint mod ins
                                                                   st2))
                                   (st-al st2))
                        (:instance all-fixpoints-greater-when-4v-alists-agree
                                   (fixpoint (esim-least-fixpoint mod ins
                                                                  st1)))
                        (:instance esim-fixpoint-p-occs-when-4v-alists-agree-with-sts
                                   (sigs1 (esim-least-fixpoint mod ins
                                                                  st1))
                                   (sigs2 (esim-least-fixpoint mod ins
                                                                  st1))
                                   (sts1 st1) (sts2 st2)
                                   (occs (alist-keys (occmap mod))))
                        (:instance least-fixpointp-esim-least-fixpoint
                                   (sig-al ins) (st-al st1))
                        (:instance least-fixpointp-esim-least-fixpoint
                                   (sig-al ins) (st-al st2)))
           :in-theory (e/d* ()
                           (; 4v-env-equiv-when-4v-alist-<=-both-ways
                            least-fixpointp-esim-least-fixpoint
                            esim-fixpoint-p-occs
                            esim-fixpoint-p-occs-when-<=
                            esim-fixpoint-equiv-when-mod-fixpoint
                            esim-occs 4v-alist-extract esim-fixpoint
                            default-car default-cdr hons-assoc-equal
                            4v-alist-extract-when-subset
                            subsetp-when-atom-left
                            alist-keys-when-atom
                            alist-vals-when-atom
                            alist-equiv-append-when-keys-nil
                            collect-signal-list
                            append
                            (:rules-of-class :type-prescription :here)
                            ; esim-fixpoint-p
                            good-esim-modulep
                            esim-wf-signals 4v-fix
                            4v-env-equiv-to-key-and-env-equiv)))
          (witness :ruleset (4v-alists-agree-witnessing
                             4v-alists-agree-lookup-ex))))


(defthm 4v-sexpr-eval-fixpoint-lemma3
  (implies
   (and (good-esim-modulep mod) (not (gpl :x mod))
        (esim-sexpr-correct-occsp (gpl :occs mod)))
   (key-and-env-equiv
    (4v-alist-extract
     (pat-flatten1 (gpl :o mod))
     (esim-least-fixpoint mod
                          (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                            env0)
                          (4v-alist-extract (pat-flatten1 (mod-state mod))
                                            env0)))
    (4v-alist-extract
     (pat-flatten1 (gpl :o mod))
     (esim-least-fixpoint mod
                          (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                            env0)
                          env0))))
  :hints (("goal" :in-theory (e/d (key-and-env-equiv)
                                  (4v-env-equiv-to-key-and-env-equiv
                                   good-esim-modulep
                                   esim-fixpoint-p
                                   4v-fix))
           :use ((:instance esim-least-fixpoint-when-4v-alists-agree
                            (ins (4v-alist-extract
                                  (pat-flatten1 (gpl :i mod)) env0))
                            (st1 (4v-alist-extract
                                  (pat-flatten1 (mod-state mod))
                                  env0))
                            (st2 env0)))))
  :otf-flg t)

(local
 (defthm lemma6
   (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
            (not (intersectp-equal (alist-keys (esim-sexpr-fixpoint-out mod))
                                   (pat-flatten1 (mod-state mod)))))))

(local
 (defthm lemma5
   (implies (not (intersectp-equal (alist-keys foo) keys))
            (4v-alists-agree keys
                             (append foo env0)
                             (4v-alist-extract keys env0)))
   :hints (("goal" :do-not-induct t
            :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                            (alist-keys-member-hons-assoc-equal
                             4v-fix)))
           (witness :ruleset 4v-alists-agree-witnessing)
           (set-reasoning))))

(defthm alists-agree-4v-alist-extract
  (4v-alists-agree keys a (4v-alist-extract keys a))
  :hints ((witness :ruleset 4v-alists-agree-witnessing)))

(defthm 4v-pat-alist-translate-self-is-4v-alist-extract
  (equal (4v-pat-alist-translate x x al nil)
         (4v-alist-extract (pat-flatten1 x) al)))

(defthm esim-sexpr-correct-modp-when-esim-sexpr-correct-occsp
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (esim-sexpr-correct-modp mod))
  :hints (("goal" :do-not-induct t
           :cases ((gpl :x mod)) ;; primitivep
           :in-theory (e/d ()
                           (extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                            esim-fixpoint-p esim-out esim-sexpr-fixpoint-out
                            eapply-spec
                            good-esim-modulep eapply-spec eapply-sexpr))
           :expand ((esim-sexpr-general-out mod)))
          (witness :ruleset esim-sexpr-correct-modp-witnessing)
          ;; (and stable-under-simplificationp
          ;;      '(:in-theory
          ;;        (e/d (;; esim-sexpr-fixpoint-out-nst
          ;;              )
          ;;             (extract-of-esim-fixpoint-equiv-esim-least-fixpoint
          ;;              esim-out esim-sexpr-fixpoint-out
          ;;              eapply-spec
          ;;              esim-fixpoint-p good-esim-modulep))))
          )
  :otf-flg t)

(mutual-recursion
 (defun esim-ind-mod (x)
   (declare (Xargs :measure (list (acl2-count x) 3)
                   :well-founded-relation nat-list-<))
   (if (gpl :x x)
       x
     (esim-ind-occs (gpl :occs x))))
 (defun esim-ind-occs (x)
   (declare (Xargs :measure (list (acl2-count x) 2)))
   (if (atom x)
       nil
     (cons (esim-ind-occ (car x))
           (esim-ind-occs (cdr x)))))
 (defun esim-ind-occ (x)
   (declare (Xargs :measure (list (acl2-count x) 4)))
   (esim-ind-mod (gpl :op x))))

(flag::make-flag esim-flag esim-ind-mod
                 :flag-mapping ((esim-ind-mod mod)
                                (esim-ind-occs occs)
                                (esim-ind-occ occ)))

(defthm-esim-flag
  (defthm esim-sexpr-correct-modp-mods
    (implies (good-esim-modulep x)
             (esim-sexpr-correct-modp x))
    :hints ('(:expand (good-esim-modulep x)))
    :flag mod)
  (defthm esim-sexpr-correct-occsp-occs
    (implies (good-esim-occsp x)
             (esim-sexpr-correct-occsp x))
    :hints ('(:expand (good-esim-occsp x)))
    :flag occs)
  (defthm esim-sexpr-correct-modp-op-occ
    (implies (good-esim-occp x)
             (esim-sexpr-correct-modp (gpl :op x)))
    :hints ('(:expand (good-esim-occp x)))
    :flag occ)
  :hints (("goal" :in-theory (disable good-esim-modulep
                                      good-esim-occsp
                                      good-esim-occp))))






;;; !! WOO

(defthm 4v-sexpr-eval-of-esim-sexpr-general-out
  (implies (good-esim-modulep mod)
           (b* ((sexpr-out (4v-sexpr-alist-extract
                            (pat-flatten1 (gpl :o mod))
                            (esim-sexpr-general-out mod)))
                (spec-out (esim-out mod env env)))
             (4v-env-equiv (4v-sexpr-eval-alist sexpr-out env)
                           spec-out)))
  :hints (("goal" :in-theory (disable 4v-sexpr-alist-extract
                                      esim-sexpr-general-out
                                      esim-out
                                      4v-sexpr-eval-alist-4v-sexpr-alist-extract
                                      esim-out-in-terms-of-least-fixpoint
                                      4v-sexpr-eval-alist
                                      good-esim-modulep))))

(defthm 4v-sexpr-eval-of-esim-sexpr-out
  (implies (good-esim-modulep mod)
           (b* ((sexpr-out (esim-sexpr-out mod sig-al st-al))
                (spec-out
                 (esim-out mod
                           (4v-sexpr-eval-alist sig-al env)
                           (4v-sexpr-eval-alist st-al env))))
             (equal (4v-sexpr-eval-alist sexpr-out env)
                    spec-out)))
  :hints(("Goal" :in-theory
          '(4v-sexpr-eval-of-esim-sexpr-out-when-esim-correct-modp
            esim-sexpr-correct-modp-mods
            4v-env-equiv-is-an-equivalence))))




(defthmd 4v-sexpr-alist-extract-cdr-when-car-not-in-keys
  (implies (and (consp (car al))
                (not (member-equal (caar al) keys)))
           (equal (4v-sexpr-alist-extract keys (cdr al))
                  (4v-sexpr-alist-extract keys al))))

(defthmd 4v-sexpr-alist-extract-idempotent
  (implies (and (alistp al)
                (equal (alist-keys al) keys)
                (no-duplicatesp-equal keys))
           (equal (4v-sexpr-alist-extract keys al) al))
  :hints(("Goal" :in-theory
          (enable 4v-sexpr-alist-extract-cdr-when-car-not-in-keys
                  alist-keys))))

(defthm alistp-4v-sexpr-restrict-alist
  (alistp (4v-sexpr-restrict-alist al env)))

(defthm alist-keys-occ-nst
  (equal (alist-keys (esim-sexpr-occ-nst occ))
         (pat-flatten1 (occ-state occ)))
  :hints (("goal" :in-theory (disable esim-sexpr-nst)
           :expand ((esim-sexpr-occ-nst occ)))))

(defthm alist-keys-esim-sexpr-occs-nst
  (equal (alist-keys (esim-sexpr-occs-nst mod occs))
         (pat-flatten1 (occs-state (alist-vals (fal-extract occs (occmap mod))))))
  :hints(("Goal" :in-theory (enable occs-state fal-extract)
          :expand ((esim-sexpr-occs-nst mod occs))
          :induct (len occs))))

(defthmd fal-extract-cdr-when-car-not-in-keys
  (implies (and (consp (car al))
                (not (member-equal (caar al) keys)))
           (equal (fal-extract keys (cdr al))
                  (fal-extract keys al)))
  :hints(("Goal" :in-theory (enable fal-extract))))

(defthm fal-extract-keys-when-no-duplicates
  (implies (and (no-duplicatesp-equal (alist-keys al))
                (alistp al))
           (equal (fal-extract (alist-keys al) al)
                  al))
  :hints(("Goal" :in-theory (enable alist-keys no-duplicatesp-equal
                                    fal-extract-cdr-when-car-not-in-keys
                                    fal-extract))))


(defthm alistp-occmap1
  (alistp (occmap1 occs)))

(Defthm alistp-occmap
  (alistp (occmap mod))
  :hints(("Goal" :in-theory (enable occmap))))

(defthm alist-vals-occmap1
  (equal (alist-vals (occmap1 occs)) (append occs nil)))

(defthm alist-vals-occmap
  (equal (alist-vals (occmap mod))
         (append (gpl :occs mod) nil))
  :hints(("Goal" :in-theory (enable occmap))))

(defthm occs-state-append-nil
  (equal (occs-state (append x nil))
         (occs-state x)))

(defthm alist-keys-esim-sexpr-occs-nst-whole
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (equal (alist-keys (esim-sexpr-occs-nst mod (alist-keys (occmap mod))))
                  (pat-flatten1 (mod-state mod))))
  :hints(("Goal" :expand ((mod-state mod))
          :in-theory (enable good-esim-modulep))))

(defthm alist-keys-eapply-sexpr-nst
  (implies (and (good-esim-modulep mod)
                (gpl :x mod))
           (equal (alist-keys (mv-nth 0 (eapply-sexpr (gpl :x mod))))
                  (pat-flatten1 (mod-state mod))))
  :hints (("goal" :in-theory '(eapply-sexpr
                               make-fast-alist
                               good-esim-modulep good-esim-primitivep
                               alist-keys-4v-sexpr-alist-extract
                               append-right-id))))

(defthm 4v-sexpr-alist-extract-eapply-sexpr-nst
  (implies (and (good-esim-modulep mod)
                (gpl :x mod))
           (equal (4v-sexpr-alist-extract
                   (pat-flatten1 (mod-state mod))
                   (mv-nth 0 (eapply-sexpr (gpl :x mod))))
                  (mv-nth 0 (eapply-sexpr (gpl :x mod)))))
  :hints(("Goal" :in-theory '(eapply-sexpr
                              make-fast-alist
                              4v-sexpr-alist-extract-idempotent
                              good-esim-modulep good-esim-primitivep
                              hons-dups-p-is-no-duplicatesp
                              no-duplicatesp-equal-append-iff
                              subsetp-refl)
          :expand ((good-esim-modulep mod)))))


(defthmd alist-equiv-append-switch-when-keys-not-intersecting
  (implies (not (intersectp-equal (alist-keys a) (alist-keys b)))
           (alist-equiv (append b a)
                        (append a b)))
  :hints ((witness :ruleset alist-equiv-witnessing)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal))))
          (set-reasoning)))

(defthmd alist-equiv-append-switch-first-two-when-keys-not-intersecting
  (implies (not (intersectp-equal (alist-keys a) (alist-keys b)))
           (alist-equiv (append b a c)
                        (append a b c)))
  :hints ((witness :ruleset alist-equiv-witnessing)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal))))
          (set-reasoning)))

(defthm no-duplicates-occmap-keys-when-good-modulep
  (implies (good-esim-modulep mod)
           (no-duplicatesp-equal (alist-keys (occmap mod))))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))


(defthmd state-of-occ-not-intersecting-member
  (implies (and (not (intersectp-equal (pat-flatten1 (occ-state occ))
                                       (pat-flatten1 (occs-state occs))))
                (member-equal occ2 occs))
           (not (intersectp-equal (pat-flatten1 (occ-state occ))
                                  (pat-flatten1 (occ-state occ2)))))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthmd state-of-occ-not-intersecting-member1
  (implies (and (not (intersectp-equal (pat-flatten1 (occ-state occ))
                                       (pat-flatten1 (occs-state occs))))
                (member-equal occ2 occs))
           (not (intersectp-equal (pat-flatten1 (occ-state occ2))
                                  (pat-flatten1 (occ-state occ)))))
  :hints(("Goal" :in-theory (enable state-of-occ-not-intersecting-member))))


(defthmd states-of-diff-occs-not-intersecting
  (implies (and (no-duplicatesp-equal (pat-flatten1 (occs-state occs)))
                (member-equal occ1 occs)
                (member-equal occ2 occs)
                (not (equal occ1 occ2)))
           (not (intersectp-equal (pat-flatten1 (occ-state occ1))
                                  (pat-flatten1 (occ-state occ2)))))
  :hints(("Goal" :in-theory (enable member-equal
                                    state-of-occ-not-intersecting-member
                                    state-of-occ-not-intersecting-member1))))

(defthm states-of-diff-occs-not-intersecting-occs-of-mod
  (implies (and (no-duplicatesp-equal (pat-flatten1 (mod-state mod)))
                (member-equal occ1 (gpl :occs mod))
                (member-equal occ2 (gpl :occs mod))
                (not (gpl :x mod))
                (not (equal occ1 occ2)))
           (not (intersectp-equal (pat-flatten1 (occ-state occ1))
                                  (pat-flatten1 (occ-state occ2)))))
  :hints(("Goal" :in-theory (enable states-of-diff-occs-not-intersecting
                                    mod-state))))

(defthm member-lookup-of-occmap1
  (implies (hons-assoc-equal name (occmap1 occs))
           (member-equal (cdr (hons-assoc-equal name (occmap1 occs))) occs)))

(defthm lookups-in-occmap1-equal
  (implies (and (hons-assoc-equal x (occmap1 occs))
                (hons-assoc-equal y (occmap1 occs)))
           (equal (equal (cdr (hons-assoc-equal x (occmap1 occs)))
                         (cdr (hons-assoc-equal y (occmap1 occs))))
                  (equal x y))))

(defthm lookups-in-occmap-equal
  (implies (and (hons-assoc-equal x (occmap mod))
                (hons-assoc-equal y (occmap mod)))
           (equal (equal (cdr (hons-assoc-equal x (occmap mod)))
                         (cdr (hons-assoc-equal y (occmap mod))))
                  (equal x y)))
  :hints(("Goal" :in-theory (enable occmap))))

(defthm state-of-occ-not-intersecting-rest
  (implies (and (no-duplicatesp-equal (pat-flatten1 (mod-state mod)))
                (not (member-equal occname rest-occnames))
                (not (gpl :x mod)))
           (not (intersectp-equal
                 (pat-flatten1 (occ-state (esim-get-occ occname mod)))
                 (pat-flatten1 (occs-state (alist-vals (fal-extract
                                                        rest-occnames (occmap mod))))))))
  :hints(("Goal" :in-theory
          (e/d (fal-extract alist-vals occs-state member-equal)
               (good-esim-modulep occ-state gpl-u-occmap-lookup
                                  default-car default-cdr))
          :induct t)
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal occname (occmap mod)))))
         (and stable-under-simplificationp
              '(:cases ((gpl :occs mod))))))









(defquant esim-sexpr-correct-nst-modp (mod)
  (forall env (b* ((sexpr-nst (esim-sexpr-general-nst mod))
                   (spec-nst  (esim-nst mod env env)))
                (4v-env-equiv (4v-sexpr-eval-alist sexpr-nst env)
                              spec-nst))))

(defthmd esim-sexpr-correct-nst-modp-implies
  (implies (esim-sexpr-correct-nst-modp mod)
           (b* ((sexpr-nst (esim-sexpr-general-nst mod))
                (spec-nst  (esim-nst mod env env)))
             (4v-env-equiv (4v-sexpr-eval-alist sexpr-nst env)
                           spec-nst)))
  :hints (("goal" :use esim-sexpr-correct-nst-modp-necc
           :in-theory nil)))


(defthmd 4v-alist-extract-4v-alists-agree
  (implies (4v-alists-agree keys a b)
           (equal (4v-alist-extract keys a)
                  (4v-alist-extract keys b))))


(defthmd esim-nst-when-4v-alists-agree-input
  (implies (4v-alists-agree (pat-flatten1 (gpl :i mod)) in1 in2)
           (equal (esim-nst mod in1 sa) (esim-nst mod in2 sa)))
  :hints(("Goal" :in-theory (e/d (4v-alist-extract-4v-alists-agree)
                                 (esim-occs-nst eapply-spec-nst
                                                esim-fixpoint
                                                4v-alists-agree))
          :expand ((:free (in) (esim-nst mod in sa))))))

(defthmd esim-nst-when-4v-alists-agree-st
  (implies (4v-alists-agree (pat-flatten1 (mod-state mod)) st1 st2)
           (equal (esim-nst mod ia st1) (esim-nst mod ia st2)))
  :hints(("Goal" :in-theory (e/d (4v-alist-extract-4v-alists-agree)
                                 (esim-occs-nst eapply-spec-nst
                                                esim-fixpoint
                                                4v-alists-agree))
          :expand ((:free (st) (esim-nst mod ia st))))))



(defthmd esim-nst-norm-appended-extracted-ins
  (equal (esim-nst mod (append (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                                 env)
                               rest)
                   st)
         (esim-nst mod env st))
  :hints(("Goal" :use ((:instance esim-nst-when-4v-alists-agree-input
                                  (in1 (append (4v-alist-extract
                                                (pat-flatten1 (gpl :i mod))
                                                env)
                                               rest))
                                  (in2 env) (sa st)))
          :in-theory (disable esim-nst))
         (witness :ruleset 4v-alists-agree-witnessing)))

(defthmd not-member-sts-when-member-ins
  (implies (and (good-esim-modulep mod)
                (member-equal k (pat-flatten1 (mod-state mod))))
           (not (member-equal k (pat-flatten1 (gpl :i mod)))))
  :hints(("Goal" :expand ((good-esim-modulep mod))
          :in-theory '(hons-dups-p-is-no-duplicatesp
                       no-duplicatesp-equal-append-iff
                       member-equal-append))
         (witness :ruleset set-reasoning-no-consp)))


(defthmd esim-nst-norm-appended-extracted-sts
  (implies (good-esim-modulep mod)
           (equal (esim-nst mod in
                            (append (4v-alist-extract (pat-flatten1 (gpl :i mod))
                                                      other)
                                    (4v-alist-extract (pat-flatten1 (mod-state mod))
                                                      env)))
                  (esim-nst mod in env)))
  :hints(("Goal" :use ((:instance esim-nst-when-4v-alists-agree-st
                                  (st1 (append (4v-alist-extract
                                                (pat-flatten1 (gpl :i mod))
                                                other)
                                               (4v-alist-extract
                                                (pat-flatten1 (mod-state mod))
                                                env)))
                                  (st2 env) (ia in)))
          :in-theory (e/d (not-member-sts-when-member-ins)
                          (esim-nst)))
         (witness :ruleset 4v-alists-agree-witnessing)))















(defthm alist-keys-eapply-spec-nst
  (implies (and (good-esim-modulep mod)
                (gpl :x mod)) ;; primitivep
           (equal (alist-keys (mv-nth 0 (eapply-spec al (gpl :x mod))))
                  (pat-flatten1 (mod-state mod))))
  :hints (("goal" :in-theory '(eapply-spec
                               make-fast-alist
                               good-esim-modulep
                               good-esim-primitivep
                               alist-keys-4v-sexpr-eval-alist
                               append-right-id))))


(defthm 4v-alistp-eapply-spec-nst
  (4v-alistp (mv-nth 0 (eapply-spec env x)))
  :hints (("goal" :in-theory '(eapply-spec make-fast-alist
                                           4v-alistp-4v-sexpr-eval-alist))))

(defthm 4v-alistp-append
  (implies (and (4v-alistp a) (4v-alistp b))
           (4v-alistp (append a b))))

(defthm 4v-alistp-4v-pat-alist-translate
  (4v-alistp (4v-pat-alist-translate pat1 pat2 al nil)))

(defthm 4v-alistp-esim-occ-nst
  (4v-alistp (esim-occ-nst occ fixpoint st))
  :hints (("goal" :expand ((esim-occ-nst occ fixpoint st))
           :in-theory (disable esim-nst))))

(defthm 4v-alistp-esim-occs-nst
  (4v-alistp (esim-occs-nst mod occs fixpoint st))
  :hints (("goal" :induct (len occs)
           :expand ((esim-occs-nst mod occs fixpoint st)))))

(defthm 4v-alistp-esim-nst
  (4v-alistp (esim-nst mod ia sa))
  :hints (("goal" :expand ((esim-nst mod ia sa))
           :in-theory (disable eapply-spec))))

(defthm alist-keys-esim-sexpr-fixpoint-nst
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (equal (alist-keys (esim-sexpr-fixpoint-nst mod))
                  (pat-flatten1 (mod-state mod))))
  :hints(("Goal" :expand ((esim-sexpr-fixpoint-nst mod))
          :in-theory (e/d (mod-state)
                          (good-esim-modulep occs-state)))))




(defthm alist-keys-esim-occ-nst
  (equal (alist-keys (esim-occ-nst occ fixpoint st))
         (pat-flatten1 (occ-state occ)))
  :hints (("goal" :expand ((esim-occ-nst occ fixpoint st))
           :in-theory (disable esim-nst))))

(defthm alist-keys-esim-occs-nst
  (equal (alist-keys (esim-occs-nst mod occs fixpoint st))
         (pat-flatten1 (occs-state (alist-vals (fal-extract occs (occmap mod))))))
  :hints (("goal" :in-theory (enable fal-extract
                                     occmap-when-no-occs)
           :induct (len occs))))

(defthm alist-keys-esim-nst
  (implies (good-esim-modulep mod)
           (equal (alist-keys (esim-nst mod ins st))
                  (pat-flatten1 (mod-state mod))))
  :hints (("goal" :expand ((esim-nst mod ins st))
           :in-theory (e/d (mod-state)
                           (occs-state esim-fixpoint eapply-spec)))))


(defcong 4v-sexpr-alist-equiv key-and-env-equiv (4v-sexpr-eval-alist x al) 1
  :hints (("goal" :in-theory (e/d (key-and-env-equiv)
                                  (4v-env-equiv-to-key-and-env-equiv)))))

(defthm 4v-sexpr-eval-of-esim-sexpr-nst-when-esim-correct-nst-modp1
  (implies (and (esim-sexpr-correct-nst-modp mod)
                (good-esim-modulep mod))
           (b* ((sexpr-nst (esim-sexpr-nst mod sig-al st-al))
                (spec-nst  (esim-nst mod
                                     (4v-sexpr-eval-alist sig-al env)
                                     (4v-sexpr-eval-alist st-al env))))
             (4v-env-equiv (4v-sexpr-eval-alist sexpr-nst env)
                           spec-nst)))
  :hints(("Goal" :in-theory
          (e/d (esim-nst-norm-appended-extracted-sts
                esim-nst-norm-appended-extracted-ins)
               (eapply-spec eapply-sexpr esim-sexpr-general-nst
                            esim-sexpr-general-out
                            esim-nst esim-out-in-terms-of-least-fixpoint
                            good-esim-modulep esim-sexpr-general-nst
                            4v-sexpr-eval 4v-lookup))
          :expand ((esim-sexpr-nst mod sig-al st-al))
          :use ((:instance esim-sexpr-correct-nst-modp-necc
                           (env (append (4v-alist-extract
                                         (pat-flatten1 (gpl :i mod))
                                         (4v-sexpr-eval-alist sig-al env))
                                        (4v-alist-extract
                                         (pat-flatten1 (mod-state mod))
                                         (4v-sexpr-eval-alist st-al env))))))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:in-theory (e/d (key-and-env-equiv)
                                (4v-env-equiv-to-key-and-env-equiv
                                 good-esim-modulep
                                 4v-sexpr-eval esim-nst))))))


(defthm alist-keys-esim-sexpr-general-nst
  (implies (good-esim-modulep mod)
           (equal (alist-keys (esim-sexpr-general-nst mod))
                  (pat-flatten1 (mod-state mod))))
  :hints(("Goal" :in-theory (disable eapply-sexpr)
          :expand ((esim-sexpr-general-nst mod)))))


(defthm 4v-sexpr-eval-of-esim-sexpr-general-nst
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-nst-modp mod))
           (b* ((sexpr-nst (esim-sexpr-general-nst mod))
                (spec-nst (esim-nst mod env env)))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints (("goal" :use
           ((:instance 4v-alistp-with-same-keys-equal
                       (a (4v-sexpr-eval-alist
                           (esim-sexpr-general-nst mod) env))
                       (b (esim-nst mod env env))))
           :in-theory (e/d (esim-sexpr-correct-nst-modp-implies)
                           (esim-sexpr-general-nst
                            4v-env-equiv-to-key-and-env-equiv
                            esim-nst)))))



(defthm 4v-sexpr-eval-alist-of-4v-sexpr-compose-with-rw-alist
  (equal (4v-sexpr-eval-alist (4v-sexpr-compose-with-rw-alist x al) env)
         (4v-sexpr-eval-alist (4v-sexpr-compose-alist x al) env))
  :hints(("Goal" :in-theory (disable 4v-sexpr-compose 4v-sexpr-compose-with-rw
                                     4v-sexpr-eval))))

(defthm 4v-sexpr-eval-alist-of-4v-sexpr-restrict-with-rw-alist
  (equal (4v-sexpr-eval-alist (4v-sexpr-restrict-with-rw-alist x al) env)
         (4v-sexpr-eval-alist (4v-sexpr-restrict-alist x al) env))
  :hints(("Goal" :in-theory (disable 4v-sexpr-restrict 4v-sexpr-restrict-with-rw
                                     4v-sexpr-eval))))


(defthm 4v-sexpr-eval-of-esim-sexpr-nst-when-esim-correct-nst-modp
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-nst-modp mod))
           (b* ((sexpr-nst (esim-sexpr-nst mod in st))
                (spec-nst (esim-nst mod
                                    (4v-sexpr-eval-alist in env)
                                    (4v-sexpr-eval-alist st env))))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints (("goal" :in-theory
          (e/d (esim-nst-norm-appended-extracted-sts
                esim-nst-norm-appended-extracted-ins)
               (eapply-spec eapply-sexpr esim-sexpr-general-nst
                            esim-sexpr-general-out
                            esim-nst esim-out-in-terms-of-least-fixpoint
                            good-esim-modulep esim-sexpr-general-nst
                            4v-sexpr-eval 4v-lookup))
          :use ((:instance 4v-alistp-with-same-keys-equal
                 (a (4V-ALIST-EXTRACT (PAT-FLATTEN1 (MOD-STATE MOD))
                                  (ESIM-NST MOD (4V-SEXPR-EVAL-ALIST IN ENV)
                                            (4V-SEXPR-EVAL-ALIST ST ENV))))
                 (b (ESIM-NST MOD (4V-SEXPR-EVAL-ALIST IN ENV)
                              (4V-SEXPR-EVAL-ALIST ST ENV)))))
          :expand ((esim-sexpr-nst mod in st)))))



(defthm 4v-sexpr-eval-of-esim-sexpr-occ-nst
  (implies (and (good-esim-occp occ)
                (esim-sexpr-correct-nst-modp (gpl :op occ)))
           (b* ((sexpr-nst (esim-sexpr-occ-nst occ))
                (spec-nst (esim-occ-nst occ env env)))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints(("Goal" :in-theory (e/d () (esim-sexpr-nst esim-nst))
          :expand ((esim-sexpr-occ-nst occ)
                   (esim-occ-nst occ env env)))))

(defun esim-sexpr-correct-nst-occsp (occs)
  (if (atom occs)
      t
    (and (esim-sexpr-correct-nst-modp (gpl :op (car occs)))
         (esim-sexpr-correct-nst-occsp (cdr occs)))))

(defthm esim-sexpr-occ-nst-of-nil
  (equal (esim-sexpr-occ-nst nil) nil)
  :hints (("goal" :expand ((esim-sexpr-occ-nst nil)
                           (:free (x) (sexpr-pat-alist-translate
                                       nil nil x nil)))
           :in-theory (disable (esim-sexpr-occ-nst)))))

(defthm 4v-sexpr-eval-of-esim-sexpr-occs-nst
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-nst-occsp
                 (alist-vals (fal-extract occs (occmap mod)))))
           (b* ((sexpr-nst (esim-sexpr-occs-nst mod occs))
                (spec-nst (esim-occs-nst mod occs env env)))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints(("Goal" :in-theory (e/d (fal-extract alist-vals)
                                 (esim-sexpr-occ-nst
                                  esim-occ-nst
                                  good-esim-modulep
                                  4v-sexpr-eval))
          :induct (len occs)
          :expand ((esim-occ-nst nil env env)
                   (esim-sexpr-occs-nst mod occs)))))

(defthm esim-sexpr-correct-nst-occsp-append
  (iff (esim-sexpr-correct-nst-occsp (append a b))
       (and (esim-sexpr-correct-nst-occsp a)
            (esim-sexpr-correct-nst-occsp b))))




(defthm good-esim-modulep-implies-no-dups-driven-signals
  (implies (good-esim-modulep mod)
           (no-duplicatesp-equal (driven-signals mod)))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))

(defthm good-esim-modulep-implies-driven-and-ins-not-intersecting
  (implies (good-esim-modulep mod)
           (not (intersectp-equal (pat-flatten1 (gpl :i mod))
                                  (driven-signals mod))))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))

(add-to-ruleset good-esim-mod-impl
                '(good-esim-modulep-implies-no-dups-driven-signals
                  good-esim-modulep-implies-driven-and-ins-not-intersecting))

(defthmd 4v-env-equiv-append-swap-when-not-intersecting-keys
  (implies (not (intersectp-equal (double-rewrite (alist-keys a))
                                  (double-rewrite (alist-keys b))))
           (4v-env-equiv (append b a)
                         (append a b)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                           (alist-keys-member-hons-assoc-equal 4v-fix)))
          (witness :ruleset 4v-env-equiv-witnessing)
          (set-reasoning)))

(defthm esim-sexpr-fixpoint-equals-esim-least-fixpoint
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (equal (append (4v-alist-extract
                                  (pat-flatten1 (gpl :i mod)) env)
                          (4v-alist-extract
                           (driven-signals mod)
                           (4v-sexpr-eval-alist
                            (esim-sexpr-fixpoint-out mod)
                            env)))
                  (esim-least-fixpoint
                   mod
                   (4v-alist-extract (pat-flatten1 (gpl :i mod)) env)
                   env)))
  :hints(("Goal" :in-theory
          (e/d (4v-env-equiv-append-swap-when-not-intersecting-keys)
               (4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                   good-esim-modulep
                   4v-env-equiv-to-key-and-env-equiv
                   esim-sexpr-correct-occsp
                   4v-sexpr-eval-alist
                   extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                   esim-fixpoint-p-occs-when-<=
                   esim-fixpoint-p
                   esim-sexpr-fixpoint-out
                   4v-alist-extract))
          :use ((:instance 4v-alistp-with-same-keys-equal
                           (a (append (4v-alist-extract
                                       (pat-flatten1 (gpl :i mod)) env)
                                      (4v-alist-extract
                                       (driven-signals mod)
                                       (4v-sexpr-eval-alist
                                        (esim-sexpr-fixpoint-out mod)
                                        env))))
                           (b (esim-least-fixpoint
                               mod
                               (4v-alist-extract (pat-flatten1 (gpl :i mod)) env)
                               env))))
          :do-not-induct t)))

(defthm esim-sexpr-fixpoint-gives-esim-least-fixpoint
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (esim-sexpr-correct-occsp (gpl :occs mod)))
           (4v-env-equiv (append (4v-sexpr-eval-alist
                                  (esim-sexpr-fixpoint-out mod)
                                  env)
                                 (4v-alist-extract
                                  (pat-flatten1 (gpl :i mod)) env))
                         (esim-least-fixpoint
                          mod
                          (4v-alist-extract (pat-flatten1 (gpl :i mod)) env)
                          env)))
  :hints(("Goal" :in-theory
          (e/d () (4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                   good-esim-modulep
                   esim-sexpr-correct-occsp
                   4v-sexpr-eval-alist
                   extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                   esim-fixpoint-p-occs-when-<=
                   esim-fixpoint-p
                   esim-sexpr-fixpoint-out
                   4v-alist-extract))
          :use ((:instance 4v-sexpr-least-fixpointp-implies-esim-least-fixpoint
                           (fixpoint (esim-sexpr-fixpoint-out mod))))
          :do-not-induct t)))


(defthm occ-inputs-subset-of-all-signals2
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (subsetp-equal
            (pat-flatten1 (gpl :i (cdr (hons-assoc-equal occ (occmap mod)))))
            (append (pat-flatten1 (gpl :i mod))
                    (collect-signal-list :o (gpl :occs mod)))))
  :hints (("goal" :in-theory (disable occ-inputs-subset-of-all-signals
                                      occ-inputs-subset-of-all-signals1
                                      good-esim-modulep)
           :use occ-inputs-subset-of-all-signals)))

(defthm good-esim-occp-similar-patterns
  (implies (good-esim-occp occ)
           (and (equal (similar-patternsp (gpl :i (gpl :op occ))
                                          (gpl :i occ))
                       t)
                (equal (similar-patternsp (gpl :o (gpl :op occ))
                                          (gpl :o occ))
                       t))))

(defthm esim-occ-nst-using-driven-signals-of-mod
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (equal (esim-occ-nst (esim-get-occ occ mod)
                                (4v-alist-extract
                                 (append (pat-flatten1 (gpl :i mod))
                                         (driven-signals mod))
                                 fixpoint)
                                st)
                  (esim-occ-nst (esim-get-occ occ mod) fixpoint st)))
  :hints (("goal" :in-theory (e/d ()
                                  (4v-alist-extract-append
                                   good-esim-modulep esim-nst))
           :expand ((:free (occ fixpoint nst)
                           (esim-occ-nst occ fixpoint nst))))))

(defthm good-esim-occsp-when-good-esim-modulep
  (implies (good-esim-modulep mod)
           (good-esim-occsp (gpl :occs mod))))

(defthm good-esim-modulep-impl-esim-sexpr-correct-occsp
  (implies (good-esim-modulep mod)
           (esim-sexpr-correct-occsp (gpl :occs mod))))


(defthm esim-occs-nst-using-driven-signals-of-mod
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (esim-occs-nst mod occs
                                 (4v-alist-extract
                                  (append (pat-flatten1 (gpl :i mod))
                                          (driven-signals mod))
                                  fixpoint)
                                 st)
                  (esim-occs-nst mod occs fixpoint st)))
  :hints(("Goal" :in-theory (e/d () (4v-alist-extract-append
                                     good-esim-modulep))
          :expand ((:free (fixpoint)
                          (esim-occs-nst mod occs fixpoint st)))
          :induct (len occs))))



(Defthmd esim-occs-nst-lemma1
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (esim-occs-nst mod (alist-keys (occmap mod))
                                 (append (4v-sexpr-eval-alist (esim-sexpr-fixpoint-out mod)
                                                              env)
                                         env)
                                 st)
                  (esim-occs-nst mod (alist-keys (occmap mod))
                                 (ESIM-LEAST-FIXPOINT
                                  MOD
                                  (4V-ALIST-EXTRACT (PAT-FLATTEN1 (GPL :I MOD))
                                                    ENV)
                                  ENV)
                                 st)))
  :hints (("goal" :use ((:instance esim-occs-nst-using-driven-signals-of-mod
                                   (fixpoint
                                    (append (4v-sexpr-eval-alist
                                             (esim-sexpr-fixpoint-out mod)
                                             env)
                                            env))
                                   (occs (alist-keys (occmap mod)))))
           :in-theory (disable good-esim-modulep
                               esim-occs-nst
                               esim-fixpoint
                               4v-env-equiv-implies-equal-esim-occs-nst-3
                               esim-occs-nst-using-driven-signals-of-mod
                               extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                               esim-fixpoint-equiv-when-mod-fixpoint
                               esim-fixpoint-p-occs-when-<=))))

(Defthmd esim-occs-nst-lemma2
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (esim-occs-nst mod (alist-keys (occmap mod))
                                 (append (4v-sexpr-eval-alist (esim-sexpr-fixpoint-out mod)
                                                              env)
                                         env)
                                 st)
                  (esim-occs-nst mod (alist-keys (occmap mod))
                                 (esim-fixpoint
                                  mod
                                  (4v-alist-extract
                                   (pat-flatten1 (gpl :i mod)) env)
                                  env)

                                 st)))
  :hints (("goal" :use ((:instance esim-occs-nst-using-driven-signals-of-mod
                                   (fixpoint
                                    (esim-fixpoint
                                     mod
                                     (4v-alist-extract
                                      (pat-flatten1 (gpl :i mod)) env)
                                     env))
                                   (occs (alist-keys (occmap mod)))))
           :in-theory (e/d (esim-occs-nst-lemma1)
                           (good-esim-modulep
                            esim-occs-nst
                            esim-fixpoint
                            esim-occs-nst-using-driven-signals-of-mod
                            esim-fixpoint-equiv-when-mod-fixpoint
                            esim-fixpoint-p-occs-when-<=)))))


;;; ESIM-OCC, ESIM-OCCS, ESIM-FIXPOINT when state alists agree

(defthmd esim-occ-when-st-alists-agree
  (implies (4v-alists-agree (pat-flatten1 (occ-state occ))
                            st-al1 st-al2)
           (equal (equal (esim-occ occ sig-al st-al1)
                         (esim-occ occ sig-al st-al2))
                  t))
  :hints (("goal" :expand ((:free (st-al) (esim-occ occ sig-al st-al)))
           :use ((:instance 4v-pat-alist-translate-when-4v-alists-agree-rw
                            (a (occ-state occ)) (b (mod-state (gpl :op occ)))
                            (al1 st-al1) (al2 st-al2)))
           :in-theory (disable esim-out occ-state
                               4v-pat-alist-translate-when-4v-alists-agree-rw))))

(defthmd esim-occs-when-st-alists-agree
  (implies (4v-alists-agree (pat-flatten1 (occs-state
                                           (alist-vals
                                            (fal-extract occs (occmap mod)))))
                            st-al1 st-al2)
           (equal (equal (esim-occs mod occs sig-al st-al1)
                         (esim-occs mod occs sig-al st-al2))
                  t))
  :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al1)
           :expand ((:free (st-al) (esim-occs mod occs sig-al st-al)))
           :in-theory (e/d (fal-extract) (esim-occ occ-state)))
          (and stable-under-simplificationp
               '(:use ((:instance esim-occ-when-st-alists-agree
                                  (occ (esim-get-occ (car occs) mod))))))))

(defthmd esim-fixpoint-when-st-alists-agree
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (4v-alists-agree (pat-flatten1 (mod-state mod))
                                 st-al1 st-al2))
           (equal (equal (esim-fixpoint mod sig-al st-al1)
                         (esim-fixpoint mod sig-al st-al2))
                  t))
  :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al1)
           :expand ((:free (st-al) (esim-fixpoint mod sig-al st-al)))
           :in-theory (e/d (mod-state)
                           (esim-occs good-esim-modulep
                                      esim-occs-equiv-when-mod-fixpoint
                                      esim-occs-equiv-when-fixpoint
                                      esim-wf-signals
                                      esim-fixpoint))
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:use ((:instance esim-occs-when-st-alists-agree
                                  (occs (alist-keys (occmap mod)))))))))





;;; ESIM-OCC-NST, ESIM-OCCS-NST when state alists agree

(defthmd esim-occ-nst-when-st-alists-agree
  (implies (4v-alists-agree (pat-flatten1 (occ-state occ))
                            st-al1 st-al2)
           (equal (equal (esim-occ-nst occ sig-al st-al1)
                         (esim-occ-nst occ sig-al st-al2))
                  t))
  :hints (("goal" :expand ((:free (st-al) (esim-occ-nst occ sig-al st-al)))
           :use ((:instance 4v-pat-alist-translate-when-4v-alists-agree-rw
                            (a (occ-state occ)) (b (mod-state (gpl :op occ)))
                            (al1 st-al1) (al2 st-al2)))
           :in-theory (disable esim-nst occ-state
                               4v-pat-alist-translate-when-4v-alists-agree-rw))))

(defthmd esim-occs-nst-when-st-alists-agree
  (implies (4v-alists-agree (pat-flatten1 (occs-state
                                           (alist-vals
                                            (fal-extract occs (occmap mod)))))
                            st-al1 st-al2)
           (equal (equal (esim-occs-nst mod occs sig-al st-al1)
                         (esim-occs-nst mod occs sig-al st-al2))
                  t))
  :hints (("goal" :induct (len occs)
           :expand ((:free (st-al) (esim-occs-nst mod occs sig-al st-al)))
           :in-theory (e/d (fal-extract) (esim-occ occ-state)))
          (and stable-under-simplificationp
               '(:use ((:instance esim-occ-nst-when-st-alists-agree
                                  (occ (esim-get-occ (car occs) mod))))))))

(defthmd esim-occs-nst-when-st-alists-agree-on-mod-state
  (implies (and (4v-alists-agree (pat-flatten1 (mod-state mod))
                                 st-al1 st-al2)
                (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (equal (esim-occs-nst mod (alist-keys (occmap mod)) sig-al st-al1)
                         (esim-occs-nst mod (alist-keys (occmap mod)) sig-al st-al2))
                  t))
  :hints (("goal" :use ((:instance esim-occs-nst-when-st-alists-agree
                                   (occs (alist-keys (occmap mod)))))
           :in-theory (e/d (mod-state) (esim-occs occs-state)))))







(defthm esim-fixpoint-extract-state
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (esim-fixpoint mod sig-al
                                 (4v-alist-extract
                                  (pat-flatten1 (mod-state mod))
                                  st-al))
                  (esim-fixpoint mod sig-al st-al)))
  :hints(("Goal" :in-theory (enable esim-fixpoint-when-st-alists-agree))))


(defthm esim-occs-nst-extract-state
  (implies (and (good-esim-modulep mod) (not (gpl :x mod)))
           (equal (esim-occs-nst mod (alist-keys (occmap mod))
                                 sig-al
                                 (4v-alist-extract
                                  (pat-flatten1 (mod-state mod))
                                  st-al))
                  (esim-occs-nst mod (alist-keys (occmap mod))
                                 sig-al st-al)))
  :hints (("goal" :use ((:instance
                         esim-occs-nst-when-st-alists-agree-on-mod-state
                         (st-al1 (4v-alist-extract
                                  (pat-flatten1 (mod-state mod))
                                  st-al))
                         (st-al2 st-al)))
           :in-theory (disable good-esim-modulep esim-occs-nst))))


(defthm 4v-alists-agree-append-first-when-first-not-intersecting
  (implies (not (intersectp-equal keys (alist-keys a)))
           (equal (4v-alists-agree keys (append a b) c)
                  (4v-alists-agree keys b c)))
  :hints(("Goal" :in-theory (disable 4vp 4v-fix 4v-alists-agree
                                     intersectp-equal)
          :expand ((:free (a b) (4v-alists-agree keys a b))
                   (intersectp-equal keys (alist-keys a)))
          :induct (len keys))))

(defthm state-not-intersecting-driven-when-good-esim-modulep
  (implies (good-esim-modulep mod)
           (not (intersectp-equal (pat-flatten1 (mod-state mod))
                                  (driven-signals mod))))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))

(defthm 4v-sexpr-eval-of-esim-sexpr-fixpoint-nst
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-nst-occsp (gpl :occs mod))
                (not (gpl :x mod)))
           (b* ((sexpr-nst (esim-sexpr-fixpoint-nst mod))
                (spec-nst (esim-nst mod env env)))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints(("Goal" :in-theory (e/d (esim-occs-nst-lemma2)
                                 (esim-sexpr-occs-nst
                                  ;; blah, need to disable append-of-nil, presumably
                                  ;; due to something above expecting it
                                  append-of-nil
                                  good-esim-modulep
                                  esim-occs-nst
                                  ; extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                                  esim-fixpoint-equiv-when-mod-fixpoint
                                  esim-fixpoint-p
                                  esim-fixpoint))
          :use ((:instance esim-occs-nst-when-st-alists-agree-on-mod-state
                           (sig-al (ESIM-FIXPOINT
                                    MOD
                                    (4V-ALIST-EXTRACT (PAT-FLATTEN1 (GPL :I MOD))
                                                      ENV)
                                    ENV))
                           (st-al1 (APPEND (4V-SEXPR-EVAL-ALIST
                                            (ESIM-SEXPR-FIXPOINT-OUT MOD) ENV)
                                           ENV))
                           (st-al2 env)))
          :expand ((esim-sexpr-fixpoint-nst mod)
                   (esim-sexpr-general-out mod)
                   (esim-nst mod env env)))))

(defthm 4v-sexpr-eval-of-eapply-sexpr-nst
  (equal (4v-sexpr-eval-alist (mv-nth 0 (eapply-sexpr x)) env)
         (mv-nth 0 (eapply-spec env x))))


(defthm 4v-sexpr-eval-of-esim-sexpr-general-nst-when-correct-occs
  (implies (and (good-esim-modulep mod)
                (esim-sexpr-correct-nst-occsp (gpl :occs mod)))
           (b* ((sexpr-nst (esim-sexpr-general-nst mod))
                (spec-nst (esim-nst mod env env)))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints(("Goal" :in-theory (e/d ()
                                 (esim-sexpr-fixpoint-nst
                                  good-esim-modulep
                                  eapply-sexpr eapply-spec
                                  ; extract-of-esim-fixpoint-equiv-esim-least-fixpoint
                                  esim-fixpoint-equiv-when-mod-fixpoint
                                  esim-fixpoint-p
                                  esim-fixpoint))
          :expand ((esim-sexpr-general-nst mod)))))

(defthm esim-sexpr-correct-nst-modp-when-esim-sexpr-correct-nst-occsp
  (implies (and (esim-sexpr-correct-nst-occsp (gpl :occs mod))
                (good-esim-modulep mod))
           (esim-sexpr-correct-nst-modp mod))
  :hints (("goal" :in-theory (e/d (esim-sexpr-correct-nst-modp)
                                  (good-esim-modulep
                                   esim-nst
                                   esim-sexpr-general-nst)))))

(defthm esim-sexpr-correct-nst-modp-when-no-occs
  (implies (and (gpl :x mod)
                (good-esim-modulep mod))
           (esim-sexpr-correct-nst-modp mod))
  :hints(("Goal" :in-theory (e/d (esim-sexpr-correct-nst-modp)
                                 (good-esim-modulep
                                  esim-sexpr-fixpoint-nst
                                  esim-fixpoint esim-occs-nst
                                  eapply-sexpr eapply-spec))
          :expand ((esim-sexpr-general-nst mod)))))


(defthm-mod-flag
  (defthm esim-sexpr-correct-nst-when-good-esim-modulep
    (implies (good-esim-modulep mod)
             (esim-sexpr-correct-nst-modp mod))
    :flag mod)
  (defthm esim-sexpr-correct-nst-occsp-when-good-esim-occsp
    (implies (good-esim-occsp occs)
             (esim-sexpr-correct-nst-occsp occs))
    :flag occs)
  (defthm esim-sexpr-correct-nst-occ-when-good-esim-occp
    (implies (good-esim-occp occ)
             (esim-sexpr-correct-nst-modp (gpl :op occ)))
    :flag occ)
  :hints(("Goal" :in-theory (disable good-esim-modulep
                                     good-esim-occp
                                     esim-sexpr-correct-nst-modp))))




(defthm 4v-sexpr-eval-of-esim-sexpr-nst
  (implies (good-esim-modulep mod)
           (b* ((sexpr-nst (esim-sexpr-nst mod in st))
                (spec-nst (esim-nst mod
                                    (4v-sexpr-eval-alist in env)
                                    (4v-sexpr-eval-alist st env))))
             (equal (4v-sexpr-eval-alist sexpr-nst env)
                    spec-nst)))
  :hints (("goal" :in-theory (disable esim-sexpr-nst esim-nst
                                      good-esim-modulep))))








(defun 4v-to-sexpr (x)
  (declare (xargs :guard t))
  (hons x nil))

(defthm 4v-to-sexpr-correct
  (equal (4v-sexpr-eval (4v-to-sexpr x) env)
         (4v-fix x)))

(in-theory (disable 4v-to-sexpr))

(defun 4v-to-sexpr-alist (x)
  (declare (xargs :Guard t))
  (if (atom x)
      nil
    (if (atom (car x))
        (4v-to-sexpr-alist (cdr x))
      (cons (cons (caar x) (4v-to-sexpr (cdar x)))
            (4v-to-sexpr-alist (cdr x))))))

(defthm lookup-in-4v-to-sexpr-alist
  (equal (hons-assoc-equal k (4v-to-sexpr-alist x))
         (and (hons-assoc-equal k x)
              (cons k (4v-to-sexpr (cdr (hons-assoc-equal k x)))))))

(defthm 4v-to-sexpr-alist-correct
  (4v-env-equiv (4v-sexpr-eval-alist (4v-to-sexpr-alist x) env)
                x)
  :hints (("goal" :in-theory (disable 4v-fix))
          (witness :ruleset 4v-env-equiv-witnessing)))

(defun esim (mod in st)
  (declare (xargs :guard (good-esim-modulep mod)
                  :verify-guards nil))
  (mbe :logic (mv (esim-nst mod in st)
                  (esim-out mod in st))
       :exec (b* ((ins (4v-to-sexpr-alist in))
                  (sts (4v-to-sexpr-alist st))
                  ((with-fast ins sts))
                  ((mv outs nsts) (esim-sexpr mod ins sts)))
               (mv (4v-sexpr-eval-alist outs nil)
                   (4v-sexpr-eval-alist nsts nil)))))

(verify-guards esim
  :hints (("goal" :in-theory (disable esim-nst esim-out
                                      esim-sexpr-out
                                      esim-out-in-terms-of-least-fixpoint
                                      esim-sexpr-nst))))




(defthm esim-sexpr-is-symbolic-version-of-esim
  (implies (good-esim-modulep mod)
           (b* ((sexpr-out (esim-sexpr-out mod in st))
                (sexpr-nst (esim-sexpr-nst mod in st))
                ((mv spec-nst spec-out)
                 (esim mod
                       (4v-sexpr-eval-alist in env)
                       (4v-sexpr-eval-alist st env))))
             (and (equal (4v-sexpr-eval-alist sexpr-out env)
                         spec-out)
                  (equal (4v-sexpr-eval-alist sexpr-nst env)
                         spec-nst))))
  :hints (("goal" :in-theory (disable esim-nst esim-out
                                      esim-sexpr-out
                                      esim-out-in-terms-of-least-fixpoint
                                      esim-sexpr-nst))))



