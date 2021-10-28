; Centaur SV Hardware Verification
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

(include-book "../mods/compile")
(include-book "fsm-base")
(include-book "expand")
(include-book "../svex/monotonify")

(local (include-book "std/lists/sets" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define svarlist-to-override-alist ((x svarlist-p))
  :returns (alist svex-alist-p)
  (if (atom x)
      nil
    (cons (b* ((x1 (car x)))
            (cons (svar-fix x1)
                  (svcall bit?!
                          (svex-var (change-svar x1 :override-test t))
                          (svex-var (change-svar x1 :override-val t))
                          (svex-var x1))))
          (svarlist-to-override-alist (cdr x))))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys alist)
           (svarlist-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-keys)))))

(define svtv-wires->lhses! ((x string-listp)
                            (modidx natp)
                            (moddb moddb-ok)
                            aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs (lhses lhslist-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv err lhs) (svtv-wire->lhs! (car x) modidx moddb aliases))
       ((mv errs lhses) (svtv-wires->lhses! (cdr x) modidx moddb aliases)))
    (mv (append-without-guard err errs) (cons lhs lhses))))
    


(local (include-book "std/osets/element-list" :dir :system))
(local (deflist svarlist
         :elt-type svar
         :true-listp t
         :elementp-of-nil nil))

(defprod flatten-res
  ((assigns assigns)
   (fixups assigns)
   (constraints constraintlist)
   (var-decl-map var-decl-map-p)))

(defprod flatnorm-res
  ((assigns svex-alist)
   (delays svar-map)
   (constraints constraintlist)))

(define flatten-res-vars ((x flatten-res-p))
  (b* (((flatten-res x)))
    (append (assigns-vars x.assigns)
            (assigns-vars x.fixups)
            (constraintlist-vars x.constraints))))


;; simple wrapper for svex-design-flatten that wraps the result into a flatten-res
(define svtv-design-flatten ((x design-p)
                             &key
                             ((moddb "overwritten") 'moddb)
                             ((aliases "overwritten") 'aliases))
  :guard (svarlist-addr-p (modalist-vars (design->modalist x)))
  :returns (mv err
               (res flatten-res-p)
               new-moddb new-aliases)
  :guard-hints (("goal" :in-theory (enable modscope-okp modscope-local-bound modscope->modidx)))
  (b* (((mv err assigns fixups constraints moddb aliases) (svex-design-flatten x))
       ((mv aliases var-decl-map)
        (if err
            (mv aliases nil)
          (time$ (aliases-indexed->named aliases (make-modscope-top
                                                  :modidx (moddb-modname-get-index
                                                           (design->top x) moddb))
                                         moddb)
                 :msg "; aliases renamed: ~st sec, ~sa bytes.~%"))))
    (mv err
        (make-flatten-res :assigns assigns :fixups fixups :constraints constraints
                          :var-decl-map var-decl-map)
        moddb aliases))
  ///
  (defretd normalize-stobjs-of-<fn>
    (implies (syntaxp (not (and (equal aliases ''nil)
                                (equal moddb ''nil))))
             (equal <call>
                    (let ((moddb nil) (aliases nil)) <call>)))
    :hints(("Goal" :in-theory (enable normalize-stobjs-of-svex-design-flatten))))

  (defret moddb-okp-of-<fn>
    (implies (not err)
             (and (moddb-mods-ok new-moddb)
                  (moddb-basics-ok new-moddb))))

  (defret modname-of-<fn>
    (implies (not err)
             (moddb-modname-get-index (design->top x) new-moddb)))

  ;; (defret modidx-of-<fn>
  ;;   (implies (not err)
  ;;            (< (moddb-modname-get-index (design->top x) new-moddb)
  ;;               (nfix (nth *moddb->nmods1* new-moddb))))
  ;;   :rule-classes :linear)

  (defret totalwires-of-<fn>
    (implies (not err)
             (<= (moddb-mod-totalwires
                  (moddb-modname-get-index (design->top x) new-moddb) new-moddb)
                 (len new-aliases)))
    :rule-classes :linear))


(defprod flatnorm-setup
  ((monotonify booleanp)))

(define svtv-normalize-assigns ((flatten flatten-res-p) aliases
                                (setup flatnorm-setup-p))
  :returns (res flatnorm-res-p)
  :guard (svarlist-boundedp (flatten-res-vars flatten) (aliass-length aliases))
  :guard-hints (("goal" :in-theory (enable flatten-res-vars)))
  (b* (((flatten-res flatten))
       ((mv assigns delays constraints)
        (svex-normalize-assigns flatten.assigns flatten.fixups flatten.constraints flatten.var-decl-map aliases))
       ((flatnorm-setup setup))
       (assigns (if setup.monotonify
                    (pairlis$ (svex-alist-keys assigns)
                              (time$ (svexlist-monotonify (svex-alist-vals assigns))
                                     :msg "; svexlist-monotonify: ~st sec (~sa bytes)~%"))
                  assigns)))
    (make-flatnorm-res :assigns assigns :delays delays :constraints constraints)))

(local
 (defsection no-duplicate-svex-alist-keys-of-fast-alist-clean
   (local (include-book "std/alists/fast-alist-clean" :dir :system))
   (defthm svex-alist-p-of-fast-alist-fork
     (implies (and (svex-alist-p x)
                   (svex-alist-p y))
              (svex-alist-p (fast-alist-fork x y))))
   (defthm cdr-last-of-svex-alist-p
     (implies (svex-alist-p x)
              (equal (cdr (last x)) nil)))
   (defthm svex-alist-p-of-fast-alist-clean
     (implies (svex-alist-p x)
              (svex-alist-p (fast-alist-clean x))))

   (defthm no-duplicate-svex-alist-keys-of-fast-alist-fork
     (implies  (no-duplicatesp-equal (svex-alist-keys y))
               (no-duplicatesp-equal (svex-alist-keys (fast-alist-fork x y))))
     :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup))))
   (defthm svex-alist-keys-of-cdr-last
     (equal (svex-alist-keys (cdr (last x))) nil)
     :hints(("Goal" :in-theory (enable svex-alist-keys))))
   (defthm no-duplicate-svex-alist-keys-of-fast-alist-clean
     (no-duplicatesp-equal (svex-alist-keys (fast-alist-clean x)))
     :hints(("Goal" :in-theory (enable svex-alist-keys))))

   (defthm svar-map-p-of-fast-alist-fork
     (implies (and (svar-map-p x)
                   (svar-map-p y))
              (svar-map-p (fast-alist-fork x y))))
   (defthm svar-map-p-of-fast-alist-clean
     (implies (svar-map-p x)
              (svar-map-p (fast-alist-clean x)))
     :hints(("Goal" :in-theory (enable fast-alist-clean))))

   (defthm no-duplicate-keys-of-fast-alist-fork
     (implies (no-duplicatesp-equal (alist-keys y))
              (no-duplicatesp-equal (alist-keys (fast-alist-fork x y)))))

   (defthm no-duplicate-keys-of-fast-alist-clean
     (no-duplicatesp-equal (alist-keys (fast-alist-clean x))))

   (in-theory (disable fast-alist-clean))))

(deftagsum svtv-assigns-override-config
  (:omit ((vars svarlist-p)))
  (:include ((vars svarlist-p)))
  :layout :list)


(local (defthm subsetp-intersection
         (subsetp-equal (intersection-equal a b) a)))

(local (defthm subsetp-set-diff
         (subsetp-equal (set-difference-equal a b) a)))

(define svtv-assigns-override-vars ((assigns svex-alist-p)
                                    (config svtv-assigns-override-config-p))
  :returns (override-vars svarlist-p)
  (svtv-assigns-override-config-case config
    :omit (acl2::hons-set-diff (svex-alist-keys assigns) config.vars)
    :include (acl2::hons-intersection (svex-alist-keys assigns) config.vars))
  ///
  (defret <fn>-subset-of-keys
    (subsetp-equal override-vars (svex-alist-keys assigns))))

(define svtv-delay-alist ((x svar-map-p)
                          (internal-signals svarlist-p)
                          (masks svex-mask-alist-p))
  ;; Converts an alist mapping delayed vars to undelayed vars (or more
  ;; generally, delay-n+1 to delay-n vars) into an svex-alist where the bound
  ;; value of each delayed variable is either (1) the corresponding undelayed
  ;; variable, if it is an internal signal bound in the given alist or (2) the
  ;; masked value of the undelayed variable, if not (for the case in which the
  ;; variable is a primary input).
  :returns (xx svex-alist-p)
  :measure (len (svar-map-fix x))
  (b* ((x (svar-map-fix x))
       ((when (atom x)) nil)
       ((cons key val) (car x))
       ((when (member-equal (svar-fix val) (svarlist-fix internal-signals)))
        (cons (cons key (svex-var val))
              (svtv-delay-alist (cdr x) internal-signals masks)))
       (mask (svex-mask-lookup (svex-var key) masks)))
    (cons (cons key
                (svcall bit?
                        (svex-quote (2vec (sparseint-val mask)))
                        (svex-var val)
                        (svex-quote (2vec 0))))
          (svtv-delay-alist (cdr x) internal-signals masks)))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys xx)
           (alist-keys (svar-map-fix x)))
    :hints(("Goal" :in-theory (enable alist-keys svar-map-fix svex-alist-keys))))

  (defcong set-equiv equal (svtv-delay-alist x internal-signals masks) 2))
       

(defprod phase-fsm-config
  ((override-config svtv-assigns-override-config-p))
  :layout :list)

(local (defthm svex-alist-keys-of-svex-alist-compose
         (Equal (svex-alist-keys (svex-alist-compose x a))
                (svex-alist-keys x))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))

(define svtv-flatnorm-apply-overrides ((flatnorm flatnorm-res-p)
                                       (config svtv-assigns-override-config-p))
  :returns (mv (assign-alist svex-alist-p)
               (delay-alist svex-alist-p))
  (b* (((flatnorm-res flatnorm))
       (override-alist (svarlist-to-override-alist
                        (svtv-assigns-override-vars flatnorm.assigns config)))
       ((acl2::with-fast override-alist))
       (overridden-assigns (svex-alist-compose flatnorm.assigns override-alist))
       (masks (svexlist-mask-alist (svex-alist-vals flatnorm.assigns)))
       (overridden-delays (svex-alist-compose (svtv-delay-alist (fast-alist-clean flatnorm.delays)
                                                                (svex-alist-keys flatnorm.assigns) masks)
                                              override-alist)))
    (mv overridden-assigns overridden-delays))
  ///
  (defret svex-alist-keys-of-<fn>-assigns
    (equal (svex-alist-keys assign-alist)
           (svex-alist-keys (flatnorm-res->assigns flatnorm))))

  (defret svex-alist-keys-of-<fn>-delays
    (equal (svex-alist-keys delay-alist)
           (alist-keys (fast-alist-clean (flatnorm-res->delays flatnorm))))))

(local (defthm append-subset-under-set-equiv
           (implies (subsetp a b)
                    (set-equiv (append b a) b))))

(local (defcong svex-alist-eval-equiv svex-alist-eval-equiv! (svex-alist-compose a b) 2
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv!)))))

(define phase-fsm-composition-p ((phase-fsm base-fsm-p)
                                 (flatnorm flatnorm-res-p)
                                 (config phase-fsm-config-p))
  (b* (((phase-fsm-config config))
       ((mv overridden-assigns overridden-delays)
        (svtv-flatnorm-apply-overrides flatnorm config.override-config))
       ((base-fsm phase-fsm)))
    (and (ec-call (netevalcomp-p phase-fsm.values overridden-assigns))
         ;; Need this because if we have signals that are in the
         ;; original assigns (therefore in the overridden assigns)
         ;; but not in the updates, then a delayed version of such a
         ;; signal would be bound to the signal itself in the
         ;; nextstates, effectively creating a new primary input. It
         ;; is always OK to bind unneeded signals to X in the
         ;; updates.
         (set-equiv (svex-alist-keys phase-fsm.values) (svex-alist-keys overridden-assigns))
         ;; Eventually weaken this to allow for sequential
         ;; equivalence under some initial state/initial primary
         ;; input assumption.
         (ec-call
          (svex-alist-eval-equiv! phase-fsm.nextstate
                                  (svex-alist-compose overridden-delays phase-fsm.values)))))
  ///
  (defcong base-fsm-eval-equiv equal (phase-fsm-composition-p phase-fsm flatnorm config) 1
    :hints(("Goal" :in-theory (enable base-fsm-eval-equiv))))

  (defcong flatnorm-res-equiv equal (phase-fsm-composition-p phase-fsm flatnorm config) 2)

  (defthm phase-fsm-composition-p-implies-no-duplicate-nextstate-keys
    (implies (phase-fsm-composition-p phase-fsm flatnorm config)
             (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate phase-fsm))))))





(local
 (defthm svex-compose-delays-in-terms-of-svtv-delay-alist
   (equal (svex-compose-delays delays updates masks)
          (svex-alist-compose
           (svtv-delay-alist delays (svex-alist-keys updates) masks)
           updates))
   :hints(("Goal" :in-theory (enable svex-compose-delays
                                     svtv-delay-alist
                                     svex-alist-compose
                                     svex-acons
                                     svex-compose
                                     svexlist-compose)))))

(local
 (defthm svex-alist-compose-of-svex-alist-compose
   (svex-alist-eval-equiv!
    (svex-alist-compose (svex-alist-compose a b) c)
    (svex-alist-compose a (append (svex-alist-compose b c) c)))
   :hints(("Goal" :in-theory (enable svex-alist-eval-equiv!
                                     svex-eval-equiv)))))

(define svtv-compose-assigns/delays ((flatnorm flatnorm-res-p)
                                     (config phase-fsm-config-p))
  :returns (fsm base-fsm-p)
  (b* (((flatnorm-res flatnorm))
       ((phase-fsm-config config))
       (override-alist (svarlist-to-override-alist
                        (svtv-assigns-override-vars flatnorm.assigns config.override-config)))
       (overridden-assigns (with-fast-alist override-alist
                             (svex-alist-compose flatnorm.assigns override-alist)))
       (updates1 (make-fast-alist
                  (with-fast-alist overridden-assigns
                    (svex-assigns-compose overridden-assigns :rewrite t))))
       (updates2 (fast-alist-fork updates1 (make-fast-alist (svex-alist-compose override-alist updates1))))
       (masks (svexlist-mask-alist (svex-alist-vals flatnorm.assigns)))
       (nextstates (svex-compose-delays (fast-alist-clean flatnorm.delays) updates2 masks)))
    (fast-alist-free updates2)
    (make-base-fsm :values updates1 :nextstate nextstates))
  ///
  (defret no-duplicate-nextstates-of-<fn>
    (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate fsm))))

  (local (defthmd svex-alist-keys-when-svex-alist-p
           (implies (svex-alist-p x)
                    (equal (svex-alist-keys x)
                           (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-alist-p svex-alist-keys alist-keys)))))

  (local (defthmd hons-assoc-equal-iff-member-alist-keys
           (iff (hons-assoc-equal k a)
                (member-equal k (alist-keys a)))
           :hints(("Goal" :in-theory (enable alist-keys hons-assoc-equal)))))

  (local (defthm svex-alist-keys-of-fast-alist-fork-under-set-equiv
           (implies (and (svex-alist-p b)
                         (svex-alist-p a))
                    (set-equiv (svex-alist-keys (fast-alist-fork a b))
                               (append (svex-alist-keys a) (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-alist-keys
                                           alist-keys
                                           svex-alist-keys-when-svex-alist-p
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (member-svex-alist-keys))))))
  
  

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append a b))
                  (or (hons-assoc-equal k a)
                      (hons-assoc-equal k b)))))

  (local (defthm hons-assoc-equal-of-fast-alist-fork
           (Equal (hons-assoc-equal k (fast-alist-fork a b))
                  (hons-assoc-equal k (append b a)))
           :hints(("Goal" :in-theory (enable fast-alist-fork)
                   :induct (fast-alist-fork a b)))))

  (local (defthm cdr-hons-assoc-equal-when-svex-alist-p
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))))

  (local (Defthm fast-alist-fork-under-svex-alist-eval-equiv
           (implies (and (Svex-alist-p x)
                         (svex-alist-p y))
                    (svex-alist-eval-equiv (fast-alist-fork x y)
                                           (Append y x)))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup)
                   :do-not-induct t))))

  (defret phase-fsm-composition-p-of-<fn>
    (phase-fsm-composition-p fsm flatnorm config)
    :hints (("goal" 
             :in-theory (enable svtv-flatnorm-apply-overrides
                                phase-fsm-composition-p
                                base-fsm-eval-equiv)))))


;; BOZO this could probably be broken into a few parts.
(define svtv-design-to-fsm ((x design-p)
                            &key
                            ((moddb "overwritten") 'moddb)
                            ((aliases "overwritten") 'aliases)
                            (override-all 't)
                            ((overrides string-listp) 'nil)
                            (rewrite 't))
  :prepwork ((local (include-book "std/alists/fast-alist-clean" :dir :system))
             (local (defthm svex-alist-p-of-fast-alist-fork
                      (implies (and (svex-alist-p x)
                                    (svex-alist-p y))
                               (svex-alist-p (fast-alist-fork x y)))))
             (local (defthm cdr-last-of-svex-alist-p
                      (implies (svex-alist-p x)
                               (equal (cdr (last x)) nil))))
             (local (defthm svex-alist-p-of-fast-alist-clean
                      (implies (svex-alist-p x)
                               (svex-alist-p (fast-alist-clean x)))))

             (local (defthm no-duplicate-svex-alist-keys-of-fast-alist-fork
                      (implies  (no-duplicatesp-equal (svex-alist-keys y))
                                (no-duplicatesp-equal (svex-alist-keys (fast-alist-fork x y))))
                      :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup)))))
             (local (defthm svex-alist-keys-of-cdr-last
                      (equal (svex-alist-keys (cdr (last x))) nil)
                      :hints(("Goal" :in-theory (enable svex-alist-keys)))))
             (local (defthm no-duplicate-svex-alist-keys-of-fast-alist-clean
                      (no-duplicatesp-equal (svex-alist-keys (fast-alist-clean x)))
                      :hints(("Goal" :in-theory (enable svex-alist-keys)))))
             (local (in-theory (disable fast-alist-clean))))
  
  :returns (mv err
               (fsm (implies (not err)
                             (base-fsm-p fsm)))
               (new-moddb moddb-basics-ok) new-aliases)
  :guard (modalist-addr-p (design->modalist x))
  (b* (((mv err assigns delays & moddb aliases)
        (svex-design-flatten-and-normalize x))
       ((when err)
        (mv err nil moddb aliases))
       (modidx (moddb-modname-get-index (design->top x) moddb))
       ((mv err override-vars)
        (if override-all
            (mv nil (svex-alist-keys assigns))
          (b* (((mv errs lhses) (svtv-wires->lhses! overrides modidx moddb aliases))
               ((when errs)
                (mv (msg-list errs) nil)))
            (mv nil (set::intersect (set::mergesort (svex-alist-keys assigns))
                                    (set::mergesort (lhslist-vars lhses)))))))
       ((when err)
        (mv err nil moddb aliases))
       (override-alist (svarlist-to-override-alist override-vars))
       (overridden-assigns (with-fast-alist override-alist
                             (svex-alist-compose assigns override-alist)))
       (updates1 (make-fast-alist
                  (with-fast-alist overridden-assigns
                    (svex-assigns-compose overridden-assigns :rewrite rewrite))))
       (updates2 (svex-alist-compose override-alist updates1))
       (masks (svexlist-mask-alist (svex-alist-vals updates2)))
       (nextstates (with-fast-alist updates2 (svex-compose-delays delays updates2 masks))))
    (mv nil
        (make-base-fsm :values updates1
                       :nextstate (fast-alist-clean nextstates))
        moddb aliases))
  ///
  (defret no-duplicate-nextstates-of-<fn>
    (implies (not err)
             (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate fsm)))))

  (defret <fn>-normalize-stobjs
    (implies (syntaxp (and (not (equal moddb ''nil))
                           (not (equal aliases ''nil))))
             (equal <call>
                    (let ((moddb nil) (aliases nil)) <call>)))
    :hints(("Goal" :in-theory (enable normalize-stobjs-of-svex-design-flatten-and-normalize))))

  (defret moddb-mods-ok-of-<fn>
    (moddb-mods-ok new-moddb))

  (defret alias-length-of-<fn>
    (implies (not err)
             (equal (len new-aliases)
                    (moddb-mod-totalwires
                     (moddb-modname-get-index (design->top x) new-moddb)
                     new-moddb))))

  (defret modidx-of-<fn>
    (implies (not err)
             (moddb-modname-get-index (design->top x) new-moddb))
    :rule-classes (:rewrite
                   (:type-prescription :corollary
                    (implies (not err)
                             (natp (moddb-modname-get-index (design->top x) new-moddb)))))))
