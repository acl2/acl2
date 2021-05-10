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
(include-book "fsm-obj")
(include-book "expand")
(include-book "../svex/monotonify")


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
          (svarlist-to-override-alist (cdr x)))))

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

(define svtv-compose-assigns/delays ((flatnorm flatnorm-res-p))
  :returns (fsm base-fsm-p)
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
  (b* (((flatnorm-res flatnorm))
       (override-alist (svarlist-to-override-alist (svex-alist-keys flatnorm.assigns)))
       (overridden-assigns (with-fast-alist override-alist
                             (svex-alist-compose flatnorm.assigns override-alist)))
       (updates1 (make-fast-alist
                  (with-fast-alist overridden-assigns
                    (svex-assigns-compose overridden-assigns :rewrite t))))
       (updates2 (svex-alist-compose override-alist updates1))
       (masks (svexlist-mask-alist (svex-alist-vals updates2)))
       (nextstates (with-fast-alist updates2 (svex-compose-delays flatnorm.delays updates2 masks))))
    (make-base-fsm :values updates1 :nextstate (fast-alist-clean nextstates)))
  ///
  (defret no-duplicate-nextstates-of-<fn>
    (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate fsm)))))


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



  
