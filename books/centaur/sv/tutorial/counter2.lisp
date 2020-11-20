; Centaur SV Hardware Verification Tutorial
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

(include-book "../svtv/assign")
(include-book "../svtv/design-fsm")
(include-book "../mods/top")
(include-book "../vl/top")
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "../svtv/expand")
(include-book "centaur/fgl/top" :dir :system)
(include-book "centaur/ipasir/ipasir-backend" :dir :system)
(include-book "oslib/ls" :dir :system)

(include-book "tools/plev-ccl" :dir :system)

(local (in-theory (disable (tau-system))))
; (depends-on "counter.sv")
; cert_param: (hons-only)
; cert_param: (uses-glucose)

(value-triple (acl2::tshell-ensure))

(make-event

; Disabling waterfall parallelism for unknown reasons other than that
; certification stalls out with it enabled.

 (if (and (acl2::hons-enabledp state)
          (f-get-global 'acl2::parallel-execution-enabled state))
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))


(defconsts (*silly* state)
  (b* (((mv loadres state)
        (vl::vl-load (vl::make-vl-loadconfig
                      :start-files (list "silly.sv"))))
       (design (vl::vl-loadresult->design loadres))
       ((mv ?err svdesign ?good ?bad)
        (vl::cwtime (vl::vl-design->svex-design "silly" design (vl::make-vl-simpconfig)))))
    (and err
         (er hard? 'silly "Error: ~@0~%Warnings: ~s1~%" err
             (vl::vl-reportcard-to-string (vl::vl-design-reportcard bad))))
    (mv svdesign state)))



(defconsts (& *fsm0* moddb aliases) (svtv-design-to-fsm *silly*))




(defconsts (& *fsm*) (svtv-fsm-add-names
                      '((clk . "clk")
                        (longpart . "inc.longpart")
                        (shortpart . "inc.shortpart")
                        (incr . "incr")
                        (count . "count"))
                      *fsm0*))

(define svarlist-keep-override-tests ((x svarlist-p))
  :returns (overrides svarlist-p)
  (if (atom x)
      nil
    (if (svar->override-test (car x))
        (cons (svar-fix (car x))
              (svarlist-keep-override-tests (cdr x)))
      (svarlist-keep-override-tests (cdr x))))
  ///
  (local (defthm member-of-nil
           (not (member k nil))))
  (defret member-of-svarlist-keep-override-tests
    (iff (member k overrides)
         (and (svar-p k)
              (svar->override-test k)
              (member k (svarlist-fix x))))
    :hints(("Goal" :in-theory (disable member-equal
                                       acl2::member-when-atom
                                       acl2::subsetp-member)
            :induct t
            :expand ((svarlist-fix x))))))


(define svarlist-all-bound-to-x ((keys svarlist-p) (env svex-env-p))
  (if (atom keys)
      t
    (and (equal (svex-env-lookup (car keys) env) (4vec-x))
         (svarlist-all-bound-to-x (cdr keys) env)))
  ///
  (defthmd lookup-when-svarlist-all-bound-to-x
    (implies (and (svarlist-all-bound-to-x keys env)
                  (member (svar-fix key) (svarlist-fix keys)))
             (equal (svex-env-lookup key env) (4vec-x)))))

(define svex-env-overrides-all-x ((env svex-env-p))
  :prepwork ((local (defthm alist-keys-when-svex-env-p
                      (implies (svex-env-p x)
                               (svarlist-p (alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys))))))
  (svarlist-all-bound-to-x
   (svarlist-keep-override-tests (alist-keys (svex-env-fix env)))
   env)
  ///
  (local (defthm svex-env-lookup-when-not-hons-assoc-equal
           (implies (not (hons-assoc-equal (svar-fix k) env))
                    (equal (svex-env-lookup k env) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  (defthmd lookup-when-svex-env-overrides-all-x
    (implies (and (svex-env-overrides-all-x env)
                  (svar->override-test k))
             (equal (svex-env-lookup k env) (4vec-x)))
    :hints(("Goal" :in-theory (enable lookup-when-svarlist-all-bound-to-x)
            :cases ((member (svar-fix k) (alist-keys (svex-env-fix env))))))))

(define svex-env-overrides-all-x-except ((exceptions svarlist-p)
                                         (env svex-env-p))
  :prepwork ((local (defthm alist-keys-when-svex-env-p
                      (implies (svex-env-p x)
                               (svarlist-p (alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys))))))
  (svarlist-all-bound-to-x
   (set-difference-equal
    (svarlist-keep-override-tests (alist-keys (svex-env-fix env)))
    (svarlist-fix exceptions))
   env)
  ///
  (local (defthm svex-env-lookup-when-not-hons-assoc-equal
           (implies (not (hons-assoc-equal (svar-fix k) env))
                    (equal (svex-env-lookup k env) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  (defthmd lookup-when-svex-env-overrides-all-x-except
    (implies (and (svex-env-overrides-all-x-except exceptions env)
                  (svar->override-test k)
                  (not (member-equal (svar-fix k) (svarlist-fix exceptions))))
             (equal (svex-env-lookup k env) (4vec-x)))
    :hints(("Goal" :in-theory (enable lookup-when-svarlist-all-bound-to-x)
            :cases ((member (svar-fix k) (alist-keys (svex-env-fix env)))))))

  (fgl::disable-definition svex-env-overrides-all-x-except)
  (fgl::add-fgl-rewrite lookup-when-svex-env-overrides-all-x-except))
             






(defconsts (*flatten-err* *assigns* *delays* & moddb aliases)
  (svex-design-flatten-and-normalize *silly*))

;; (define svarlist-nonoverriddes-p ((x svarlist-p))
;;   (b* (((when (atom x)) t)
;;        ((svar x1) (car x)))
;;     (and (not x1.override-test)
;;          (not x1.override-val)
;;          (svarlist-nonoverriddes-p (cdr x)))))

(define svarlist-to-override-alist ((x svarlist-p))
  (if (atom x)
      nil
    (cons (b* ((x1 (car x)))
            (cons (svar-fix x1)
                  (svcall bit?!
                          (svex-var (change-svar x1 :override-test t))
                          (svex-var (change-svar x1 :override-val t))
                          (svex-var x1))))
          (svarlist-to-override-alist (cdr x)))))
                                    

(defconsts *overridde-alist* (make-fast-alist (svarlist-to-override-alist
                                               (svex-alist-keys *assigns*))))

(defconsts (*updates* *nextstates*)
  (b* ((overridden-assigns (svex-alist-compose *assigns* *overridde-alist*))
       (updates (make-fast-alist (with-fast-alist overridden-assigns (svex-assigns-compose overridden-assigns :rewrite t))))
       (updates1 (svex-alist-compose *overridde-alist* updates))
       (masks (svexlist-mask-alist (svex-alist-vals updates1)))
       (nextstates (with-fast-alist updates1 (svex-compose-delays *delays* updates1 masks))))
    (mv updates nextstates)))





(defconsts *modidx* (moddb-modname-get-index (design->top *silly*) moddb))

(defconsts *input-lhsmap*
  (b* (((mv errs lhsmap)
        (svtv-namemap->lhsmap '((clk . "clk")
                                (fact1 . "inc.fact1")
                                (fact2 . "inc.fact2[1:0]")
                                (incr . "incr"))
                              *modidx* moddb aliases))
       ((when errs)
        (er hard? 'lhsmap "Errors: ~@0~%" (msg-list errs))))
    lhsmap))

(defconsts *output-lhsmap*
  (b* (((mv errs lhsmap)
        (svtv-namemap->lhsmap '((count . "count"))
                              *modidx* moddb aliases))
       ((when errs)
        (er hard? 'lhsmap "Errors: ~@0~%" (msg-list errs))))
    lhsmap))





(define lhs-value-to-svtv-assigns ((lhs lhs-p)
                                   (val svex-p)
                                   (updates svex-alist-p))
  :returns (assigns assigns-p)
  (b* (((when (atom lhs))
        nil)
       ((lhrange x) (lhrange-fix (car lhs))))
    (lhatom-case x.atom
      :z (lhs-value-to-svtv-assigns (cdr lhs)
                                    (svex-rsh x.w val)
                                    updates)
      :var (b* ((overridep (svex-lookup x.atom.name updates))
                ((unless overridep)
                 (cons (cons (list x)
                             (make-driver :value val))
                       (lhs-value-to-svtv-assigns (cdr lhs)
                                                  (svex-rsh x.w val)
                                                  updates))))
             (cons (cons (list (change-lhrange
                                x
                                :atom (change-lhatom-var
                                       x.atom
                                       :name (change-svar x.atom.name :override-test t))))
                         (make-driver :value -1))
                   (cons (cons (list (change-lhrange
                                      x
                                      :atom (change-lhatom-var
                                             x.atom
                                             :name (change-svar x.atom.name :override-val t))))
                               (make-driver :value val))
                         (lhs-value-to-svtv-assigns (cdr lhs)
                                                  (svex-rsh x.w val)
                                                  updates)))))))



       
    

(define svtv-input-assigns ((lhsmap svtv-name-lhs-map-p)
                            (updates svex-alist-p))
  :returns (assigns assigns-p)
  (b* (((when (atom lhsmap))
        nil)
       ((unless (mbt (and (consp (car lhsmap))
                          (svar-p (caar lhsmap)))))
        (svtv-input-assigns (cdr lhsmap) updates))
       ((cons var lhs) (car lhsmap))
       (pairs (lhs-value-to-svtv-assigns lhs (svex-var var) updates)))
    (append pairs
            (svtv-input-assigns (cdr lhsmap) updates))))

(define svtv-input-alist ((lhsmap svtv-name-lhs-map-p
                                  "Input signal map, produced by svtv-namemap->lhsmap")
                          (updates svex-alist-p))
  :parents (svtv-steps)
  :short "Compose the updates/nextstates with this alist in order to get the
formulas in terms of a set of input signals."
  :returns (alist svex-alist-p)
  (b* ((assigns (svtv-input-assigns lhsmap updates))
       (netassigns (assigns->netassigns assigns))
       (res-assigns (netassigns->resolves netassigns)))
    res-assigns))


(define svtv-output-alist ((lhsmap svtv-name-lhs-map-p))
  :parents (svtv-steps)
  :short "Compose this alist with the updates in order to get formulas for the
given outputs."
  :returns (alist svex-alist-p)
  (b* (((when (atom lhsmap)) nil)
       ((unless (mbt (and (consp (car lhsmap))
                          (svar-p (caar lhsmap)))))
        (svtv-output-alist (cdr lhsmap))))
    (cons (cons (caar lhsmap)
                (lhs->svex (cdar lhsmap)))
          (svtv-output-alist (cdr lhsmap)))))


;; When composing a set of 0-delay updates and nextstates into a clock cycle,
;; we might have a few different goals.

;; Inputs:
;; 1. We might want to keep the inputs as free as possible, only assigning (say) a
;;    fixed value to the clock.  Other input signals would then have two
;;    variants, one for each phase.

;; 2. We might want to fix the phase in which inputs are accepted.  E.g., we
;;    might pass all Xes for the non-clock inputs in the clock-high phase,
;;    where they shouldn't matter (for strictly flop-based logic), and use the
;;    original input variables to stand for their values in the clock-0 phase.
;;    Or alternatively we might use the original input variables to stand for
;;    their values during both phases.

;; 3. We might want to narrow down the inputs affecting the circuit to only a
;;    small named subset, with the rest Xes.

;; Outputs:
;; 1. We might want to keep all signals' values at each phase.

;; 2. We might want to designate a phase in which we keep all signals' values.

;; 3. We might want to narrow down which values we keep to a small named
;;    subset, for performance reasons.

;; States:
;; Presumably for a clock cycle we want to keep initial states free and final
;; states fully expressed.  We might want to save state from the internal
;; phases for debugging purposes.


(defconsts (*cycle-updates* *cycle-nextstates*)
  (b* ((statevars (svex-alist-keys *nextstates*))
       (initst (pairlis$ statevars (svarlist-svex-vars statevars)))
       (invars (svexlist-collect-vars (append (svex-alist-vars *nextstates*)
                                              (svex-alist-vars *updates*))))
       (phase0-ins (b* ((inalist (svtv-input-alist (fal-extract '(clk) (make-fast-alist *input-lhsmap*))
                                                   (make-fast-alist *updates*)))
                        (settings '((clk . 0))))
                     (with-fast-alist settings
                       (svex-alist-compose-rw inalist settings))))
       (phase0-env (append initst phase0-ins))
       ((mv phase0-outs phase0-nextstate)
        (with-fast-alist phase0-env
          (mv (svex-alist-compose-rw *updates* phase0-env)
              (svex-alist-compose-rw *nextstates* phase0-env))))
       (phase1-ins (b* ((inalist (svtv-input-alist (fal-extract '(clk) (make-fast-alist *input-lhsmap*))
                                                   (make-fast-alist *updates*)))
                        (settings '((clk . 1))))
                     (with-fast-alist settings
                       (append (svex-alist-compose-rw inalist settings)
                               (pairlis$ invars
                                         (make-list (len invars)
                                                    :initial-element (svex-x)))))))
       (phase1-env (append phase0-nextstate phase1-ins))
       (phase1-nextstate
        (with-fast-alist phase1-env
          (svex-alist-compose-rw *nextstates* phase1-env))))
    (mv phase0-outs phase1-nextstate)))
                        


;; Let's standardize on having a cycle in which the signals that aren't set to
;; concrete values are left as their original canonical variables.  That means
;; that a wire can't be set to more than one distinct variable in a cycle.  If
;; we want that, then we're going to just do it phase-based instead.
;; Similarly, we're going to produce outputs on one phase of the cycle (we
;; won't require this strictly, but will just append the outputs together so
;; that you get the outputs from the latest phase where they're recorded).

;; So: A cycle will be defined by a list of phases, each of which will have (1)
;; an assignment of (canonical) variables to constant values, (2) a
;; Boolean saying whether the rest of the input variables are assigned Xes or
;; left free, and (3) a Boolean saying whether the outputs are captured that phase.

(fty::defprod svtv-cyclephase
  ((constants svex-env-p)
   (inputs-free booleanp)
   (outputs-captured booleanp))
  :layout :fulltree)


(fty::deflist svtv-cyclephaselist :elt-type svtv-cyclephase :true-listp t)

(define svtv-cycle-step-phase-outs ((ins svex-env-p)
                                    (prev-st svex-env-p)
                                    (phase svtv-cyclephase-p)
                                    (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (outs svex-env-p)
  (b* (((svtv-cyclephase phase))
       (env (svtv-fsm-step-env (if phase.inputs-free
                                   (append phase.constants ins)
                                 phase.constants)
                               prev-st x))
       ((svtv x))
       (outs (and phase.outputs-captured
                  (svex-alist-eval x.outexprs env))))
    (fast-alist-free env)
    outs))

(define svtv-cycle-step-phase-nextsts ((ins svex-env-p)
                                       (prev-st svex-env-p)
                                       (phase svtv-cyclephase-p)
                                       (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (nextsts svex-env-p)
  (b* (((svtv-cyclephase phase))
       (env (svtv-fsm-step-env (if phase.inputs-free
                                   (append phase.constants ins)
                                 phase.constants)
                               prev-st x))
       ((svtv x))
       (nextsts (svex-alist-eval x.nextstate env)))
    (fast-alist-free env)
    nextsts)
  ///
  (defret alist-keys-of-<fn>
    (equal (alist-keys nextsts) (svex-alist-keys (svtv->nextstate x)))))

(define svtv-cycle-step-phase ((ins svex-env-p)
                               (prev-st svex-env-p)
                               (phase svtv-cyclephase-p)
                               (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :prepwork ((local (in-theory (enable svtv-cycle-step-phase-nextsts
                                       svtv-cycle-step-phase-outs))))
  :returns (mv (outs (equal outs (svtv-cycle-step-phase-outs ins prev-st phase x)))
               (nextsts (equal nextsts (svtv-cycle-step-phase-nextsts ins prev-st phase x))))
  (b* (((svtv-cyclephase phase))
       (env (svtv-fsm-step-env (if phase.inputs-free
                                   (append phase.constants ins)
                                 phase.constants)
                               prev-st x))
       ((svtv x))
       (outs (and phase.outputs-captured
                  (svex-alist-eval x.outexprs env)))
       (nextsts (svex-alist-eval x.nextstate env)))
    (fast-alist-free env)
    (mv outs nextsts)))

(define svtv-cycle-eval-outs ((ins svex-env-p)
                              (prev-st svex-env-p)
                              (phases svtv-cyclephaselist-p)
                              (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (outs svex-env-p)
  (b* (((when (atom phases)) nil)
       ((mv outs1 nextst) (svtv-cycle-step-phase ins prev-st (car phases) x))
       (rest-outs (svtv-cycle-eval-outs ins nextst (cdr phases) x)))
    (mbe :logic (append outs1 rest-outs)
         :exec (if rest-outs
                   (append outs1 rest-outs)
                 outs1))))


(define svtv-cycle-eval-nextst ((ins svex-env-p)
                                (prev-st svex-env-p)
                                (phases svtv-cyclephaselist-p)
                                (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (nextst svex-env-p)
  (b* (((when (atom phases))
        (mbe :logic (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st)
             :exec prev-st))
       (nextst (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)))
    (svtv-cycle-eval-nextst ins nextst (cdr phases) x)))


(define svtv-cycle-eval ((ins svex-env-p)
                         (prev-st svex-env-p)
                         (phases svtv-cyclephaselist-p)
                         (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (mv (outs (equal outs (svtv-cycle-eval-outs ins prev-st phases x)))
               (nextst (equal nextst (svtv-cycle-eval-nextst ins prev-st phases x))))
  :prepwork ((local (in-theory (enable svtv-cycle-eval-outs
                                       svtv-cycle-eval-nextst))))
  (b* (((when (atom phases))
        (mv nil
            (mbe :logic (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st)
                 :exec prev-st)))
       ((mv outs1 nextst) (svtv-cycle-step-phase ins prev-st (car phases) x))
       ((mv rest-outs final-st) (svtv-cycle-eval ins nextst (cdr phases) x)))
    (mv (mbe :logic (append outs1 rest-outs)
             :exec (if rest-outs
                       (append outs1 rest-outs)
                     outs1))
        final-st)))
  

(include-book "../svex/unroll")

(encapsulate nil
  (local (in-theory (disable cons-equal member-equal)))
  (local (defthmd svex-alist-extract-when-not-present
           (implies (not (member-equal (caar x) (svarlist-fix keys)))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (svarlist-fix keys)
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthmd svex-alist-extract-when-bad-pair
           (implies (or (not (consp (car x)))
                        (not (svar-p (caar x))))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthm svex-alist-extract-of-cons
           (equal (svex-alist-extract (cons key rest) x)
                  (cons (cons (svar-fix key)
                              (or (svex-lookup key x)
                                  (svex-x)))
                        (svex-alist-extract rest x)))
           :hints(("Goal" :in-theory (enable svex-alist-extract)))))

  (defthm svex-alist-extract-when-same-keys
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-extract (svex-alist-keys x) x)
                    (svex-alist-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-extract-when-bad-pair
                                      svex-alist-extract-when-not-present
                                      svex-alist-fix
                                      svex-alist-keys
                                      no-duplicatesp-equal
                                      svex-lookup)))))


(local (in-theory (disable hons-dups-p)))

(define svtv-fsm-step-subst ((in svex-alist-p)
                             (prev-st svex-alist-p)
                             (x svtv-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (subst svex-alist-p)
  (b* (((svtv x)))
    (make-fast-alist
     (append (mbe :logic (svex-alist-extract (svex-alist-keys x.nextstate)
                                             prev-st)
                  :exec prev-st)
             (svex-alist-fix in))))
  ///
  (defret eval-of-svtv-fsm-step-subst
    (equal (svex-alist-eval subst env)
           (svtv-fsm-step-env (svex-alist-eval in env)
                              (svex-alist-eval prev-st env)
                              x))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-env))))

  (local (defthm svex-lookup-of-append
           (equal (svex-lookup k (append x y))
                  (or (svex-lookup k x)
                      (svex-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defret eval-lookup-of-svtv-fsm-step-subst
    (equal (svex-eval (svex-lookup k subst) env)
           (svex-env-lookup k (svtv-fsm-step-env (svex-alist-eval in env)
                                                 (svex-alist-eval prev-st env)
                                                 x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-env)))))

(define svex-env-to-subst ((x svex-env-p))
  :returns (subst svex-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x)
                    (svex-quote (cdar x)))
              (svex-env-to-subst (cdr x)))
      (svex-env-to-subst (cdr x))))
  ///
  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key subst) env)
           (svex-env-lookup key x))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval subst env)
           (svex-env-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-fix)))))
       

(define svtv-cycle-step-phase-exprs ((ins svex-alist-p)
                                     (prev-st svex-alist-p)
                                     (phase svtv-cyclephase-p)
                                     (x svtv-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextsts svex-alist-p))
  (b* (((svtv-cyclephase phase))
       (subst (svtv-fsm-step-subst (if phase.inputs-free
                                       (append (svex-env-to-subst phase.constants) ins)
                                     (svex-env-to-subst phase.constants))
                                   prev-st x))
       ((svtv x))
       (outs (and phase.outputs-captured
                  (svex-alist-subst-rw x.outexprs subst)))
       (nextsts (svex-alist-subst-rw x.nextstate subst)))
    (fast-alist-free subst)
    (clear-memoize-table 'svex-subst-rw)
    (mv outs nextsts))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (svtv-cycle-step-phase-outs (svex-alist-eval ins env)
                                       (svex-alist-eval prev-st env)
                                       phase x))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-outs)
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextsts env)
           (svtv-cycle-step-phase-nextsts (svex-alist-eval ins env)
                                          (svex-alist-eval prev-st env)
                                          phase x))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts)
            :expand ((svex-alist-eval nil env)))))

  (local (defthm svex-eval-of-svex-lookup
           (equal (svex-eval (svex-lookup k x) env)
                  (svex-env-lookup k (svex-alist-eval x env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-lookup svex-lookup
                                             svex-env-fix svex-alist-fix)))))

  (defret eval-outs-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k outs) env)
           (svex-env-lookup k
                            (svtv-cycle-step-phase-outs (svex-alist-eval ins env)
                                                           (svex-alist-eval prev-st env)
                                                           phase x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret eval-nextsts-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k nextsts) env)
           (svex-env-lookup k
                            (svtv-cycle-step-phase-nextsts (svex-alist-eval ins env)
                                                             (svex-alist-eval prev-st env)
                                                             phase x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret svex-alist-keys-of-<fn>-nextst
    (equal (svex-alist-keys nextsts)
           (svex-alist-keys (svtv->nextstate x)))))


;; (define svtv-cycle-compile-outs ((ins svex-alist-p)
;;                                  (prev-st svex-alist-p)
;;                                  (phases svtv-cyclephaselist-p)
;;                                  (x svtv-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
;;   :returns (outs svex-alist-p)
;;   :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
;;                       (implies (svex-alist-p x)
;;                                (true-listp x)))))
;;   (b* (((when (atom phases)) nil)
;;        ((mv outs1 nextst) (svtv-cycle-step-phase-exprs ins prev-st (car phases) x))
;;        (rest-outs (svtv-cycle-compile-outs ins nextst (cdr phases) x)))
;;     (mbe :logic (append outs1 rest-outs)
;;          :exec (if rest-outs
;;                    (append outs1 rest-outs)
;;                  outs1)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval outs env)
;;            (svtv-cycle-eval-outs (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env))))))


;; (define svtv-cycle-compile-nextst ((ins svex-alist-p)
;;                                 (prev-st svex-alist-p)
;;                                 (phases svtv-cyclephaselist-p)
;;                                 (x svtv-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
;;   :returns (nextst svex-alist-p)
;;   (b* (((when (atom phases))
;;         (mbe :logic (svex-alist-extract (svex-alist-keys (svtv->nextstate x)) prev-st)
;;              :exec prev-st))
;;        (nextst (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)))
;;     (svtv-cycle-compile-nextst ins nextst (cdr phases) x))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval nextst env)
;;            (svtv-cycle-eval-nextst (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env)))))

;;   (defret svex-alist-keys-of-<fn>
;;     (equal (svex-alist-keys nextst)
;;            ()


(define svtv-cycle-compile ((ins svex-alist-p)
                         (prev-st svex-alist-p)
                         (phases svtv-cyclephaselist-p)
                         (x svtv-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextst svex-alist-p))
  :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
                      (implies (svex-alist-p x)
                               (true-listp x)))))
  (b* (((when (atom phases))
        (mv nil
            (mbe :logic (svex-alist-extract (svex-alist-keys (svtv->nextstate x)) prev-st)
                 :exec prev-st)))
       ((mv outs1 nextst) (svtv-cycle-step-phase-exprs ins prev-st (car phases) x))
       ((mv rest-outs final-st) (svtv-cycle-compile ins nextst (cdr phases) x)))
    (mv (mbe :logic (append outs1 rest-outs)
             :exec (if rest-outs
                       (append outs1 rest-outs)
                     outs1))
        final-st))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (svtv-cycle-eval-outs (svex-alist-eval ins env)
                                 (svex-alist-eval prev-st env)
                                 phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextst env)
           (svtv-cycle-eval-nextst (svex-alist-eval ins env)
                                   (svex-alist-eval prev-st env)
                                   phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst)
            :induct <call>
            :expand ((svex-alist-eval nil env))))))




