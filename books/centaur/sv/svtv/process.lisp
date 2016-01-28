; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
;                   Jared Davis <jared@centtech.com>

(in-package "SV")
(include-book "structure")
(include-book "expand")
(include-book "doc")
(include-book "../mods/compile")
(include-book "../svex/4vmask")
(include-book "../svex/compose")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "centaur/gl/auto-bindings" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable nth update-nth acl2::nth-when-zp)))
(local (std::add-default-post-define-hook :fix))

(defxdoc process.lisp :parents (svex-stvs))
(local (xdoc::set-default-parents process.lisp))


(local (defthm integerp-lookup-in-4vmask-alist
         (implies (and (4vmask-alist-p x)
                       (hons-assoc-equal k x))
                  (integerp (cdr (hons-assoc-equal k x))))
         :hints(("Goal" :in-theory (enable 4vmask-alist-p)))))


(defthm svtv-entry-p-nth
  (implies (and (svtv-entrylist-p x)
                (nth n x))
           (svtv-entry-p (nth n x)))
  :hints(("Goal" :in-theory (enable nth svtv-entrylist-p))))


(define svtv-inputs->assigns ((x svtv-lines-p) (phase natp))
  :verbosep t
  :prepwork ((local (defthm svar-when-svtv-entry
                      (implies (and (svtv-entry-p x)
                                    (not (4vec-p x)))
                               (svar-p x))
                      :hints(("Goal" :in-theory (enable svtv-entry-p svar-p)))))
             (local (in-theory (enable svtv-lines-fix))))
  :returns (assigns assigns-p)
  (B* (((when (atom x)) nil)
       ((svtv-line xf) (car x))
       (ent (or (nth phase xf.entries) 'acl2::_))
       ((when (svtv-dontcare-p ent))
        (svtv-inputs->assigns (cdr x) phase))
       (val (cond ((4vec-p ent)      (svex-quote ent))
                  ((eq ent 'acl2::x) (svex-quote (4vec-x)))
                  ((eq ent :ones)    (svex-quote -1))
                  (t (svex-var ent)))))
    (cons (cons xf.lhs (make-driver :value val :strength 10))
          (svtv-inputs->assigns (cdr x) phase))))


(define svtv-overrides->assigns ((x svtv-overridelines-p) (phase natp))
  :verbosep t
  :prepwork ((local (defthm svar-when-svtv-entry
                      (implies (and (svtv-entry-p x)
                                    (not (4vec-p x)))
                               (svar-p x))
                      :hints(("Goal" :in-theory (enable svtv-entry-p svar-p)))))
             (local (in-theory (enable svtv-overridelines-fix))))
  :returns (assigns svex-alist-p)
  (B* (((when (atom x)) nil)
       ((svtv-overrideline xf) (car x))
       (ent (or (nth phase xf.entries) 'acl2::_))
       ((when (svtv-dontcare-p ent))
        (cons (cons xf.test (svex-quote 0))
              (svtv-overrides->assigns (cdr x) phase)))
       ((mv val test)
        (cond ((4vec-p ent)      (mv (svex-quote ent)      (svex-quote -1)))
              ((eq ent 'acl2::x) (mv (svex-quote (4vec-x)) (svex-quote -1)))
              ((eq ent :ones)    (mv (svex-quote -1)       (svex-quote -1)))
              (t                 (mv (svex-var ent)        (svex-quote -1))))))
    (cons (cons xf.val val)
          (cons (cons xf.test test)
                (svtv-overrides->assigns (cdr x) phase)))))


(define lhs->mask ((x lhs-p))
  :returns (mask natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable lhs-fix))))
  (b* (((when (atom x)) 0)
       ((lhrange xf) (car x))
       (rest (ash (lhs->mask (cdr x)) xf.w))
       ((when (eq (lhatom-kind xf.atom) :z))
        rest))
    (logior (lognot (ash -1 xf.w)) rest)))



(define lhatom->svex-zero ((x lhatom-p))
  :returns (xx svex-p)
  (lhatom-case x
    :z (svex-quote 0)
    :var (svex-rsh x.rsh (svex-var x.name))))

(define lhrange->svex-zero ((x lhrange-p))
  :returns (s svex-p)
  (b* (((lhrange x) x))
    (svex-concat x.w
                 (lhatom->svex-zero x.atom)
                 (svex-quote (4vec-z)))))

(define lhs->svex-zero ((x lhs-p))
  :returns (xx svex-p)
  :prepwork ((local (in-theory (enable lhs-fix))))
  (if (atom x)
      (svex-quote 0)
    (b* (((lhrange xf) (car x)))
      (svex-concat xf.w
                   (lhatom->svex-zero xf.atom)
                   (lhs->svex-zero (cdr x))))))


(define svtv-outputs->outalist ((x svtv-lines-p) (phase natp))
  :prepwork ((local (defthm svar-when-svtv-entry
                      (implies (and (svtv-entry-p x)
                                    (not (4vec-p x)))
                               (svar-p x))
                      :hints(("Goal" :in-theory (enable svtv-entry-p svar-p)))))
             (local (in-theory (enable svtv-lines-fix))))
  :returns (outalist svex-alist-p)
  (b* (((when (atom x)) nil)
       ((svtv-line xf) (car x))
       (ent (or (nth phase xf.entries) 'acl2::_))
       ((when (svtv-dontcare-p ent))
        (svtv-outputs->outalist (cdr x) phase))
       ((unless (svar-p ent))
        (raise "Bad output entry: ~x0~%" ent)
        (svtv-outputs->outalist (cdr x) phase)))
    (cons (cons ent (lhs->svex-zero xf.lhs))
          (svtv-outputs->outalist (cdr x) phase))))

(define svtv-phase-var ((x svar-p) (phase natp))
  :returns (phasevar svar-p)
  (b* ((x (svar-fix x))
       (x (if (and (consp x) (eq (car x) :var))
              (cdr x)
            x))
       (phase (lnfix phase)))
    (make-svar :name `(:svtv-phase ,phase . ,x))))


;; BOZO use phase variables instead of Xes
(define svtv-inalist-resolve-unassigned ((inalist svex-alist-p) (masks 4vmask-alist-p) (phase natp))
  :measure (len (svex-alist-fix inalist))
  :returns (inalist1 svex-alist-p)
  :hints(("Goal" :in-theory (enable len)))
  (b* ((inalist (svex-alist-fix inalist))
       (masks (4vmask-alist-fix masks))
       ((when (atom inalist)) nil)
       ((cons var expr) (car inalist))
       (mask (or (cdr (hons-get var masks)) 0))
       (exp (svex-call 'bit? (list (svex-quote (2vec mask))
                                   expr
                                   (svex-var (svtv-phase-var var phase))))))
    (cons (cons var exp)
          (svtv-inalist-resolve-unassigned (cdr inalist) masks phase))))

(define svtv-phase-var-assigns ((x svarlist-p) (phase natp))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (assigns svex-alist-p)
  (if (atom x)
      nil
    (cons (let ((v (svar-fix (car x))))
            (cons v (svex-var (svtv-phase-var v phase))))
          (svtv-phase-var-assigns (cdr x) phase))))

(define svtv-phase-inputs ((phase natp) (ins svtv-lines-p) (overrides svtv-overridelines-p)
                           (invars svarlist-p))
  :returns (inalist svex-alist-p)
  (b* ((in-assigns (svtv-inputs->assigns ins phase))
       (ov-assigns (svtv-overrides->assigns overrides phase))
       (netassigns (assigns->netassigns in-assigns))
       (inalist (netassigns->resolves netassigns))
       ((mv masks conflicts) (assigns-check-masks in-assigns nil nil))
       (- (and (consp conflicts)
               (raise "Conflicting assignments. Masks: ~x0~%"
                      (fast-alist-free (fast-alist-clean conflicts)))))
       (- (fast-alist-free conflicts))

       ;; BOZO allow overriding states without Xing them out
       (final-ins (svtv-inalist-resolve-unassigned inalist masks phase))
       (- (fast-alist-free masks)))

    (append ov-assigns final-ins (svtv-phase-var-assigns invars phase))))

(fty::deffixcong svex-alist-equiv svex-alist-equiv (append a b) b)

(define svtv-compile-phase ((phase natp)
                            (ins svtv-lines-p) (overrides svtv-overridelines-p)
                            (outs svtv-lines-p)
                            (prev-state svex-alist-p)     ;; in terms of svtv vars
                            (updates svex-alist-p)        ;; in terms of mod state/inputs
                            (state-updates svex-alist-p)  ;; in terms of mod state/inputs
                            (in-vars svarlist-p))
  :returns (mv (outalist svex-alist-p)
               (next-state svex-alist-p))
  (b* ((input-alist (append (svtv-phase-inputs phase ins overrides in-vars) prev-state))
       ((with-fast input-alist updates))
       (outalist
        ;; outalist just maps svtv vars to wire names so this composition is
        ;; cheap.  therefore, we clear the svex-compose memo table after each
        ;; round even though we repeatedly call this with the same updates
        (svex-alist-compose (svtv-outputs->outalist outs phase) updates))
       (composed-outalist (svex-alist-compose outalist input-alist))
       (next-state (svex-alist-compose state-updates input-alist)))
    (clear-memoize-table 'svex-compose)
    (mv composed-outalist next-state)))


(define svtv-compile ((phase natp) (nphases natp)
                      (ins svtv-lines-p)
                      (overrides svtv-overridelines-p)
                      (outs svtv-lines-p)
                      (prev-state svex-alist-p)
                      (updates svex-alist-p) (state-updates svex-alist-p)
                      (in-vars svarlist-p))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (outalist svex-alist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql nphases phase)))
        nil)
       ((mv phase-outs next-state)
        (svtv-compile-phase phase ins overrides outs prev-state updates state-updates in-vars)))
    (append phase-outs
            (svtv-compile (+ 1 (lnfix phase)) nphases ins overrides outs next-state
                          updates state-updates in-vars))))



;; (define svtv-inputs->drivmasks ((x svtv-lines-p) (phase natp))
;;   :verbosep t
;;   :prepwork ((local (defthm svar-when-svtv-entry
;;                       (implies (and (svtv-entry-p x)
;;                                     (not (4vec-p x)))
;;                                (svar-p x))
;;                       :hints(("Goal" :in-theory (enable svtv-entry-p svar-p)))))
;;              (local (in-theory (enable svtv-lines-fix))))
;;   :returns (vars svar-boolmasks-p
;;                  :hints(("Goal" :in-theory (enable svar-boolmasks-p))))
;;   (B* (((when (atom x)) nil)
;;        ((svtv-line xf) (car x))
;;        (ent (or (nth phase xf.entries) 'acl2::_))
;;        ((when (eq ent 'acl2::_))
;;         (svtv-inputs->drivmasks (cdr x) phase))
;;        ((when (4vec-p ent))
;;         (svtv-inputs->drivmasks (cdr x) phase))
;;        ((when (eq ent 'acl2::x))
;;         (svtv-inputs->drivmasks (cdr x) phase))
;;        ((when (eq ent :ones))
;;         (svtv-inputs->drivmasks (cdr x) phase)))
;;     (cons (cons ent (lhs->mask xf.lhs))
;;           (svtv-inputs->drivmasks (cdr x) phase))))

;; (define svtv-collect-inmasks ((phase natp) (nphases natp)
;;                      (ins svtv-lines-p))
;;   :prepwork ((local (defthm svar-boolmasks-p-of-append
;;                       (implies (and (svar-boolmasks-p x)
;;                                     (svar-boolmasks-p y))
;;                                (svar-boolmasks-p (append x y)))
;;                       :hints(("Goal" :in-theory (enable svar-boolmasks-p))))))
;;   :guard (<= phase nphases)
;;   :measure (nfix (- (nfix nphases) (nfix phase)))
;;   :returns (inmasks svar-boolmasks-p)
;;   (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
;;                    :exec (eql nphases phase)))
;;         nil)
;;        (drivmasks (svtv-inputs->drivmasks ins phase)))
;;     (append drivmasks
;;             (svtv-collect-inmasks (+ 1 (lnfix phase)) nphases ins))))



(local (defthm true-list-listp-append
         (implies (and (true-list-listp a)
                       (true-List-Listp b))
                  (true-list-listp (append a b)))))

(local (defthm svar-boolmasks-p-append
         (implies (and (svar-boolmasks-p a)
                       (svar-boolmasks-p b))
                  (svar-boolmasks-p (append a b)))
         :hints(("Goal" :in-theory (enable svar-boolmasks-p)))))

(define svtv-entries->vars ((x svtv-entrylist-p))
  :returns (vars symbol-listp)
  :prepwork ((local (in-theory (enable svtv-entrylist-fix))))
  (if (atom x)
      nil
    (let ((xf (svtv-entry-fix (car x))))
      (if (and (symbolp xf)
               (not (svtv-dontcare-p xf))
               (not (equal (symbol-name xf) "~"))
               (not (eq xf :ones)))
          (cons xf (svtv-entries->vars (cdr x)))
        (svtv-entries->vars (cdr x)))))
  ///
  (defthm svarlist-p-of-svtv-entries->vars
    (svarlist-p (svtv-entries->vars x))
    :hints(("Goal" :in-theory (enable svar-p svtv-entry-fix svarlist-p)))))

(defthm svar-boolmasks-p-of-pairlis
  (implies (and (svarlist-p x)
                (integer-listp y)
                (equal (len x) (len y)))
           (svar-boolmasks-p (pairlis$ x y)))
  :hints(("Goal" :in-theory (enable svar-boolmasks-p pairlis$ svarlist-p))))

(local
 (defthm integer-listp-of-replicate
   (implies (integerp x)
            (integer-listp (replicate n x)))
   :hints(("Goal" :in-theory (enable replicate)))))

(define svtv-collect-masks ((x svtv-lines-p))
  :returns (xx svar-boolmasks-p)
  :prepwork ((local (in-theory (enable svtv-lines-fix))))
  (b* (((when (atom x)) nil)
       ((svtv-line xf) (car x))
       (vars (svtv-entries->vars xf.entries))
       (mask (lhs->mask xf.lhs)))
    (append (pairlis$ vars (replicate (len vars) mask))
            (svtv-collect-masks (cdr x)))))

(fty::deffixcong true-list-list-equiv true-list-list-equiv (append a b) a
  :hints(("Goal" :in-theory (enable true-list-list-fix))))
(fty::deffixcong true-list-list-equiv true-list-list-equiv (append a b) b
  :hints (("goal" :in-theory (enable append true-list-list-fix))))


(define svtv-init-states ((x svarlist-p))
  :returns (initst svex-alist-p)
  (if (atom x)
      nil
    (cons (let ((v (svar-fix (car x))))
            (cons v
                  (svex-var
                   (make-svar :name
                              (list :svtv-init-st
                                    (svar->name v))))))
          (svtv-init-states (cdr x)))))

(defthm svarlist-p-of-set-difference
  (implies (svarlist-p a)
           (svarlist-p (set-difference$ a b)))
  :hints(("Goal" :in-theory (enable svarlist-p set-difference$))))


(defthm svar-boolmasks-p-of-fast-alist-fork
  (implies (and (svar-boolmasks-p x)
                (svar-boolmasks-p y))
           (svar-boolmasks-p (fast-alist-fork x y))))

(local (defthm atom-of-cdr-last
         (not (consp (cdr (last x))))
         :hints(("Goal" :in-theory (enable last)))
         :rule-classes :type-prescription))

(defthm true-listp-of-fast-alist-fork
  (equal (true-listp (fast-alist-fork x y))
         (true-listp y)))

(defthm cdr-last-under-iff
  (iff (cdr (last x))
       (and (consp x)
            (not (true-listp x))))
  :hints(("Goal" :in-theory (enable last true-listp))))

(defthm true-listp-of-fast-alist-clean
  (equal (true-listp (fast-alist-clean x))
         (true-listp x)))

(defthm svar-boolmasks-p-of-fast-alist-clean
  (implies (svar-boolmasks-p x)
           (svar-boolmasks-p (fast-alist-clean x)))
  :hints(("Goal" :in-theory (enable svar-boolmasks-p))))

(local (in-theory (disable fast-alist-clean)))


(define defsvtv-main ((name symbolp)
                      (ins true-list-listp)
                      (overrides true-list-listp)
                      (outs true-list-listp)
                      (internals true-list-listp)
                      (design design-p)
                      (simplify)
                      (pre-simplify))
  :parents (defsvtv)
  :short "Main subroutine of @(see defsvtv), which extracts output formulas from
          the provided design."
  :guard (modalist-addr-p (design->modalist design))
  :returns (res (iff (svtv-p res) res))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable modscope-local-bound modscope-okp modscope->modidx)))
  :prepwork ((local (in-theory (disable max))))
  :verbosep t
  (b* (((acl2::local-stobjs moddb aliases)
        (mv svtv moddb aliases))
       ;; Make a moddb, canonical alias table, and flattened
       ;; (non-alias-normalized) assignments from the design.  These are
       ;; expressed terms of indexed variable names.
       ((mv err assigns moddb aliases)
        (svex-design-flatten design))
       ((when err) (raise "Error flattening design: ~@0" err)
        (mv nil moddb aliases))
       ;; get the index of the top-level module within the moddb
       (modidx (moddb-modname-get-index (design->top design) moddb))
       ;; Translate the alias table into named variables.
       (aliases (aliases-indexed->named aliases (make-modscope-top :modidx modidx) moddb))
       ;; Alias-normalize the assignments and make a delay table
       ((mv assigns delays) (svex-normalize-assigns assigns aliases))

       ;; Process the timing diagram into internal form
       (orig-ins ins)
       (orig-overrides overrides)
       (orig-outs outs)
       (orig-internals internals)
       ((mv errs1 ins) (svtv-wires->lhses ins modidx moddb aliases))
       (input-err (and errs1 (msg "Errors resolving inputs:~%~@0~%" (msg-list errs1))))
       ((mv errs2 overrides) (svtv-wires->lhses overrides modidx moddb aliases))
       (override-err (and errs2 (msg "Errors resolving overrides:~%~@0~%" (msg-list errs2))))
       ;; Outputs and internals are exactly the same for our purposes.
       ((mv errs3 outs) (svtv-wires->lhses (append outs internals) modidx moddb aliases))
       (output-err (and errs3 (msg "Errors resolving outputs:~%~@0~%" (msg-list errs3))))
       ((when (or input-err override-err output-err))
        (raise "~%~@0" (msg-list (list input-err output-err override-err)))
        (mv nil moddb aliases))

       ;; get the total number of phases to simulate and extend the
       ;; inputs/overrides to that length
       (nphases (max (svtv-max-length ins)
                     (max (svtv-max-length overrides)
                          (svtv-max-length outs))))
       (ins (svtv-expand-lines ins nphases))
       (overrides (svtv-expand-lines overrides nphases))
       ;; Each override has a unique test variable (determining if the override
       ;; happens in a given phase) and override value variable.  This
       ;; generates them (as tagged indices) and records them in data
       ;; structures to associate the LHS for each override with its variables
       ;; and entries.
       ((mv ovlines ovs) (svtv-lines->overrides overrides 0))

       ;; Apply the overrides to the assigns.  Each wire that is overridden has
       ;; its gate-level assignment replaced with something like:
       ;; (if override-this-phase override-value original-assignment)
       ;; except that extra care is taken to override only the specified range.
       (assigns (make-fast-alist assigns))
       (overridden-assigns (svex-apply-overrides ovs assigns))
       ;; Still need the original assigns in case we need to output the value
       ;; of a signal on the same phase as we override it.
       (orig-assigns (make-fast-alist assigns))


       (- (fast-alist-free overridden-assigns))
       ;; Compose together the final (gate-level) assignments to get full
       ;; update formulas (in terms of PIs and current states), and compose
       ;; delays with these to get next states.
       ((mv updates next-states) (svex-compose-assigns/delays overridden-assigns delays
                                                              :rewrite pre-simplify))

       ;; Compute an initial state of all Xes
       (states (svex-alist-keys next-states))
       (initst (pairlis$ states (replicate (len states) (svex-quote (4vec-x)))))

       ;; collect the set of all input variables.  We generate a unique
       ;; variable per phase for each variable (unless it is bound to an STV
       ;; input variable).
       (in-vars (acl2::hons-set-diff (cwtime
                                      (svexlist-collect-vars
                                       (append (svex-alist-vals updates)
                                               (svex-alist-vals next-states)))
                                      :mintime 1)
                                     (append (svex-alist-keys updates)
                                             states)))

       ;; Compose the un-overridden gate-level assignments with the update
       ;; functions (with full overrides).  This gives us a formula for each
       ;; signal before it itself is overridden, but with all the overrides
       ;; within its cone intact.
       (updates-for-outs
        (with-fast-alist updates
          (make-fast-alist (svex-alist-compose orig-assigns updates))))
       (- (fast-alist-free updates)
          (clear-memoize-table 'svex-compose))
       ;; Unroll the FSM and collect the formulas for the output signals.
       (outexprs (cwtime
                  (svtv-compile
                   0 nphases ins ovlines outs initst updates-for-outs next-states in-vars)
                  :mintime 1))

       (has-duplicate-outputs (acl2::hons-dups-p (svex-alist-keys outexprs)))
       ((when has-duplicate-outputs)
        (raise "Duplicated output variable: ~x0" (car has-duplicate-outputs))
        (mv nil moddb aliases))

       (outexprs (if simplify
                     (svex-alist-normalize-concats
                      (svex-alist-rewrite-fixpoint
                       outexprs :verbosep t)
                      :verbosep t)
                   outexprs))

       ;; Compute the masks for the input/output varaiables.
       (inmasks (fast-alist-free (fast-alist-clean (svtv-collect-masks ins))))
       (override-inmasks (fast-alist-free (fast-alist-clean (svtv-collect-masks overrides))))
       (outmasks (fast-alist-free (fast-alist-clean (svtv-collect-masks outs)))))
    (fast-alist-free updates-for-outs)
    (mv (make-svtv :name           name
                   :outexprs       outexprs
                   :inmasks        (append inmasks override-inmasks)
                   :outmasks       outmasks
                   :orig-ins       orig-ins
                   :orig-overrides orig-overrides
                   :orig-outs      orig-outs
                   :orig-internals orig-internals
                   :expanded-ins       ins
                   :expanded-overrides overrides
                   :nphases        nphases)
        moddb aliases)))




(defthm svarlist-p-compound-recongizer
  (implies (svarlist-p x)
           (true-listp x))
  :hints(("Goal" :in-theory (enable svarlist-p)))
  :rule-classes :compound-recognizer)


(defthm svarlist-p-alist-keys-of-svar-boolmasks
  (implies (svar-boolmasks-p x)
           (svarlist-p (alist-keys x)))
  :hints(("Goal" :in-theory (enable svar-boolmasks-p svarlist-p alist-keys))))

(defthm svarlist-p-alist-keys-of-svex-env
  (implies (svex-env-p x)
           (svarlist-p (alist-keys x)))
  :hints(("Goal" :in-theory (enable svex-env-p svarlist-p alist-keys))))

(define svar-boolmasks-limit-to-bound-vars ((keys svarlist-p)
                                            (boolvars svar-boolmasks-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (xx svar-boolmasks-p)
  (if (atom keys)
      nil
    (let* ((look (svar-boolmasks-lookup (car keys) boolvars)))
      (cons (cons (svar-fix (car keys)) look)
            (svar-boolmasks-limit-to-bound-vars (cdr keys) boolvars)))))

(defthm svex-p-of-lookup-in-svex-alist-p
  (implies (and (svex-alist-p x)
                (hons-assoc-equal k x))
           (svex-p (cdr (hons-assoc-equal k x))))
  :hints(("Goal" :in-theory (enable svex-alist-p))))

(defthm svex-alist-p-of-fal-extract
  (implies (svex-alist-p x)
           (svex-alist-p (acl2::fal-extract keys x)))
  :hints(("Goal" :in-theory (enable acl2::fal-extract svex-alist-p))))



(defxdoc svtv-utilities
  :parents (svex-stvs)
  :short "Various utilities for interacting with SVTV structures.")

;; Stv compatibility stuff

(defmacro defalias (new old &key (macro-alias 't) (xdoc 't))
  `(progn (defmacro ,new (&rest args) (cons ',old args))
          ,@(and xdoc
                 `((defxdoc ,new :parents (,old)
                     :short ,(concatenate
                              'string "Same as @(see " (symbol-name old) ")."))))
          ,@(and macro-alias `((add-macro-alias ,new ,old)))))

(define svtv->in-width (name (svtv svtv-p))
  :parents (svtv-utilities)
  :short "Given an input name and an SVTV, get the width of the part that is used."
  :returns (width natp :rule-classes :type-prescription)
  (b* ((look (hons-assoc-equal name (svtv->inmasks svtv)))
       ((unless look)
        (raise "Unknown input: ~x0~%" name)
        0))
    (integer-length (nfix (cdr look))))
  ///
  (defalias stv->in-width svtv->in-width))

(define svtv->out-width (name (svtv svtv-p))
  :parents (svtv-utilities)
  :short "Given an output name and an SVTV, finds the width of that output."
  :returns (width natp :rule-classes :type-prescription)
  (b* ((look (hons-assoc-equal name (svtv->outmasks svtv)))
       ((unless look)
        (raise "Unknown output: ~x0~%" name)
        0))
    (integer-length (nfix (cdr look))))
  ///
  (defalias stv->out-width svtv->out-width))



(define svtv->ins ((svtv svtv-p))
  :parents (svtv-utilities)
  :short "Get the list of input variables of an SVTV."
  :returns (names svarlist-p :rule-classes (:rewrite :type-prescription))
  (alist-keys (svtv->inmasks svtv))
  ///
  (defalias stv->ins svtv->ins))

(define svtv->outs ((svtv svtv-p))
  :parents (svtv-utilities)
  :short "Get the list of output variables of an SVTV."
  :returns (names svarlist-p :rule-classes (:rewrite :type-prescription))
  (svex-alist-keys (svtv->outexprs svtv))
  ///
  (defalias stv->outs svtv->outs))

(define svtv->vars ((svtv svtv-p))
  :parents (svtv-utilities)
  :short "Union of the input and output variables of an SVTV."
  :returns (names svarlist-p :rule-classes (:rewrite :type-prescription))
  (append (svtv->ins svtv)
          (svtv->outs svtv))
  ///
  (defalias stv->vars svtv->vars))





(define svtv-autohyps-aux ((x svar-boolmasks-p))
  :hooks nil
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x)))) (svtv-autohyps-aux (cdr x)))
       ((cons var mask) (car x)))
    (cons `(unsigned-byte-p ,(integer-length mask) ,var)
          (svtv-autohyps-aux (cdr x)))))

(define svtv-autohyps ((x svtv-p))
  :hooks nil
  `(and . ,(svtv-autohyps-aux (svtv->inmasks x))))

(define svtv-autoins-aux ((x svar-boolmasks-p))
  :hooks nil
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x)))) (svtv-autoins-aux (cdr x)))
       (var (caar x)))
    (cons `(cons ',var ,var)
          (svtv-autoins-aux (cdr x)))))

(define svtv-autoins ((x svtv-p))
  :hooks nil
  `(list . ,(reverse (svtv-autoins-aux (svtv->inmasks x)))))

(define svtv-autobinds-aux ((x svar-boolmasks-p))
  :hooks nil
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x)))) (svtv-autobinds-aux (cdr x)))
       ((cons var mask) (car x)))
    (cons `(:nat ,var ,(integer-length mask))
          (svtv-autobinds-aux (cdr x)))))

(define svtv-autobinds ((x svtv-p))
  :hooks nil
  `(gl::auto-bindings . ,(svtv-autobinds-aux (svtv->inmasks x))))


(define defsvtv-default-names (vars)
  (if (atom vars)
      nil
    (cons `(,(car vars) ',(car vars))
          (defsvtv-default-names (cdr vars)))))

;; bozo this is duplicated in ../decomp.lisp
(defthmd assoc-of-acons
  (equal (assoc key (cons (cons k v) a))
         (if (equal key k)
             (cons k v)
           (assoc key a))))

(defthmd assoc-of-nil
  (equal (assoc key nil)
         nil))

(defthmd consp-of-assoc-when-alistp
  (implies (alistp x)
           (iff (consp (assoc k x))
                (assoc k x))))

(defun autoins-lookup-cases (ins)
  (declare (xargs :guard t))
  (if (atom ins)
      nil
    (cons `(,(car ins)
            (cons ',(car ins) ,(car ins)))
          (autoins-lookup-cases (cdr ins)))))

(defun autoins-lookup-casesplit (ins var)
  (declare (xargs :guard t))
  (if (atom ins)
      nil
    (cons `(equal ,var ',(car ins))
          (autoins-lookup-casesplit (cdr ins) var))))





(define defsvtv-fn ((name symbolp)
                    (ins true-list-listp)
                    (overrides true-list-listp)
                    (outs true-list-listp)
                    (internals true-list-listp)
                    (design design-p)
                    (design-const symbolp)
                    labels
                    simplify
                    pre-simplify
                    define-macros
                    parents short long)
  :guard (modalist-addr-p (design->modalist design))
  :irrelevant-formals-ok t
  :hooks nil
  ;; much of this copied from defstv
  (b* ((?labels      (if (symbol-listp labels)
                        labels
                      (raise ":labels need to be a symbol-listp.")))

       (want-xdoc-p (or parents short long))
       (short       (cond ((stringp short) short)
                          ((not short)     "")
                          (t               (progn$ (raise ":short must be a string.")
                                                   ""))))
       (long        (cond ((stringp long) long)
                          ((not long)     "")
                          (t              (progn$ (raise ":long must be a string.")
                                                  ""))))

       (svtv (defsvtv-main name ins overrides outs internals design simplify pre-simplify))
       ((unless svtv)
        (raise "failed to generate svtv"))

       ;; Only now, after we've already compiled and processed the STV, do we
       ;; bother to generate the documentation.  We want to make sure it stays
       ;; in this order, because stv-to-xml doesn't have good error reporting.
       (long (if (not want-xdoc-p)
                 long
               (str::cat "<h3>Simulation Diagram</h3>

<p>This is a <see topic='@(url svex-stvs)'>svex symbolic test vector</see>
defined with @(see sv::defsvtv).</p>"
                         (or (svtv-to-xml svtv labels)
                             "Error generating diagram")
                         long)))


       (stvconst             (intern-in-package-of-symbol
                              (str::cat "*" (symbol-name name) "*")
                              name))
       (modconst             (intern-in-package-of-symbol
                              (str::cat "*" (symbol-name name) "-MOD*")
                              name))
       (name-mod             (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-MOD")
                              name))
       (name-autohyps        (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOHYPS")
                              name))
       (name-autohyps-fn     (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOHYPS-FN")
                              name))
       (name-autohyps-body   (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOHYPS-BODY")
                              name))
       (name-alist-autohyps  (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-ALIST-AUTOHYPS")
                              name))
       (name-autoins         (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOINS")
                                name))
       (name-autoins-fn         (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOINS-FN")
                                name))
       (name-autoins-body    (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOINS-BODY")
                              name))
       (name-alist-autoins   (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-ALIST-AUTOINS")
                              name))
       (name-autobinds       (intern-in-package-of-symbol
                              (str::cat (symbol-name name) "-AUTOBINDS")
                              name))
       (invars (mergesort (alist-keys (svtv->inmasks svtv))))
       (invar-defaults (defsvtv-default-names invars))
       (cmds `((defconst ,stvconst ',svtv)

               (defconst ,modconst ,design-const)

               (defund ,name-mod ()
                 (declare (xargs :guard t))
                 ,modconst)

               (define ,name ()
                 :returns (svtv svtv-p)
                 ,stvconst
                 ///

                 (defthm ,(intern-in-package-of-symbol
                           (str::cat "SVTV->OUTS-OF-" (symbol-name name))
                           name)
                   ;; This is trivial by execution or definition of (,name), but
                   ;; often the executable-counterpart and definition will be
                   ;; disabled
                   (equal (svtv->outs (,name))
                          ',(svtv->outs svtv)))

                 (defthm ,(intern-in-package-of-symbol
                           (str::cat "SVTV->INS-OF-" (symbol-name name))
                           name)
                   ;; This is trivial by execution or definition of (,name), but
                   ;; often the executable-counterpart and definition will be
                   ;; disabled
                   (equal (svtv->ins (,name))
                          ',(svtv->ins svtv)))

                 (in-theory (disable (,name)))
                 (add-to-ruleset! svtv-execs '((,name))))

               ,@(if define-macros
                     `((define ,name-autohyps (&key . ,invar-defaults)
                         ,(svtv-autohyps svtv))

                       (defmacro ,name-autohyps-body ()
                         ',(svtv-autohyps svtv))

                       (define ,name-alist-autohyps ((x alistp))
                         :guard-hints
                         (("Goal" :in-theory
                           (e/d** (consp-of-assoc-when-alistp
                                   (eqlablep)
                                   acl2::assoc-eql-exec-is-assoc-equal))))
                         (declare (ignorable x)) ;; incase there are no input vars
                         (b* (((acl2::assocs . ,invars) x))
                           (,name-autohyps)))

                       (add-to-ruleset! gl::shape-spec-obj-in-range-backchain
                                        ,name-autohyps-fn)

                       (add-to-ruleset! gl::shape-spec-obj-in-range-open
                                        ,name-autohyps-fn)

                       (add-to-ruleset! svtv-autohyps ,name-autohyps-fn)
                       (add-to-ruleset! svtv-alist-autohyps ,name-alist-autohyps)

                       (define ,name-autoins (&key . ,invar-defaults)
                         ,(svtv-autoins svtv))

                       (defthm ,(intern-in-package-of-symbol
                                 (str::cat (symbol-name name) "-AUTOINS-LOOKUP")
                                 name)
                         (implies (syntaxp (quotep k))
                                  (equal (assoc k (,name-autoins))
                                         (case k
                                           . ,(autoins-lookup-cases invars))))
                         :hints (("goal" :in-theory (e/d** (,name-autoins-fn
                                                            assoc-of-acons
                                                            assoc-of-nil
                                                            car-cons cdr-cons
                                                            member-equal))
                                  ,@(if (consp invars)
                                        `(:cases ,(autoins-lookup-casesplit invars 'k))
                                      nil))))
                       (defmacro ,name-autoins-body ()
                         ',(svtv-autoins svtv))

                       (define ,name-alist-autoins ((x alistp))
                         :guard-hints
                         (("Goal" :in-theory
                           (e/d** (consp-of-assoc-when-alistp
                                   (eqlablep)
                                   acl2::assoc-eql-exec-is-assoc-equal))))
                         (declare (ignorable x)) ;; in case there are no input vars
                         (b* (((acl2::assocs . ,invars) x))
                           (,name-autoins)))

                       (add-to-ruleset! svtv-autoins ,name-autoins-fn)
                       (add-to-ruleset! svtv-alist-autoins ,name-alist-autoins)

                       (defthm ,(intern-in-package-of-symbol
                                 (str::cat (symbol-name name) "-ALIST-AUTOINS-IDEMPOTENT")
                                 name)
                         (equal (,name-alist-autoins (,name-alist-autoins x))
                                (,name-alist-autoins x))
                         :hints(("Goal" :in-theory (e/d** (,name-alist-autoins
                                                           ,name-autoins-fn
                                                           assoc-of-acons
                                                           car-cons cdr-cons
                                                           (assoc))))))

                       (defthm ,(intern-in-package-of-symbol
                                 (str::cat (symbol-name name) "-ALIST-AUTOINS-LOOKUP")
                                 name)
                         (equal (assoc k (,name-alist-autoins x))
                                (and (member k (svtv->ins ,stvconst))
                                     (cons k (cdr (assoc k x)))))
                         :hints (("goal" :in-theory (e/d** (,name-alist-autoins
                                                            ,name-autoins-fn
                                                            assoc-of-acons
                                                            assoc-of-nil
                                                            car-cons cdr-cons
                                                            member-equal
                                                            (svtv->ins))))))


                       (defthm ,(intern-in-package-of-symbol
                                 (str::cat (symbol-name name) "-ALIST-AUTOHYPS-OF-AUTOINS")
                                 name)
                         (equal (,name-alist-autohyps (,name-alist-autoins x))
                                (,name-alist-autohyps x))
                         :hints(("Goal" :in-theory (e/d** (,name-alist-autohyps
                                                           ,name-alist-autoins
                                                           ,name-autoins-fn
                                                           assoc-of-acons
                                                           car-cons cdr-cons
                                                           (assoc))))))

                       (defmacro ,name-autobinds ()
                         ',(svtv-autobinds svtv)))
                   nil)))
       (cmds (if (not want-xdoc-p)
                 cmds
               (cons `(defxdoc ,name
                        :parents ,parents
                        :short ,short
                        :long ,long)
                     cmds))))

      `(with-output :off (event)
         (progn . ,cmds))))

(defmacro defsvtv (name &key design mod
                        labels
                        inputs
                        overrides
                        outputs
                        internals
                        parents
                        short
                        long
                        (simplify 't)
                        (pre-simplify 't) ;; should this be t by default?
                        (define-macros 't))
  (b* (((unless (xor design mod))
        (er hard? 'defsvtv "DEFSVTV: Must provide either :design or :mod (interchangeable), but not both.~%")))
    `(make-event (defsvtv-fn ',name ,inputs ,overrides ,outputs ,internals
                   ,(or design mod) ',(or design mod) ,labels ,simplify
                   ,pre-simplify ,define-macros
                   ',parents ,short ,long))))

(defxdoc svtv-stimulus-format
  :parents (defsvtv)
  :short "Syntax for inputs/outputs/overrides/internals entries of @(see defsvtv) forms"
  :long "

<p>An SVTV is a timing diagram-like format similar to @(see acl2::esim) @(see
acl2::symbolic-test-vectors).  Each of the fields @(':inputs'), @(':outputs'),
@(':overrides'), and @(':internals') may have a table (list of lists) where the
rows each pertain to a particular (vector) signal and the columns each pertain
to a particular time step.  The @(':inputs') and @(':overrides') entries
provide inputs to the simulation and the @(':outputs') and @(':internals')
entries extract outputs.</p>

<h4>Example</h4>

<p>Here is an example input/override table:</p>
@({
  '((\"clk\"        1   ~)         ;; toggles until the end
    (\"enable\"     _  en)         ;; keeps assigned value until the end
    (\"dataport\"   _ #x20  _)
    (\"data_busa\"  _   _   _   a   _)
    (\"data_busb\"  _   _   _   b   _)
    (\"opcode\"     _  op   _   _   _)
    (\"clkgates\"   _ :ones _ :ones _))
 })
<p>And an example output/internal table:</p>
@({
  '((\"output_signal1\"   _   _   _  out1 _   _   _)
    (\"output_signal2\"   _   _   _   _   _ out2  _))
 })

<p>In both cases, each table is a list of lists.  Each interior list
contains a signal name followed by a list of entries, each of which corresponds
to a phase of simulation.  The number of simulation phases of an SVTV is the
maximum length of any such entry list among the @(':inputs'), @(':outputs'),
@(':overrides'), and @(':internals').  Input/override entries that are shorter
than the simulation are extended to the simulation length by repeating their
last entry, whereas output/internal entries that are shorter than the
simulation are extended with @('_') entries.</p>

<h4>Output Specifications</h4>

<p>There are only two kinds of valid entry for @(':outputs')/@(':internals')
tables:</p>

<ul>
<li>@('_') or @('-'), meaning the signal is ignored at the phase</li>

<li>A variable name, meaning that the signal's value at that phase is assigned
to that output variable.</li>
</ul>

<p>So in the above example, at simulation time frame 4, the value of
@('\"output_signal1\"') will be extracted and at time frame 6, the value of
@('\"output_signal2\"') will be extracted; and these values will be assigned,
respectively, to output variables @('out1') and @('out2').</p>

<h4>Input Specifications</h4>

<p>There are several types of valid entries for @(':inputs')/@(':overrides')
tables:</p>

<ul>

<li>@('_') or @('-') (actually, any symbol whose name is \"_\" or \"-\"), makes
the signal undriven at that phase.  Actually, this means slightly different
things for inputs versus overrides: for an input, the wire simply doesn't get
assigned a value, whereas for an override, it isn't overridden at that
phase.</li>

<li>An integer or @(see 4vec): the signal is assigned that value at that
time.  (An integer <i>is</i> a 4vec, just to be clear.)</li>

<li>(Deprecated): the symbol @('acl2::x'), means the same thing as the constant
value @('(4vec-x)') or @('(-1 . 0)'), namely, assign all bits of the signal the
value X at the given phase.</li>

<li>(Deprecated): the symbol @(':ones'), means the same thing as -1, namely,
assign all bits of the signal the value 1 at the given phase.</li>

<li>The symbol @('~') (actually, any symbol whose name is \"~\") means toggle),
which must be preceded by a constant (4vec) or another @('~'), means the signal
is assigned the bitwise negation of its value from the previous phase.  Thus
the \"clk\" signal in the above example is assigned 1, then 0, then 1, etc.,
because the final @('~') is replicated out to the end of the simulation.</li>

<li>Any other symbol becomes an input variable assigned to that signal at that
phase.</li>

</ul>
")

(defxdoc defsvtv
  :parents (svex-stvs)
  :short "Create an SVTV structure for some simulation pattern of a hardware design."
  :long "

<p>See the @(see sv-tutorial) and the parent topic @(see svex-stvs) for
higher-level discussion; here, we provide a reference for the arguments.</p>

<ul>

<li>@(':design') or @(':mod') provides the SVEX @(see design) object containing
the hierarchical hardware model.  One or the other of @(':design') or @(':mod')
should be given, but not both; they mean exactly the same thing.</li>

<li>@(':inputs') provide the stimulation pattern for inputs to the module,
formatted as discussed in @(see svtv-stimulus-format).  The argument is
evaluated, so if you want to write your stimulus as a literal (as opposed to
referencing a constant or generating it via a function call) you should put a
quote in front of it; you may also use backquote syntax.</li>

<li>@(':overrides') are similar to @(':inputs') and take the same syntax, but
are expected to refer to signals that are already driven.  For signals that are
overridden, in the cycle that a variable or value is provided, that signal's
driving expressions will be disconnected and it will instead be forced to the
given value.</li>

<li>@(':outputs') and @(':internals') are treated interchangeably; both specify
what signals should be extracted and at what phases of simulation.</li>

<li>@(':parents'), @(':short'), @(':long'), and @(':labels') pertain to
documentation; if any of @(':parents'), @(':short'), or @(':long') are given
then additional xdoc will also be generated to show a timing diagram.
@(':labels'), if provided, label the phases in that timing diagram.</li>

<li>@(':simplify') is T by default; it can be set to NIL to avoid rewriting the
output svex expressions, which may be desirable if you are doing a
decomposition proof.</li>

</ul>

")

;; Alias for defsvtv
(defalias defstv defsvtv :macro-alias nil)




(define svtv-print-alist ((al svex-env-p))
  (if (atom al)
      nil
    (prog2$
     (and (mbt (consp (car al)))
          (if (2vec-p (cdar al))
              (cw "  ~s0:~t1~s2~%" (caar al) 25 (str::hexify (2vec->val (cdar al))))
            (cw "  ~s0:~t1(4v) ~s2~%~t3~s4~%" (caar al) 20 (str::hexify (4vec->upper (cdar al)))
                25 (str::hexify (4vec->lower (cdar al))))))
     (svtv-print-alist (cdr al)))))

(define svtv-print-alist-readable-aux ((al svex-env-p) firstp)
  (if (atom al)
      nil
    (progn$
     (and (mbt (consp (car al)))
          (progn$
           (if firstp
               (cw " ((")
             (cw "  ("))
           (if (2vec-p (cdar al))
               (fmt-to-comment-window
                "~x0 ~t1. ~s2)"
                (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                            #\5 #\6 #\7 #\8 #\9)
                          (list (caar al) 23 (str::hexify (2vec->val (cdar al)))))
                3 nil)
             (progn$
              (fmt-to-comment-window
               "~x0   ~t1~s2         ;; non-Boolean mask: ~s3~%"
               (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                           #\5 #\6 #\7 #\8 #\9)
                         (list (caar al) 25 (str::hexify (4vec->upper (cdar al)))
                               (str::hexify (logxor (4vec->upper (cdar al))
                                                    (4vec->lower (cdar al))))))
               3 nil)
              (cw "       ~t0. ~s1)" 23 (str::hexify (4vec->lower (cdar al))))))
           (if (consp (cdr al))
               (cw "~%")
             (cw ")~%"))))
     (svtv-print-alist-readable-aux (cdr al) nil))))

(define svtv-print-alist-readable ((al svex-env-p))
  (svtv-print-alist-readable-aux al t))




(define svtv-run ((svtv svtv-p "Symbolic test vector created by @(see defsvtv)")
                  (inalist     "Alist mapping input names to @(see 4vec) values")
                  &key
                  ((skip "List of output names that should NOT be computed")   'nil)
                  ((boolvars "For symbolic execution, assume inputs are Boolean-valued") 't)
                  ((simplify "For symbolic execution, apply svex rewriting to the SVTV") 'nil)
                  ((quiet "Don't print inputs/outputs")  'nil)
                  ((readable "Print input/output alists readably") 't))
  :parents (svex-stvs)
  :short "Run an SVTV and get the outputs."
  :long "

<p>@('Svtv-run') runs a simulation of the given @(see symbolic-test-vector) on
the given inputs and returns the output values.</p>

<p>The input names and output names referred to above are the variable symbols
used in the @(see defsvtv) form.  For example,</p>

@({
 (defsvtv my-test
   :inputs
   '((\"clk\"           1   ~)
     (\"dwire\"         _   _   _  dat  _)
     (\"cwire\"         _ ctrl  _   _   _))
   :overrides
   '((\"inst.signal\"   _   _   _  ov   _))
   :outputs
   '((\"firstout\"      _   _   _ outa  _)
     (\"secondout\"     _   _   _   _   _ outb))
   :internals
   '((\"inst2.myint\"   _  intl)))
 })

<p>In this STV, the input names are @('dat'), @('ctrl'), and @('ov'), and the
output names are @('outa'), @('outb'), and @('intl').  See the section @(see
stvs-and-testing) of the @(see sv-tutorial) for more examples.</p>"

  :prepwork ((local (in-theory (enable svarlist-fix))))
  :returns (res svex-env-p "Alist mapping output names to 4vec values")
  (b* (((svtv svtv) svtv)
       (inalist (ec-call (svex-env-fix$inline inalist)))
       ((with-fast inalist))
       (svtv.inmasks (make-fast-alist svtv.inmasks))
       (keys (alist-keys inalist))
       (boolmasks (hons-copy
                   (and boolvars
                        (svar-boolmasks-limit-to-bound-vars keys svtv.inmasks))))
       (outs (b* (((unless (consp skip)) svtv.outexprs)
                  (outkeys (difference (mergesort (svex-alist-keys svtv.outexprs))
                                       (mergesort skip))))
               (acl2::fal-extract outkeys svtv.outexprs)))
       (res
        (mbe :logic (svex-alist-eval-for-symbolic outs
                                                  inalist
                                                  `((:vars . ,(alist-keys svtv.inmasks))
                                                    (:boolmasks . ,boolmasks)
                                                    (:simplify . ,simplify)))
             :exec (svex-alist-eval outs inalist))))
    (clear-memoize-table 'svex-eval)
    (and (not quiet)
         (progn$ (cw "~%SVTV Inputs:~%")
                 (if readable
                     (svtv-print-alist-readable inalist)
                   (svtv-print-alist inalist))
                 (cw "~%SVTV Outputs:~%")
                 (if readable
                     (svtv-print-alist-readable res)
                   (svtv-print-alist res))
                 (cw "~%")))
    res)
  ///
  (defalias stv-run svtv-run)

  (defmacro stv-run-fn (&rest args) (cons 'acl2::svtv-run-fn args))
  (add-macro-alias stv-run-fn acl2::svtv-run-fn)

  (defthm svtv-run-normalize-irrelevant-inputs
    (implies (syntaxp (not (and (equal boolvars ''t)
                                (equal quiet ''nil)
                                (equal simplify ''nil)
                                (equal readable ''t))))
             (equal (svtv-run svtv inalist
                              :skip skip
                              :boolvars boolvars
                              :simplify simplify
                              :quiet quiet
                              :readable readable)
                    (svtv-run svtv inalist :skip skip)))
    :hints(("Goal" :in-theory (enable svex-alist-eval-for-symbolic))))

  (local (defthm alistp-of-svex-alist-eval
           (alistp (Svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval)))))

  (defthm alistp-of-svtv-run
    (alistp (svtv-run svtv inalist :skip skip :boolvars boolvars :quiet quiet)))

  (local (defthm svex-lookup-iff-hons-assoc-equal
           (implies (and (svex-alist-p x)
                         (svar-p k))
                    (iff (svex-lookup k x)
                         (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-lookup hons-assoc-equal)))))

  (local (defthm assoc-of-svex-alist-eval
           (equal (hons-assoc-equal key (svex-alist-eval x env))
                  (and (svar-p key)
                       (assoc key (svex-alist-fix x))
                       (cons key (svex-eval (cdr (assoc key (svex-alist-fix x))) env))))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-fix)))))

  (local (defthm assoc-when-alistp
           (implies (alistp a)
                    (Equal (assoc k a)
                           (hons-assoc-equal k a)))))

  (local (defthm alistp-when-svex-alist-p-rw
           (implies (svex-alist-p x)
                    (alistp x))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (defthm lookup-in-svtv-run-under-iff
    (iff (assoc key (svtv-run svtv inalist :skip skip :boolvars boolvars :quiet quiet))
         (and (member key (svtv->outs svtv))
              (not (member key skip))))
    :hints(("Goal" :in-theory (enable svtv->outs))))

  (defthm lookup-in-svtv-run-consp
    (equal (consp (assoc key (svtv-run svtv inalist :skip skip :boolvars boolvars :quiet quiet)))
         (and (member key (svtv->outs svtv))
              (not (member key skip))))
    :hints(("Goal" :in-theory (enable svtv->outs))))

  (defthm 4vec-p-lookup-in-svtv-run
    (equal (4vec-p (cdr (assoc key (svtv-run svtv inalist :skip skip :boolvars boolvars :quiet quiet))))
           (and (member key (svtv->outs svtv))
                (not (member key skip))))
    :hints(("Goal" :in-theory (enable svtv->outs))))

  (defthm lookup-in-svtv-run-with-skips
    (implies (and (syntaxp (and (quotep skips)
                                (not (equal skips ''nil))))
                  (not (member signal skips)))
             (equal (assoc signal (svtv-run svtv inalist :skip skips))
                    (assoc signal (svtv-run svtv inalist))))
 :hints(("Goal" :in-theory (enable svtv-run)))))

(defthm svex-env-p-of-pairlis
  (implies (and (svarlist-p a)
                (4veclist-p b)
                (equal (len a) (len b)))
           (svex-env-p (pairlis$ a b)))
  :hints(("Goal" :in-theory (enable svex-env-p pairlis$ svarlist-p 4veclist-p))))



(define svtv-run-squash-dontcares ((svtv svtv-p)
                                   inalist
                                   &key
                                   (boolvars 't)
                                   (skip 'nil)
                                   (quiet 'nil)
                                   (simplify 'nil))
  :prepwork ((local (in-theory (enable svarlist-fix))))
  (b* (((svtv svtv) svtv)
       (inalist (ec-call (svex-env-fix$inline inalist)))
       ((with-fast inalist))
       (svtv.inmasks (make-fast-alist svtv.inmasks))
       (keys (alist-keys inalist))
       (boolmasks (hons-copy
                   (and boolvars
                        (svar-boolmasks-limit-to-bound-vars keys svtv.inmasks))))
       (outs (b* (((unless (consp skip)) svtv.outexprs)
                  (outkeys (difference (mergesort (svex-alist-keys svtv.outexprs))
                                       (mergesort skip))))
               (acl2::fal-extract outkeys svtv.outexprs)))
       (othervars (svexlist-collect-vars (svex-alist-vals outs)))
       (othervars-env (pairlis$ othervars (replicate (len othervars) 0)))
       (othervars-boolmasks (pairlis$ othervars (replicate (len othervars) -1)))
       (res (mbe :logic (svex-alist-eval-for-symbolic
                         outs
                         (append (svex-env-fix inalist) othervars-env)
                         `((:vars .  ,(append (alist-keys svtv.inmasks) othervars))
                           (:boolmasks . ,(append boolmasks othervars-boolmasks))
                           (:simplify . ,simplify)))
                 :exec (svex-alist-eval outs (append (svex-env-fix inalist) othervars-env)))))
    (and (not quiet)
         (progn$ (cw "~%SVTV Inputs:~%")
                 (svtv-print-alist inalist)
                 (cw "~%SVTV Outputs:~%")
                 (svtv-print-alist res)
                 (cw "~%")))
    res))




(define svtv-easy-bindings-inside-mix ((x "Some arguments inside of a :mix")
                                      (svtv svtv-p))
  :parents (svtv-easy-bindings)
  (cond ((atom x)
         nil)
        ((symbolp (car x))
         ;; Should be an SVTV input.
         (cons `(:nat ,(car x) ,(svtv->in-width (car x) svtv))
               (svtv-easy-bindings-inside-mix (cdr x) svtv)))
        (t
         ;; Anything else is illegal inside mix.
         (raise "Inside a :mix you can only have symbols (the names of svtv ~
                 inputs), so ~x0 is illegal." (car x)))))

(define svtv-easy-bindings-main ((x   "Some arguments to easy-bindings")
                                (svtv svtv-p))
  (cond ((atom x)
         nil)
        ((symbolp (car x))
         ;; Should be an SVTV input.
         (cons `(:nat ,(car x) ,(svtv->in-width (car x) svtv))
               (svtv-easy-bindings-main (cdr x) svtv)))
        ((and (consp (car x))
              (equal (caar x) :mix))
         (let ((things-to-mix (cdar x)))
           (if (consp things-to-mix)
               (cons `(:mix . ,(svtv-easy-bindings-inside-mix things-to-mix svtv))
                     (svtv-easy-bindings-main (cdr x) svtv))
             (raise ":MIX with no arguments? ~x0" (car x)))))
        (t
         (raise "Arguments to svtv-easy-bindings should be input names or ~
                 (:mix input-name-list), so ~x0 is illegal." (car x)))))

(program)

(define svtv-easy-bindings
  :hooks nil
  :parents (symbolic-test-vector)
  :short "Generating G-bindings from an SVTV in a particular way."

  ((svtv   "The SVTV you are dealing with."
          svtv-p)
   (order "The variable order you want to use."))

  :long "<p>@(call svtv-easy-bindings) is a macro for proving theorems about
@(see symbolic-test-vector)s using @(see gl::gl).  It returns a list of
G-bindings for use with @(see gl::def-gl-thm).  That is, you can write something
like:</p>

@({
 (def-gl-thm foo
    ...
    :g-bindings
    (svtv-easy-bindings (my-svtv) '(opcode size special (:mix a b) c)))
})

<p>This is probably only useful when:</p>

<ul>

<li>You are using GL in BDD mode, not some AIG or SAT based mode.</li>

<li>You are running into performance problems when using the default
@('-autobinds') from the @(see defsvtv).</li>

<li>You want to see if a different variable order performs better.</li>

</ul>

<p>To use @('svtv-easy-bindings'), you just list (a subset of) the SVTV inputs in
priority order.  For instance, in the above example, the @('opcode') will get
the smallest indices, then @('size') next, etc.  You do <b>not</b> have to list
all of the SVTV variables.  Any unmentioned variables will be assigned indices
after mentioned variables.</p>

<p>As in @(see gl::auto-bindings), you can also use @('(:mix a b c ...)') to
interleave the bits of @('a'), @('b'), @('c'), ...; note that for this to work
these variables must all share the same width.  This is generally useful for
data buses that are going to be combined together.</p>

<p>An especially nice feature of easy-bindings is that they automatically
adjust when inputs to the SVTV are resized, when new inputs are added, and when
irrelevant inputs are removed.</p>"

  (b* ((binds   (svtv-easy-bindings-main order svtv))
       (unbound (set-difference-equal (svtv->ins svtv)
                                      (acl2::pat-flatten1 binds))))
    (gl::auto-bindings-fn
     (append binds
             ;; bozo ugly, but workable enough...
             (svtv-easy-bindings-inside-mix unbound svtv))))
  ///
  (defmacro stv-easy-bindings (&rest args) (cons 'svtv-easy-bindings args))
  (add-macro-alias stv-easy-bindings svtv-easy-bindings))





(defxdoc svex-stvs
  :parents (sv)
  :short "Using SVEX-based STVs as a replacement for ESIM/4v-sexpr-based STVs"
  :long
  "<p>Svex STVs are a mostly-drop-in replacement for ESIM-based STVs.  In this
topic we discuss practicalities of making the transition.</p>

<h3>Obtaining a Module</h3>

<p>An example of the full process, starting from a Verilog file and resulting
in a constant containing the new svex design:</p>

@({
 (local ;; optional
  (include-book \"svex/vl-svex\" :dir :cbooks))
 (defconsts (*my-design* state)
    (b* (((mv loadres state)
          (vl::vl-load (vl::make-vl-loadconfig
                        :edition :verilog-2005
                        :start-files '(\"/foo/bar/mymod.v\")
                        :search-path '(\"/library/directory1\"
                                       \"/library/directory2\"))))
         (vl-design (vl::vl-loadresult->design loadres))
         ((mv ?err svex-design ?vl-good-design ?vl-bad-design)
          (vl::cwtime (vl::vl-design->svex-design \"topmodule\" vl-design
                                                  (vl::make-vl-simpconfig)))))
      (and err
           (er hard? 'my-design \Error: ~@0~%\" err))
      (mv svex-design state)))
 })

<p>The resulting constant @('*my-design*') (if there is no error) is an
@('sv::design-p') object that, among other things, can be passed to
@('defsvtv').</p>

<h3>General STV Creation and Usage</h3>

<p>The svex STV package is largely compatible with the ESIM STV package.  In
particular, the following functions/macros have largely the same meaning and
interface in both packages:</p>
@({
 defstv
 stv-run
 stv-easy-bindings
 stv-debug
 stv->ins
 stv->outs
 stv->out-width
 stv->in-width
 })

<p>Each of these names is defined in the SVEX package and also aliased in the
ACL2 package but with \"SVTV\" used instead of \"STV\".  This allows two ways
of transitioning from ESIM STVs to SVEX STVs: if your proofs are in a package,
then just import the symbols above from the SVEX package instead of the ACL2
package; otherwise, search and replace \"stv\" with \"svtv\" in your sources;
we assume \"stv\" is a rare enough substring that unrelated code isn't likely
to be affected. See also @(see svtv-versus-stv).</p>

<h3>Simulation and Specifications</h3>

<p>The one important difference between svex's @('stv-run') and esim's
@('acl2::stv-run') is in the values of the input/output alists.  Esim's are
either natural numbers or the symbol X, meaning that some bit in the vector is
non-Boolean.  Svex's are @(see 4vec) objects.  These will also be natural
numbers iff all of the bits in the vector are Boolean.  If some bits are X or
Z, then the 4vec will be a cons of two integers; where the corresponding bits
are the same, they indicate Boolean values, and where they are opposite, @('(1
. 0)') indicates X and @('(0 . 1)') indicates Z.  Therefore, if your
specifications make queries like @('(eq (cdr (assoc 'my-result out-alist))
\'x)') then you'll need to change these to some other idiom.</p>

<h3>Symbolic Simulation</h3>

<p>Svex STVs support symbolic simulation via the GL package similar to esim
STVs: first, the formulas are expressed as AIGs and then these AIGs are
composed with the symbolic representations of the inputs.  This is implemented
in the book \"svex/symbolic.lisp\".  Svex's stv-run has an optional keyword
argument that can have an impact on symbolic execution (but doesn't mean
anything logically): @(':boolvars') is T by default, and in this case the
symbolic execution assumes that all your input vectors are syntactically
obviously Boolean-valued.  This helps symbolic execution speed, but can cause
an error like:</p>

@({ ERROR: some bits assumed to be Boolean were not. })

<p>If you see such an error, you should set @(':boolvars nil').</p>

<h3>Decomposition Proofs</h3>

<p>The book \"svex/decomp.lisp\" contains a proof strategy for proving that the
composition of two or more STV runs is equivalent to some other STV run.  It
provides a computed hint that provides a good theory for rewriting such rules,
then a meta rule that can reverse the decomposition, and an invocation of GL to
finish off any mismatches due to svex simplification.  Here is an example
showing that the composition of STVs @('stv-a') and @('stv-b') is equivalent to
@('stv-c'):</p>

@({
 (defthm a-and-b-compose-to-c
  (implies (stv-c-autohyps)
           (b* ((c-out (stv-run (stv-c) (stv-c-autoins)))
                (a-ins (stv-a-autoins))
                (a-out (stv-run (stv-a) a-ins))
                ;; may be various ways of making the input to the 2nd phase
                (b-ins (stv-b-alist-autoins (append a-ins a-out)))
                (b-out (stv-run (stv-b) b-ins)))
             (and
               ;; may be various forms for the final equivalence
               (equal (extract-keys *my-keys* b-out)
                      (extract-keys *my-keys* c-out))
               (equal (cdr (assoc 'out b-out))
                      (cdr (assoc 'out c-out)))
               (equal b-out c-out))))
  :hints ((sv::svdecomp-hints :hyp (stv-c-autohyps)
                                :g-bindings (stv-c-autobinds)
                                :enable (extract-keys-of-cons))))
 })

<p>The @(':hyp') and @(':g-bindings') arguments to svdecomp-hints are for the
GL phase.  Usually some autohyps and autobindings from your STV are
appropriate. @(':enable') allows you to add rules to use in the initial
rewriting phase before the meta rule is used.  This can help on occasion when
you want to use some particular function to (e.g.) construct the alist for some
subsequent step or to extract values to compare.</p>

<p>More information about the decomposition strategy is in @(see svex-decomp),
or will be someday.</p>")

(defxdoc svtv-versus-stv
  :parents (svex-stvs)
  :short "A note on naming conventions"
  :long "

<p>Svex STVs are modeled after @(see acl2::esim) @(see
acl2::symbolic-test-vectors), and since they are intended to be a nearly
drop-in replacement, we had to mangle the names of existing esim STV-related
functions somehow.  We settled on the following scheme:</p>

<p>Basically all Esim STV-related functions/utilities have names in the ACL2
package and containing \"STV\".  So for an Esim function
@('acl2::some-stv-tool'), we name our Svex analogue @('acl2::some-svtv-tool')
and import that symbol into the SVEX package.  We also add an alias
@('sv::some-stv-tool') (not in the ACL2 package).  To summarize, you can
refer to the Svex version of this function by any of the following:</p>

<ul>
<li>@('acl2::some-svtv-tool')</li>
<li>@('sv::some-svtv-tool'), really the same symbol as above</li>
<li>@('sv::some-stv-tool'), a macro alias for the above.</li>
</ul>

<p>The modified name \"SVTV\" doesn't really stand for anything aside from
perhaps \"Svex symbolic test vector.\" In svex-related documentation, we refer
to STVs and SVTVs more or less interchangeably, unless we are explicitly
referring to Esim STVs (in which case we won't say SVTV).  We usually refer to
functions using the SVTV versions of the name, since that will be the same in
either package.</p>

<p>Maybe we shouldn't pollute the ACL2 package with the SVTV symbols, and
instead just use STV symbols in the SVEX package.  We don't have much of an
excuse other than sometimes we're working in the ACL2 package and want to just
type an extra V rather than an extra @('SV::').</p>")


