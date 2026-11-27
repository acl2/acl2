; Copyright 2026 Google LLC
; Use of this source code is governed by a BSD-style license that can be
; found in the LICENSE file.
;
; books/tools/defthm-prune.lisp
;
; Zero-Dependency Heuristic Theory Pruner for ACL2:
;   - (defthm-prune  name formula &rest opts)  : drop-in peer of defthm
;   - (defthmd-prune name formula &rest opts)  : drop-in peer of defthmd
;   - (prune-theory-hint &key (hops 1) keep disable)
;       : computed hint usable in defthm, define :returns, defret, defrule,
;         verify-guards, defun, etc.
;   - (prune-theory-for-fns seed-fns hops en-items dis-items use-rw-dis wrld ens)
;       : pure function returning the pruned runic theory list.
;
; ZERO include-book dependencies, ZERO defaxiom, ZERO skip-proofs, ZERO trust tags.
; Works in any ACL2 package (all emitted core symbols are explicitly ACL2-qualified).
;
; How it works:
;   1. Collects seed function symbols from the translated goal formula (or clause)
;      plus :use/:by lemmas and :instance terms, :cases, :expand, :induct, :enable,
;      and :prune-keep-rules.
;   2. Expands reachable symbols by :prune-hops (default 1) through enabled
;      definition bodies and covered non-primitive rewrite-rule RHSs, plus a
;      1-step RHS-auxiliary closure on core arithmetic operators (preserving
;      arithmetic-5 cleanup rules such as BUBBLE-DOWN without pulling in
;      unrelated domain functions).
;   3. Keeps minimal-theory, primitive :definition runes (avoiding spurious
;      Theory warnings), cheap structural rune classes (:compound-recognizer,
;      :equivalence, :congruence, :refinement, :elim, :tau-system,
;      :built-in-clause, :fake-rune-*), and ONLY enabled :definition,
;      :executable-counterpart, :induction, :type-prescription, :rewrite,
;      :linear, :forward-chaining, and :meta runes whose trigger/LHS AND
;      hypotheses are covered by the reachable symbol set.
;   4. Respects Goal :in-theory (enable/disable/e/d and rulesets */variants)
;      using ACL2's exact runic-designator semantics (e.g., disabling a function
;      name disables :definition and :induction, preserving :executable-counterpart
;      and :type-prescription unless explicitly named).
;   5. With :prune-fallback T (default), emits (make-event '(:or <pruned> <orig>))
;      capped by :prune-step-limit (default 50000) on the pruned attempt.
;      With :prune-fallback NIL, enforces the pruned theory strictly.

(in-package "ACL2")

(program)
(set-state-ok t)

(defconst *dp-core-fns*
  '(if not equal iff eq eql synp hide force case-split return-last
    acl2-numberp rationalp real/rationalp integerp natp posp zp zip
    fix ifix nfix rfix realfix booleanp consp atom null endp true-listp))

(defconst *dp-no-rw-expand-fns*
  '(if not equal iff eq eql binary-+ binary-* unary-- unary-/ < cons car cdr))

(defconst *dp-arith-rhs-aux-ops*
  '(binary-+ binary-* unary-- unary-/ < expt floor mod))

(defconst *dp-always-keep-tags*
  '(:compound-recognizer :equivalence :congruence
    :refinement :elim :tau-system :built-in-clause
    :fake-rune-for-type-set :fake-rune-for-linear
    :fake-rune-for-linear-equalities))

(defconst *dp-default-hops* 1)
(defconst *dp-default-step-limit* 50000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: World & Designator Helpers (Zero Dependencies)

(defun dp-fn-p (sym wrld)
  (and (symbolp sym)
       (not (eq :none (getprop sym 'formals :none 'current-acl2-world wrld)))))

(defun dp-theorem-p (sym wrld)
  (and (symbolp sym)
       (not (eq :none (getprop sym 'theorem :none 'current-acl2-world wrld)))))

(defun dp-deftheory-p (sym wrld)
  (and (symbolp sym)
       (not (eq :none (getprop sym 'theory :none 'current-acl2-world wrld)))))

(defun dp-rmp (sym wrld)
  (if (symbolp sym)
      (getprop sym 'runic-mapping-pairs nil 'current-acl2-world wrld)
    nil))

(defun dp-find-rune-nume (rune rmp)
  (cond ((endp rmp) nil)
        ((equal (cdar rmp) rune) (caar rmp))
        (t (dp-find-rune-nume rune (cdr rmp)))))

(defun dp-def-enabled-p (sym wrld ens)
  (let ((nume (dp-find-rune-nume (list :definition sym) (dp-rmp sym wrld))))
    (and nume (enabled-numep nume ens))))

;; Resolve macro-aliases (e.g. + -> binary-+, append -> binary-append)
(defun dp-resolve-alias (sym wrld)
  (if (symbolp sym)
      (let ((pair (assoc-eq sym (macro-aliases wrld))))
        (if pair (cdr pair) sym))
    sym))

;; Match ACL2's CONVERT-THEORY-TO-UNORDERED-MAPPING-PAIRS1 semantics for a bare symbol:
;;   - Function symbol -> (:definition fn) [+ (:induction fn) if recursive]
;;     (does NOT include :executable-counterpart or :type-prescription)
;;   - Theorem symbol  -> all runes of that theorem
(defun dp-symbol-designator-runes (sym wrld)
  (let* ((deref (dp-resolve-alias sym wrld))
         (rmp   (dp-rmp deref wrld)))
    (cond
     ((and (consp rmp)
           (consp (cdr rmp))
           (consp (cdar rmp))
           (eq (car (cdar rmp)) :definition)
           (consp (cdadr rmp))
           (eq (car (cdadr rmp)) :executable-counterpart))
      (if (equal (len rmp) 4)
          (list (cdar rmp) (cdr (cadddr rmp)))
        (list (cdar rmp))))
     (rmp
      (strip-cdrs rmp))
     (t nil))))

;; Expand rune designators including deftheories, rune abbreviations (:e, :d, :t, :r, :i),
;; 1-element executable-counterpart shorthand (fn), and optional tools/rulesets entries.
(mutual-recursion
 (defun dp-expand-designator (item wrld seen-rs)
   (cond
    ((consp item)
     (cond
      ((and (eq (car item) :ruleset) (consp (cdr item)) (symbolp (cadr item)))
       (dp-expand-ruleset (cadr item) wrld seen-rs))
      ((and (eq (car item) :theory) (consp (cdr item)) (symbolp (cadr item))
            (dp-deftheory-p (cadr item) wrld))
       (theory-fn (cadr item) wrld))
      ((and (null (cdr item)) (symbolp (car item)))
       (let* ((deref (dp-resolve-alias (car item) wrld))
              (rmp   (dp-rmp deref wrld)))
         (if (and (consp rmp) (consp (cdr rmp))
                  (consp (cdadr rmp))
                  (eq (car (cdadr rmp)) :executable-counterpart))
             (list (cdadr rmp))
           nil)))
      ((keywordp (car item))
       (let ((r (translate-abbrev-rune item (macro-aliases wrld))))
         (if (runep r wrld)
             (list r)
           nil)))
      (t nil)))
    ((symbolp item)
     (let* ((sym-runes (dp-symbol-designator-runes item wrld))
            (rs-pair   (assoc-eq item (table-alist 'acl2::ruleset-table wrld))))
       (cond
        (sym-runes
         sym-runes)
        ((dp-deftheory-p item wrld)
         (theory-fn item wrld))
        (rs-pair
         (dp-expand-ruleset item wrld seen-rs))
        (t nil))))
    (t nil)))

 (defun dp-expand-ruleset (name wrld seen-rs)
   (if (member-eq name seen-rs)
       nil
     (let ((pair (assoc-eq name (table-alist 'acl2::ruleset-table wrld))))
       (if (and pair (true-listp (cdr pair)))
           (dp-expand-designators-aux (cdr pair) wrld (cons name seen-rs))
         nil))))

 (defun dp-expand-designators-aux (items wrld seen-rs)
   (if (endp items)
       nil
     (append (dp-expand-designator (car items) wrld seen-rs)
             (dp-expand-designators-aux (cdr items) wrld seen-rs)))))

(defun dp-expand-designators (items wrld)
  (dp-expand-designators-aux items wrld nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Seed Symbol Collection & Hop Expansion

(mutual-recursion
 (defun dp-syntactic-fn-syms (form wrld acc)
   (cond
    ((atom form) acc)
    ((eq (car form) 'quote) acc)
    (t
     (let* ((hd   (dp-resolve-alias (car form) wrld))
            (acc1 (if (dp-fn-p hd wrld) (add-to-set-eq hd acc) acc)))
       (dp-syntactic-fn-syms-lst (cdr form) wrld acc1)))))

 (defun dp-syntactic-fn-syms-lst (forms wrld acc)
   (if (endp forms)
       acc
     (dp-syntactic-fn-syms-lst (cdr forms) wrld
                               (dp-syntactic-fn-syms (car forms) wrld acc)))))

(defun dp-term-fn-syms (form ctx wrld state acc)
  (mv-let (erp tr state)
    (translate form t nil nil ctx wrld state)
    (if erp
        (mv (dp-syntactic-fn-syms form wrld acc) state)
      (mv (union-eq (all-fnnames tr) acc) state))))

(defun dp-term-list-fn-syms (forms ctx wrld state acc)
  (if (endp forms)
      (mv acc state)
    (mv-let (acc1 state)
      (dp-term-fn-syms (car forms) ctx wrld state acc)
      (dp-term-list-fn-syms (cdr forms) ctx wrld state acc1))))

(defun dp-instance-pairs-fn-syms (pairs ctx wrld state acc)
  (if (endp pairs)
      (mv acc state)
    (let ((pair (car pairs)))
      (if (and (consp pair) (consp (cdr pair)))
          (mv-let (acc1 state)
            (dp-term-fn-syms (cadr pair) ctx wrld state acc)
            (dp-instance-pairs-fn-syms (cdr pairs) ctx wrld state acc1))
        (dp-instance-pairs-fn-syms (cdr pairs) ctx wrld state acc)))))

(defun dp-fn-inst-pairs-fn-syms (pairs wrld acc)
  (if (endp pairs)
      acc
    (let* ((pair (car pairs))
           (rhs  (if (and (consp pair) (consp (cdr pair)))
                     (dp-resolve-alias (cadr pair) wrld)
                   nil))
           (acc1 (if (dp-fn-p rhs wrld) (add-to-set-eq rhs acc) acc)))
      (dp-fn-inst-pairs-fn-syms (cdr pairs) wrld acc1))))

(defun dp-use-item-seeds (item ctx wrld state acc-fns acc-rw-dis)
  (cond
   ((symbolp item)
    (let* ((f    (if (dp-theorem-p item wrld) (formula item t wrld) nil))
           (fns1 (if f (union-eq (all-fnnames f) acc-fns) acc-fns))
           (rw   (list :rewrite item))
           (dis1 (if (dp-find-rune-nume rw (dp-rmp item wrld))
                     (cons rw acc-rw-dis)
                   acc-rw-dis)))
      (mv fns1 dis1 state)))
   ((and (consp item) (eq (car item) :instance) (consp (cdr item)))
    (mv-let (fns1 dis1 state)
      (dp-use-item-seeds (cadr item) ctx wrld state acc-fns acc-rw-dis)
      (mv-let (fns2 state)
        (dp-instance-pairs-fn-syms (cddr item) ctx wrld state fns1)
        (mv fns2 dis1 state))))
   ((and (consp item) (eq (car item) :functional-instance) (consp (cdr item)))
    (mv-let (fns1 dis1 state)
      (dp-use-item-seeds (cadr item) ctx wrld state acc-fns acc-rw-dis)
      (mv (dp-fn-inst-pairs-fn-syms (cddr item) wrld fns1) dis1 state)))
   ((and (consp item) (consp (cdr item)) (symbolp (cadr item)))
    (let* ((sym  (dp-resolve-alias (cadr item) wrld))
           (f    (if (dp-theorem-p sym wrld) (formula sym t wrld) nil))
           (fns1 (cond (f (union-eq (all-fnnames f) acc-fns))
                       ((dp-fn-p sym wrld) (add-to-set-eq sym acc-fns))
                       (t acc-fns))))
      (mv fns1 acc-rw-dis state)))
   (t (mv acc-fns acc-rw-dis state))))

;; Accepts both standard list (:use (a b)) and bare ACL2 (:use a) or (:use (:instance ...))
(defun dp-normalize-use-val (val)
  (cond ((null val) nil)
        ((symbolp val) (list val))
        ((and (consp val)
              (member-eq (car val) '(:instance :functional-instance
                                     :definition :rewrite :linear :type-prescription
                                     :forward-chaining :compound-recognizer :elim :meta)))
         (list val))
        ((true-listp val) val)
        (t nil)))

(defun dp-use-list-seeds (items ctx wrld state acc-fns acc-rw-dis)
  (if (endp items)
      (mv acc-fns acc-rw-dis state)
    (mv-let (fns1 dis1 state)
      (dp-use-item-seeds (car items) ctx wrld state acc-fns acc-rw-dis)
      (dp-use-list-seeds (cdr items) ctx wrld state fns1 dis1))))

(defun dp-expand-items-seeds (items ctx wrld state acc)
  (if (endp items)
      (mv acc state)
    (let ((item (car items)))
      (cond
       ((and (consp item) (eq (car item) :free) (equal (len item) 3))
        (mv-let (acc1 state)
          (dp-term-fn-syms (caddr item) ctx wrld state acc)
          (dp-expand-items-seeds (cdr items) ctx wrld state acc1)))
       ((and (consp item) (eq (car item) :with) (equal (len item) 3))
        (let* ((hd   (dp-resolve-alias (cadr item) wrld))
               (acc0 (if (dp-fn-p hd wrld) (add-to-set-eq hd acc) acc)))
          (mv-let (acc1 state)
            (dp-term-fn-syms (caddr item) ctx wrld state acc0)
            (dp-expand-items-seeds (cdr items) ctx wrld state acc1))))
       ((and (consp item) (not (keywordp (car item))))
        (mv-let (acc1 state)
          (dp-term-fn-syms item ctx wrld state acc)
          (dp-expand-items-seeds (cdr items) ctx wrld state acc1)))
       (t
        (dp-expand-items-seeds (cdr items) ctx wrld state acc))))))

(defun dp-runes-seeds (runes wrld acc)
  (if (endp runes)
      acc
    (let* ((r    (car runes))
           (sym  (if (and (consp r) (consp (cdr r)) (symbolp (cadr r)))
                     (dp-resolve-alias (cadr r) wrld)
                   nil))
           (acc1 (cond ((null sym) acc)
                       ((dp-theorem-p sym wrld)
                        (let ((f (formula sym t wrld)))
                          (if f (union-eq (all-fnnames f) acc) acc)))
                       ((dp-fn-p sym wrld)
                        (add-to-set-eq sym acc))
                       (t acc))))
      (dp-runes-seeds (cdr runes) wrld acc1))))

(defun dp-plist-get (key plist)
  (cond ((or (endp plist) (endp (cdr plist))) nil)
        ((eq (car plist) key) (cons t (cadr plist)))
        (t (dp-plist-get key (cddr plist)))))

(defun dp-goal-plist-seeds (plist ctx wrld state acc-fns acc-rw-dis)
  (let ((use-p (dp-plist-get :use plist))
        (by-p  (dp-plist-get :by plist))
        (cas-p (dp-plist-get :cases plist))
        (exp-p (dp-plist-get :expand plist))
        (ind-p (dp-plist-get :induct plist)))
    (mv-let (fns1 dis1 state)
      (if use-p
          (dp-use-list-seeds (dp-normalize-use-val (cdr use-p))
                             ctx wrld state acc-fns acc-rw-dis)
        (mv acc-fns acc-rw-dis state))
      (mv-let (fns2 dis2 state)
        (if (and by-p (cdr by-p))
            (dp-use-item-seeds (cdr by-p) ctx wrld state fns1 dis1)
          (mv fns1 dis1 state))
        (mv-let (fns3 state)
          (if (and cas-p (true-listp (cdr cas-p)))
              (dp-term-list-fn-syms (cdr cas-p) ctx wrld state fns2)
            (mv fns2 state))
          (mv-let (fns4 state)
            (if (and exp-p (true-listp (cdr exp-p)))
                (dp-expand-items-seeds (cdr exp-p) ctx wrld state fns3)
              (mv fns3 state))
            (mv-let (fns5 state)
              (if (and ind-p (consp (cdr ind-p)))
                  (dp-term-fn-syms (cdr ind-p) ctx wrld state fns4)
                (mv fns4 state))
              (mv fns5 dis2 state))))))))

(defun dp-hints-list-seeds (hints ctx wrld state acc-fns acc-rw-dis)
  (if (endp hints)
      (mv acc-fns acc-rw-dis state)
    (let ((entry (car hints)))
      (if (and (consp entry) (stringp (car entry)) (true-listp (cdr entry)))
          (mv-let (fns1 dis1 state)
            (dp-goal-plist-seeds (cdr entry) ctx wrld state acc-fns acc-rw-dis)
            (dp-hints-list-seeds (cdr hints) ctx wrld state fns1 dis1))
        (dp-hints-list-seeds (cdr hints) ctx wrld state acc-fns acc-rw-dis)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Core Theory Pruner (Pure)

(defun dp-rw-rhs-fns (rules known-fns dis-runes use-rw-dis ens acc)
  (if (endp rules)
      acc
    (let* ((r    (car rules))
           (sub  (access rewrite-rule r :subclass))
           (rune (access rewrite-rule r :rune))
           (nume (access rewrite-rule r :nume)))
      (if (and (not (eq sub 'meta))
               (enabled-numep nume ens)
               (not (member-equal rune dis-runes))
               (not (member-equal rune use-rw-dis))
               (subsetp-eq (all-fnnames (access rewrite-rule r :lhs)) known-fns)
               (subsetp-eq (all-fnnames-lst (access rewrite-rule r :hyps)) known-fns))
          (dp-rw-rhs-fns (cdr rules) known-fns dis-runes use-rw-dis ens
                         (union-eq (all-fnnames (access rewrite-rule r :rhs)) acc))
        (dp-rw-rhs-fns (cdr rules) known-fns dis-runes use-rw-dis ens acc)))))

(defun dp-expand-frontier (frontier known-fns en-runes dis-runes use-rw-dis wrld ens acc)
  (if (endp frontier)
      acc
    (let ((fn (car frontier)))
      (if (member-eq fn *dp-core-fns*)
          (dp-expand-frontier (cdr frontier) known-fns en-runes dis-runes use-rw-dis
                              wrld ens acc)
        (let* ((def-rune (list :definition fn))
               (def-en   (and (not (member-equal def-rune dis-runes))
                              (or (dp-def-enabled-p fn wrld ens)
                                  (member-equal def-rune en-runes))))
               (body     (if def-en
                             (getprop fn 'unnormalized-body :none 'current-acl2-world wrld)
                           :none))
               (acc1     (if (not (eq body :none))
                             (union-eq (all-fnnames body) acc)
                           acc))
               (acc2     (if (not (member-eq fn *dp-no-rw-expand-fns*))
                             (dp-rw-rhs-fns
                              (getprop fn 'lemmas nil 'current-acl2-world wrld)
                              known-fns dis-runes use-rw-dis ens acc1)
                           acc1)))
          (dp-expand-frontier (cdr frontier) known-fns en-runes dis-runes use-rw-dis
                              wrld ens acc2))))))

(defun dp-expand-fns (known-fns frontier hops en-runes dis-runes use-rw-dis wrld ens)
  (if (or (zp hops) (endp frontier))
      known-fns
    (let* ((next-raw     (dp-expand-frontier frontier known-fns en-runes dis-runes
                                             use-rw-dis wrld ens nil))
           (new-frontier (set-difference-eq next-raw known-fns)))
      (if (endp new-frontier)
          known-fns
        (dp-expand-fns (union-eq new-frontier known-fns)
                       new-frontier
                       (+ -1 hops)
                       en-runes dis-runes use-rw-dis wrld ens)))))

(defun dp-primitive-def-runes (fns acc)
  (if (endp fns)
      acc
    (dp-primitive-def-runes (cdr fns) (cons (list :definition (car fns)) acc))))

(defun dp-filter-base-runes (runes acc)
  (if (endp runes)
      acc
    (let ((r (car runes)))
      (if (and (consp r) (member-eq (car r) *dp-always-keep-tags*))
          (dp-filter-base-runes (cdr runes) (cons r acc))
        (dp-filter-base-runes (cdr runes) acc)))))

(defun dp-collect-rmp-runes (rmp ens acc)
  (if (endp rmp)
      acc
    (let* ((pair (car rmp))
           (nume (car pair))
           (rune (cdr pair)))
      (if (and (enabled-numep nume ens)
               (consp rune)
               (member-eq (car rune) '(:definition :executable-counterpart :induction)))
          (dp-collect-rmp-runes (cdr rmp) ens (cons rune acc))
        (dp-collect-rmp-runes (cdr rmp) ens acc)))))

(defun dp-collect-tp-runes (tps ens acc)
  (if (endp tps)
      acc
    (let* ((tp   (car tps))
           (nume (access type-prescription tp :nume))
           (rune (access type-prescription tp :rune)))
      (if (and (enabled-numep nume ens) (consp rune))
          (dp-collect-tp-runes (cdr tps) ens (cons rune acc))
        (dp-collect-tp-runes (cdr tps) ens acc)))))

(defun dp-collect-rw-runes-and-rhs (rules reachable ens acc-runes acc-rhs)
  (if (endp rules)
      (mv acc-runes acc-rhs)
    (let* ((r    (car rules))
           (nume (access rewrite-rule r :nume))
           (sub  (access rewrite-rule r :subclass))
           (rune (access rewrite-rule r :rune)))
      (cond
       ((not (enabled-numep nume ens))
        (dp-collect-rw-runes-and-rhs (cdr rules) reachable ens acc-runes acc-rhs))
       ((eq sub 'meta)
        (dp-collect-rw-runes-and-rhs (cdr rules) reachable ens (cons rune acc-runes) acc-rhs))
       ((and (subsetp-eq (all-fnnames (access rewrite-rule r :lhs)) reachable)
             (subsetp-eq (all-fnnames-lst (access rewrite-rule r :hyps)) reachable))
        (dp-collect-rw-runes-and-rhs (cdr rules) reachable ens
                                     (cons rune acc-runes)
                                     (union-eq (all-fnnames (access rewrite-rule r :rhs)) acc-rhs)))
       (t
        (dp-collect-rw-runes-and-rhs (cdr rules) reachable ens acc-runes acc-rhs))))))

(defun dp-collect-kept-rw-rhs-fns (fns reachable wrld ens acc-rhs)
  (if (endp fns)
      acc-rhs
    (mv-let (ign rhs1)
      (dp-collect-rw-runes-and-rhs
       (getprop (car fns) 'lemmas nil 'current-acl2-world wrld)
       reachable ens nil acc-rhs)
      (declare (ignore ign))
      (dp-collect-kept-rw-rhs-fns (cdr fns) reachable wrld ens rhs1))))

(defun dp-collect-rw-runes (rules reachable ens acc)
  (mv-let (runes ign)
    (dp-collect-rw-runes-and-rhs rules reachable ens acc nil)
    (declare (ignore ign))
    runes))

(defun dp-collect-lin-runes (lems reachable ens acc)
  (if (endp lems)
      acc
    (let* ((l    (car lems))
           (nume (access linear-lemma l :nume))
           (rune (access linear-lemma l :rune)))
      (if (and (enabled-numep nume ens)
               (subsetp-eq (all-fnnames (access linear-lemma l :max-term)) reachable)
               (subsetp-eq (all-fnnames-lst (access linear-lemma l :hyps)) reachable))
          (dp-collect-lin-runes (cdr lems) reachable ens (cons rune acc))
        (dp-collect-lin-runes (cdr lems) reachable ens acc)))))

(defun dp-collect-fc-runes (fcs reachable ens acc)
  (if (endp fcs)
      acc
    (let* ((fc   (car fcs))
           (nume (access forward-chaining-rule fc :nume))
           (rune (access forward-chaining-rule fc :rune)))
      (if (and (enabled-numep nume ens)
               (subsetp-eq (all-fnnames (access forward-chaining-rule fc :trigger)) reachable)
               (subsetp-eq (all-fnnames-lst (access forward-chaining-rule fc :hyps)) reachable))
          (dp-collect-fc-runes (cdr fcs) reachable ens (cons rune acc))
        (dp-collect-fc-runes (cdr fcs) reachable ens acc)))))

(defun dp-collect-fns-runes (fns reachable wrld ens acc)
  (if (endp fns)
      acc
    (let* ((fn   (car fns))
           (acc1 (dp-collect-rmp-runes (dp-rmp fn wrld) ens acc))
           (acc2 (dp-collect-tp-runes
                  (getprop fn 'type-prescriptions nil 'current-acl2-world wrld)
                  ens acc1))
           (acc3 (dp-collect-rw-runes
                  (getprop fn 'lemmas nil 'current-acl2-world wrld)
                  reachable ens acc2))
           (acc4 (dp-collect-lin-runes
                  (getprop fn 'linear-lemmas nil 'current-acl2-world wrld)
                  reachable ens acc3))
           (acc5 (dp-collect-fc-runes
                  (getprop fn 'forward-chaining-rules nil 'current-acl2-world wrld)
                  reachable ens acc4)))
      (dp-collect-fns-runes (cdr fns) reachable wrld ens acc5))))

(defun prune-theory-for-fns (seed-fns hops en-items dis-items use-rw-dis wrld ens)
  (let* ((en-runes   (dp-expand-designators en-items wrld))
         (dis-runes  (dp-expand-designators dis-items wrld))
         (seeds1     (dp-runes-seeds en-runes wrld seed-fns))
         (known0     (union-eq seeds1 *dp-core-fns*))
         (reachable0 (dp-expand-fns known0 seeds1 hops
                                    en-runes dis-runes use-rw-dis wrld ens))
         ;; 1-step RHS-auxiliary closure ONLY on arithmetic ops (keeps cleanup rules
         ;; for arithmetic-5 markers like BUBBLE-DOWN without expanding domain functions).
         (arith-ops  (intersection-eq reachable0 *dp-arith-rhs-aux-ops*))
         (rhs-fns    (dp-collect-kept-rw-rhs-fns arith-ops reachable0 wrld ens nil))
         (reachable  (union-eq rhs-fns reachable0))
         (min-runes  (theory-fn 'minimal-theory wrld))
         (prim-defs  (dp-primitive-def-runes (strip-cars *primitive-formals-and-guards*)
                                             min-runes))
         (base-runes (dp-filter-base-runes (current-theory-fn :here wrld) prim-defs))
         (fn-runes   (dp-collect-fns-runes reachable reachable wrld ens nil))
         (kept       (remove-duplicates-equal (append en-runes fn-runes base-runes)))
         (final-dis  (append dis-runes (set-difference-equal use-rw-dis en-runes))))
    (set-difference-equal kept final-dis)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Computed Hint Form (prune-theory-hint)

(defun dp-prune-theory-hint-fn (id clause world pspv hops keep disable)
  (if (not (equal id *initial-clause-id*))
      nil
    (let* ((ens      (access rewrite-constant
                             (access prove-spec-var pspv :rewrite-constant)
                             :current-enabled-structure))
           (seed-fns (all-fnnames-lst clause))
           (pruned   (prune-theory-for-fns seed-fns hops keep disable nil world ens)))
      `(:in-theory (acl2::quote ,pruned)))))

(defmacro prune-theory-hint (&key (hops '1) keep disable)
  `(acl2::dp-prune-theory-hint-fn acl2::id acl2::clause acl2::world acl2::pspv
                                  ,hops ',keep ',disable))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: Drop-in Macros (defthm-prune / defthmd-prune)

(defun dp-split-prune-opts (opts hops fb step-lim keep rev-rest ctx-msg)
  (cond
   ((null opts)
    (mv nil hops fb step-lim keep (reverse rev-rest)))
   ((or (not (consp opts)) (not (keywordp (car opts))) (not (consp (cdr opts))))
    (mv (msg "~@0: malformed keyword option list near ~x1." ctx-msg opts)
        nil nil nil nil nil))
   ((eq (car opts) :prune-hops)
    (if (natp (cadr opts))
        (dp-split-prune-opts (cddr opts) (cadr opts) fb step-lim keep rev-rest ctx-msg)
      (mv (msg "~@0: :PRUNE-HOPS must be a natural number, got ~x1." ctx-msg (cadr opts))
          nil nil nil nil nil)))
   ((eq (car opts) :prune-fallback)
    (if (booleanp (cadr opts))
        (dp-split-prune-opts (cddr opts) hops (cadr opts) step-lim keep rev-rest ctx-msg)
      (mv (msg "~@0: :PRUNE-FALLBACK must be T or NIL, got ~x1." ctx-msg (cadr opts))
          nil nil nil nil nil)))
   ((eq (car opts) :prune-step-limit)
    (if (or (null (cadr opts)) (posp (cadr opts)))
        (dp-split-prune-opts (cddr opts) hops fb (cadr opts) keep rev-rest ctx-msg)
      (mv (msg "~@0: :PRUNE-STEP-LIMIT must be NIL or a positive integer, got ~x1."
               ctx-msg (cadr opts))
          nil nil nil nil nil)))
   ((eq (car opts) :prune-keep-rules)
    (if (true-listp (cadr opts))
        (dp-split-prune-opts (cddr opts) hops fb step-lim (cadr opts) rev-rest ctx-msg)
      (mv (msg "~@0: :PRUNE-KEEP-RULES must be a proper list, got ~x1." ctx-msg (cadr opts))
          nil nil nil nil nil)))
   (t
    (dp-split-prune-opts (cddr opts) hops fb step-lim keep
                         (list* (cadr opts) (car opts) rev-rest)
                         ctx-msg))))

;; Extract (mv ok en-items dis-items) from Goal :in-theory (enable/disable/e/d + * variants)
(defun dp-parse-in-theory-delta (expr)
  (cond
   ((not (consp expr)) (mv nil nil nil))
   ((and (symbolp (car expr))
         (member-equal (symbol-name (car expr)) '("ENABLE" "ENABLE*"))
         (true-listp (cdr expr)))
    (mv t (cdr expr) nil))
   ((and (symbolp (car expr))
         (member-equal (symbol-name (car expr)) '("DISABLE" "DISABLE*"))
         (true-listp (cdr expr)))
    (mv t nil (cdr expr)))
   ((and (symbolp (car expr))
         (member-equal (symbol-name (car expr)) '("E/D" "E/D*"))
         (equal (len expr) 3)
         (true-listp (cadr expr))
         (true-listp (caddr expr)))
    (mv t (cadr expr) (caddr expr)))
   (t (mv nil nil nil))))

(defun dp-find-goal-entry (hints)
  (cond ((endp hints) nil)
        ((and (consp (car hints)) (equal (caar hints) "Goal")) (car hints))
        (t (dp-find-goal-entry (cdr hints)))))

(defun dp-plist-strip (plist key)
  (cond ((or (endp plist) (endp (cdr plist))) nil)
        ((eq (car plist) key) (dp-plist-strip (cddr plist) key))
        (t (list* (car plist) (cadr plist) (dp-plist-strip (cddr plist) key)))))

(defun dp-inject-pruned-theory (hints pruned-runes found-goal)
  (cond
   ((endp hints)
    (if found-goal
        nil
      (list (list "Goal" :in-theory `(acl2::quote ,pruned-runes)))))
   ((and (consp (car hints)) (equal (caar hints) "Goal"))
    (cons (list* "Goal"
                 :in-theory `(acl2::quote ,pruned-runes)
                 (dp-plist-strip (cdar hints) :in-theory))
          (dp-inject-pruned-theory (cdr hints) pruned-runes t)))
   (t
    (cons (car hints)
          (dp-inject-pruned-theory (cdr hints) pruned-runes found-goal)))))

(defun dp-compile-defthm-prune (name formula opts disable-p wrld ens state)
  (let* ((defthm-sym (if disable-p 'acl2::defthmd 'acl2::defthm))
         (ctx-msg    (msg "In ~s0 ~x1" (if disable-p "DEFTHMD-PRUNE" "DEFTHM-PRUNE") name)))
    (mv-let (oerr hops fb step-lim keep-rules base-opts)
      (dp-split-prune-opts opts *dp-default-hops* t *dp-default-step-limit* nil nil ctx-msg)
      (if oerr
          (mv oerr nil state)
        (let* ((orig-ev  `(,defthm-sym ,name ,formula ,@base-opts))
               (instr-p  (dp-plist-get :instructions base-opts))
               (hints-p  (dp-plist-get :hints base-opts))
               (hints    (if (and hints-p (true-listp (cdr hints-p))) (cdr hints-p) nil))
               (g-entry  (dp-find-goal-entry hints))
               (g-th-p   (if g-entry (dp-plist-get :in-theory (cdr g-entry)) nil)))
          ;; If :instructions is used or Goal has a non-delta custom :in-theory, pass through cleanly.
          (if instr-p
              (mv nil orig-ev state)
            (mv-let (delta-ok en-items dis-items)
              (if g-th-p
                  (dp-parse-in-theory-delta (cdr g-th-p))
                (mv t nil nil))
              (if (not delta-ok)
                  (if fb
                      (mv nil orig-ev state)
                    (mv (msg "~@0: cannot prune Goal with custom :IN-THEORY ~x1 when ~
                              :PRUNE-FALLBACK NIL."
                             ctx-msg (cdr g-th-p))
                        nil state))
                (mv-let (terp tr-formula state)
                  (translate formula t nil nil name wrld state)
                  (if terp
                      (mv (msg "~@0: failed to translate formula: ~@1" ctx-msg terp)
                          nil state)
                    (mv-let (seed-fns use-rw-dis state)
                      (dp-hints-list-seeds hints name wrld state (all-fnnames tr-formula) nil)
                      (let* ((all-en       (append en-items keep-rules))
                             (pruned-runes (prune-theory-for-fns
                                            seed-fns hops all-en dis-items
                                            use-rw-dis wrld ens))
                             (pruned-hints (dp-inject-pruned-theory hints pruned-runes nil))
                             (other-opts   (dp-plist-strip base-opts :hints))
                             (pruned-ev    `(,defthm-sym ,name ,formula
                                              :hints ,pruned-hints
                                              ,@other-opts)))
                        (if (not fb)
                            (mv nil pruned-ev state)
                          (let ((p-ev (if step-lim
                                          `(acl2::with-prover-step-limit ,step-lim ,pruned-ev)
                                        pruned-ev)))
                            (mv nil
                                `(acl2::make-event '(:or ,p-ev ,orig-ev))
                                state)))))))))))))))

(defmacro defthm-prune (name formula &rest opts)
  `(acl2::make-event
    (acl2::mv-let (dp$err dp$ev acl2::state)
      (acl2::dp-compile-defthm-prune ',name ',formula ',opts nil
                                     (acl2::w acl2::state) (acl2::ens acl2::state) acl2::state)
      (if dp$err
          (acl2::er acl2::soft (cons 'acl2::defthm-prune ',name) "~@0" dp$err)
        (acl2::value dp$ev)))))

(defmacro defthmd-prune (name formula &rest opts)
  `(acl2::make-event
    (acl2::mv-let (dp$err dp$ev acl2::state)
      (acl2::dp-compile-defthm-prune ',name ',formula ',opts t
                                     (acl2::w acl2::state) (acl2::ens acl2::state) acl2::state)
      (if dp$err
          (acl2::er acl2::soft (cons 'acl2::defthmd-prune ',name) "~@0" dp$err)
        (acl2::value dp$ev)))))
