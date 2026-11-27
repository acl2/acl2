; Copyright 2026 Google LLC
; Use of this source code is governed by a BSD-style license that can be
; found in the LICENSE file.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc defthm-prune
  :parents (proof-automation theories macro-libraries)
  :short "Heuristic theory pruning for @(tsee defthm) and computed hints"
  :long "<p>The zero-dependency community book @('tools/defthm-prune') provides
 a lightweight heuristic theory pruner that restricts a proof's initial
 @('\"Goal\"') theory to runes reachable from the symbols in the goal formula
 and its hints.  It introduces no @(see defttag)s, no axioms, and no
 @('include-book') dependencies, and works from any ACL2 package.</p>

 <h3>Usage</h3>

 @({
 (local (include-book \"tools/defthm-prune\" :dir :system))

 ;; Drop-in peers of defthm and defthmd:
 (defthm-prune my-thm
   (equal (foo (append x y)) ...)
   :hints ((\"Goal\" :induct (foo x))))

 (defthmd-prune my-disabled-thm
   ...)

 ;; Computed-hint form (usable in defthm, define :returns, defret,
 ;; defrule, verify-guards, defun, etc.):
 (defthm my-other-thm
   ...
   :hints ((prune-theory-hint :hops 1)))
 })

 <h3>Options for @('defthm-prune') / @('defthmd-prune')</h3>

 <p>All standard @(tsee defthm) keyword options are passed through unchanged.
 Four additional optional keywords control pruning:</p>

 <ul>
 <li>@(':prune-hops') (default @('1')): number of expansion hops from the
 initial seed function symbols through enabled definitions and covered
 non-primitive rewrite-rule right-hand sides.</li>
 <li>@(':prune-fallback') (default @('t')): when @('t'), emits
 @('(make-event '(:or <pruned> <original>))') so that if the pruned attempt
 fails or exceeds @(':prune-step-limit'), ACL2 falls back transparently to the
 unpruned event.  When @('nil'), enforces the pruned theory strictly.</li>
 <li>@(':prune-step-limit') (default @('50000')): prover step limit applied to
 the pruned attempt when @(':prune-fallback t'); may be @('nil') for no
 limit.</li>
 <li>@(':prune-keep-rules') (default @('nil')): list of extra runic designators
 (or ruleset names) to keep enabled and seed from.</li>
 </ul>

 <h3>Options for @('prune-theory-hint')</h3>

 @({
 (prune-theory-hint &key (hops 1) keep disable)
 })

 <p>Fires at @('*initial-clause-id*') and returns an @(':in-theory') hint
 computed from the function symbols in the initial clause.  @(':keep') and
 @(':disable') accept lists of runic designators.</p>

 <h3>How it works</h3>

 <ol>
 <li>Collects seed function symbols from the translated goal formula (or
 initial clause) together with any @(':use'), @(':by'), @(':cases'),
 @(':expand'), @(':induct'), @(':in-theory') @('enable')/@('enable*'), and
 @(':prune-keep-rules') items.</li>
 <li>Expands the reachable symbol set by @(':prune-hops') hops through enabled
 definition bodies and covered rewrite-rule right-hand sides, plus a one-step
 RHS-auxiliary closure on core arithmetic operators (preserving
 @('arithmetic-5') cleanup rules such as @('BUBBLE-DOWN') without pulling in
 unrelated domain definitions).</li>
 <li>Constructs a @('\"Goal\"') theory containing @(tsee minimal-theory),
 primitive @(':definition') runes, cheap structural rune classes
 (@(':compound-recognizer'), @(':equivalence'), @(':congruence'),
 @(':refinement'), @(':elim'), @(':tau-system'), @(':built-in-clause'), and
 @(':fake-rune-*')), and only those enabled @(':definition'),
 @(':executable-counterpart'), @(':induction'), @(':type-prescription'),
 @(':rewrite'), @(':linear'), @(':forward-chaining'), and @(':meta') runes
 whose trigger/LHS and hypotheses are covered by the reachable symbol set.</li>
 <li>Applies any @('\"Goal\"') @(':in-theory') @('enable')/@('disable')/@('e/d')
 (and @('tools/rulesets') @('*') variants) using ACL2's runic-designator
 semantics.  If @(':instructions') or a non-delta custom @('\"Goal\"')
 @(':in-theory') is given, @('defthm-prune') passes the event through
 unchanged when @(':prune-fallback t').</li>
 </ol>

 <p>The pure core function @(tsee prune-theory-for-fns) is also exported for
 programmatic inspection or custom computed hints.</p>")

(defpointer defthmd-prune defthm-prune)
(defpointer prune-theory-hint defthm-prune)
(defpointer prune-theory-for-fns defthm-prune)
