; Copyright (C) 2026
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Tests for books/tools/defthm-prune.lisp

(in-package "ACL2")

(include-book "defthm-prune")

(defun dp-t-f (x)
  (declare (xargs :guard t))
  (+ 1 (ifix x)))
(defun dp-t-g (x)
  (declare (xargs :guard t))
  (dp-t-f (+ 1 (ifix x))))
(defund dp-t-double (x) (+ x x))

(defund dp-t-unrel-pred (x) (natp x))
(defund dp-t-unrel-val (x) (+ 10 (ifix x)))

(defthm dp-t-unrel-lt-rule
  (implies (dp-t-unrel-pred x)
           (< 0 (dp-t-unrel-val x)))
  :hints (("Goal" :in-theory (enable dp-t-unrel-pred dp-t-unrel-val))))

(defthm dp-t-f-gt-0
  (implies (natp x)
           (< 0 (dp-t-f x))))

(defthmd dp-t-double-rwd
  (equal (dp-t-double x) (+ x x))
  :hints (("Goal" :in-theory (enable dp-t-double))))

(defun dp-t-hop2 (x) (+ 2 (ifix x)))
(defun dp-t-hop1 (x) (dp-t-hop2 x))
(defun dp-t-hop0 (x) (dp-t-hop1 x))

;; 1. Core theory shrinkage, hyp-coverage filter, and primitive def retention
(assert-event
 (let* ((full-th   (current-theory-fn :here (w state)))
        (pruned-th (prune-theory-for-fns '(dp-t-f < natp) 1 nil nil nil (w state) (ens state))))
   (and (< (len pruned-th) (len full-th))
        (consp (member-equal '(:rewrite dp-t-f-gt-0) pruned-th))
        (consp (member-equal '(:definition dp-t-f) pruned-th))
        (consp (member-equal '(:type-prescription dp-t-f) pruned-th))
        (consp (member-equal '(:definition symbolp) pruned-th))
        (null (member-equal '(:rewrite dp-t-unrel-lt-rule) pruned-th))
        (null (member-equal '(:definition dp-t-hop0) pruned-th))
        (prog2$ (cw "~%[dp-test] shrank theory from ~x0 to ~x1 runes~%"
                    (len full-th) (len pruned-th))
                t))))

;; 2. Exact ACL2 enable/disable designator semantics:
;;    (disable fn) disables :definition (and :induction), keeping :executable-counterpart
;;    and :type-prescription; (:e fn) or (fn) disables :executable-counterpart.
(assert-event
 (let* ((th-dis-fn (prune-theory-for-fns '(dp-t-f) 1 nil '(dp-t-f) nil (w state) (ens state)))
        (th-dis-e  (prune-theory-for-fns '(dp-t-f) 1 nil '((:e dp-t-f)) nil (w state) (ens state)))
        (th-dis-p  (prune-theory-for-fns '(dp-t-f) 1 nil '((dp-t-f)) nil (w state) (ens state))))
   (and (null  (member-equal '(:definition dp-t-f) th-dis-fn))
        (consp (member-equal '(:executable-counterpart dp-t-f) th-dis-fn))
        (consp (member-equal '(:type-prescription dp-t-f) th-dis-fn))
        (consp (member-equal '(:definition dp-t-f) th-dis-e))
        (null  (member-equal '(:executable-counterpart dp-t-f) th-dis-e))
        (null  (member-equal '(:executable-counterpart dp-t-f) th-dis-p)))))

;; 3. Strict prune-only (1-hop, 2-hop, bare :use, e/d, keep-rules)
(defthm-prune dp-test-1hop
  (implies (natp x) (< 0 (dp-t-g x)))
  :rule-classes nil
  :prune-fallback nil)

(defthm-prune dp-test-2hop
  (implies (natp x) (equal (dp-t-hop0 x) (+ 2 x)))
  :rule-classes nil
  :prune-hops 2
  :prune-fallback nil)

(defthmd-prune dp-test-bare-use
  (equal (dp-t-double x) (+ x x))
  :prune-fallback nil
  :hints (("Goal" :use dp-t-double-rwd)))

;; Verify defthmd-prune actually disabled its exported rune
(assert-event
 (let ((nume (dp-find-rune-nume '(:rewrite dp-test-bare-use)
                                (dp-rmp 'dp-test-bare-use (w state)))))
   (and nume (not (enabled-numep nume (ens state))))))

(defthm-prune dp-test-keep-rules
  (implies (natp x) (equal (dp-t-hop0 x) (+ 2 x)))
  :rule-classes nil
  :prune-hops 0
  :prune-fallback nil
  :prune-keep-rules (dp-t-hop1 dp-t-hop2))

;; Verify disabling a function still allows ground evaluation via its executable counterpart
(defthm-prune dp-test-disable-keeps-exec
  (equal (dp-t-f 3) 4)
  :rule-classes nil
  :prune-fallback nil
  :hints (("Goal" :in-theory (disable dp-t-f))))

;; 4. Fallback recovery when :prune-hops 0 omits deeper defs
(defthm-prune dp-test-fallback-recovers
  (implies (natp x) (equal (dp-t-hop0 x) (+ 2 x)))
  :rule-classes nil
  :prune-hops 0
  :prune-fallback t
  :prune-step-limit 5000)

;; 5. Computed-hint form (prune-theory-hint) in plain defthm and verify-guards
(defthm dp-test-computed-hint
  (implies (natp x) (< 0 (dp-t-g x)))
  :rule-classes nil
  :hints ((prune-theory-hint :hops 1)))

(defun dp-t-guarded (x)
  (declare (xargs :guard (natp x) :verify-guards nil))
  (/ 1 (dp-t-g x)))

(verify-guards dp-t-guarded
  :hints ((prune-theory-hint :hops 1)))

;; 6. Works inside arithmetic-5/top + rulesets (e/d*)
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (include-book "rulesets"))
  (local (def-ruleset dp-t-rs '(dp-t-double)))
  ;; Verify arithmetic-5's BUBBLE-DOWN cleanup rules are preserved when binary-+ is present
  (assert-event
   (let ((pruned (prune-theory-for-fns '(binary-+ integerp) 1 nil nil nil (w state) (ens state))))
     (consp (member-equal '(:rewrite bubble-down-+-match-1) pruned))))
  (defthm-prune dp-test-arith5-and-ruleset
    (implies (natp x)
             (equal (dp-t-double x) (+ x x)))
    :rule-classes nil
    :prune-fallback nil
    :hints (("Goal" :in-theory (enable* dp-t-rs)))))
