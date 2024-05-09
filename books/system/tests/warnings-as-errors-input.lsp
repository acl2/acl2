; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; There are some calls of warning1-cw that print to the comment window.  Let's
; redirect that output to the current value of 'standard-co.

(redef+)
(make-event `(defconst *standard-co* ',(standard-co state)))
(redef-)

; Undo possible skipping of locals, e.g., by the build system (note that
; set-inhibit-warnings is really a local event, for example):
(set-ld-always-skip-top-level-locals nil state)

(defthm foo (equal (car (cons x x)) x)) ; warning

(u)

(set-warnings-as-errors t '("Subsume") state)

(defthm foo (equal (car (cons x x)) x)) ; error

(set-inhibit-warnings "Subsume")

(defthm foo (equal (car (cons x x)) x)) ; quiet success

(u)

(set-warnings-as-errors :always '("Theory" "SUBSUME") state)

(defthm foo (equal (car (cons x x)) x)) ; error

(set-warnings-as-errors :always :all state)

(defthm foo (equal (car (cons x x)) x)) ; error

(set-warnings-as-errors t :all state)

(defthm foo (equal (car (cons x x)) x)) ; quiet success

(u)

(toggle-inhibit-warning "Subsume")

(defthm foo (equal (car (cons x x)) x)) ; error

(set-warnings-as-errors nil "Use" state) ; error (need a list)

(set-warnings-as-errors nil '("Use") state)

(defthm foo (equal (car (cons x x)) x)) ; error

(set-warnings-as-errors nil '("subsume") state)

(defthm foo (equal (car (cons x x)) x)) ; warning

(u)

(set-warnings-as-errors t '("Use") state)

(defthm foo (equal (car (cons x x)) x)) ; warning

(u)

(set-warnings-as-errors t '("Subsume") state)

(defthm foo (equal (car (cons x x)) x)) ; error

; Test warnings without a type.

(set-warnings-as-errors nil :all state) ; restore default
(set-inhibit-output-lst '(prove)) ; warning
(set-inhibit-output-lst '(proof-tree)) ; restore default
(set-warnings-as-errors t :all state)
(set-inhibit-output-lst '(prove)) ; error
(set-warnings-as-errors nil :all state) ; restore default
(set-inhibit-output-lst '(proof-tree warning))
(set-inhibit-output-lst '(prove)) ; quiet
(set-inhibit-output-lst '(proof-tree warning)) ; restore default and add warning
(set-warnings-as-errors t :all state)
(set-inhibit-output-lst '(prove)) ; quiet
(set-inhibit-output-lst '(proof-tree)) ; restore default
(set-warnings-as-errors :always :all state)
(set-inhibit-output-lst '(prove)) ; error
(assert-event (equal (@ inhibit-output-lst) '(proof-tree)))

; Test warning$-cw1
(set-inhibit-output-lst '(proof-tree)) ; restore default
(set-warnings-as-errors nil :all state) ; restore default
(defmacro mac (&key x) x)
(mac :x 3 :x 4) ; error
(set-duplicate-keys-action mac :warning)
(mac :x 3 :x 4) ; warning
(set-warnings-as-errors t '("Duplicate-Keys") state)
(mac :x 3 :x 4) ; error
(set-inhibit-output-lst '(warning)) ; inhibit warnings
(mac :x 3 :x 4) ; quiet
(set-warnings-as-errors :always '("Duplicate-Keys") state)
(mac :x 3 :x 4) ; error
(set-warnings-as-errors t :all state)
(mac :x 3 :x 4) ; quiet
(set-warnings-as-errors :always '("Duplicate-Keys") state)
(mac :x 3 :x 4) ; error

; Test warning$-cw
(set-inhibit-output-lst '(proof-tree)) ; restore default
(set-warnings-as-errors nil :all state) ; restore default
(defun fn (x) x)
(memoize 'fn) ; error
(memoize 'fn :ideal-okp :warn) ; warning
(u)
(set-warnings-as-errors t :all state)
(memoize 'fn :ideal-okp :warn) ; error
(set-inhibit-output-lst '(warning)) ; inhibit warnings
(memoize 'fn :ideal-okp :warn) ; quiet
(u)
(set-warnings-as-errors :always '("memoize") state)
(memoize 'fn :ideal-okp :warn) ; error

; Test warning$ when warning output is inhibited, rather than a type of
; warning.
(set-inhibit-output-lst '(proof-tree)) ; restore default
(set-warnings-as-errors t '("use") state)
(defthm foo ; error
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)
(set-inhibit-output-lst '(warning proof-tree))
(defthm foo ; quiet
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)
(u)
(set-warnings-as-errors :always '("use") state)
(defthm foo ; error
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)
(set-warnings-as-errors t :all state)
(defthm foo ; quiet
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)
(u)
(set-warnings-as-errors nil '("xyz") state)
(defthm foo ; quiet
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)
(u)
(set-inhibit-output-lst '(proof-tree)) ; restore default
(defthm foo ; error
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)
(set-warnings-as-errors nil '("USE") state)
(defthm foo ; warning
  t
  :hints (("Goal" :use car-cons))
  :rule-classes nil)

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)
