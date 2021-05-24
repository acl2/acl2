; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(verify-termination illegal-fmt-string) ; and guards
(verify-termination fmt-char) ; and guards
(verify-termination zero-one-or-more) ; and guards
(verify-termination standard-evisc-tuplep) ; and guards
(verify-termination fmt-var) ; and guards

; Start termination and guards for find-alternative-skip.

(verify-termination find-alternative-skip
  (declare (xargs :verify-guards nil)))

(defthm find-alternative-skip-increases-1
  (implies (not (equal (1+ maximum) (find-alternative-skip s i maximum quiet)))
           (< i (find-alternative-skip s i maximum quiet)))
  :rule-classes :linear)

(defthm find-alternative-skip-increases-2
  (implies (<= i maximum)
           (<= i (find-alternative-skip s i maximum quiet)))
  :rule-classes :linear)

(defthm find-alternative-skip-bound
  (implies (natp maximum)
           (<= (find-alternative-skip s i maximum quiet)
               (1+ maximum)))
  :rule-classes :linear)

(defthm natp-find-alternative-skip
  (implies (natp maximum)
           (natp (find-alternative-skip s i maximum quiet)))
  :rule-classes :type-prescription)

(local (in-theory (disable nth)))

(verify-guards find-alternative-skip)

; Start termination and guards for find-alternative-start1, based on events
; above for find-alternative-skip, and then find-alternative-start.

(verify-termination find-alternative-start1
  (declare (xargs :verify-guards nil)))

(defthm find-alternative-start1-increases-1
  (let ((index (find-alternative-start1 x s i maximum quiet)))
    (implies (and (not (equal (1+ maximum) index))
                  (not (equal (- maximum) index))
                  (not (equal maximum index))
                  (<= 0 index))
             (<= i index)))
  :rule-classes :linear)

(defthm find-alternative-start1-increases-2
  (implies (and (natp i)
                (<= i maximum)
                (<= 0 (find-alternative-start1 x s i maximum quiet)))
           (<= i (find-alternative-start1 x s i maximum quiet)))
  :rule-classes :linear)

(defthm find-alternative-start1-bound
  (implies (and (natp i)
                (<= i maximum))
           (<= (find-alternative-start1 x s i maximum quiet)
               (1+ maximum)))
  :rule-classes :linear)

(defthm integerp-find-alternative-start1
  (implies (and (natp maximum)
                (natp i))
           (integerp (find-alternative-start1 x s i maximum quiet)))
  :rule-classes :type-prescription)

(defthm find-alternative-skip-bound-alt
  (implies (and (natp maximum)
                (not (equal (find-alternative-skip s i maximum quiet)
                            (1+ maximum))))
           (<= (find-alternative-skip s i maximum quiet)
               maximum))
  :rule-classes :linear)

(defthm find-alternative-start1-bound-2
  (implies (and (natp maximum)
                (natp i))
           (<= (- maximum)
               (find-alternative-start1 x s i maximum quiet)))
  :rule-classes :linear)

(verify-guards find-alternative-start1)

(verify-termination find-alternative-start) ; and guards

; Start termination and guards for find-alternative-stop, based on events above
; for find-alternative-skip.

(verify-termination find-alternative-stop
  (declare (xargs :verify-guards nil)))

(defthm find-alternative-stop-increases-1
  (implies (not (equal (1+ maximum) (find-alternative-stop s i maximum quiet)))
           (<= i (find-alternative-stop s i maximum quiet)))
  :rule-classes :linear)

(defthm find-alternative-stop-increases-2
  (implies (<= i maximum)
           (<= i (find-alternative-stop s i maximum quiet)))
  :rule-classes :linear)

(defthm find-alternative-stop-bound
  (<= (find-alternative-stop s i maximum quiet)
      (1+ maximum))
  :rule-classes :linear)

(defthm natp-find-alternative-stop
  (implies (and (natp i)
                (natp maximum))
           (natp (find-alternative-stop s i maximum quiet)))
  :rule-classes :type-prescription)

(verify-guards find-alternative-stop)

; Start termination and guards for scan-past-whitespace.

(verify-termination scan-past-whitespace
  (declare (xargs :verify-guards nil)))

(defthm natp-scan-past-whitespace
  (implies (and (natp i)
                (natp maximum))
           (natp (scan-past-whitespace s i maximum)))
  :rule-classes :type-prescription)

(defthm scan-past-whitespace-bound
  (implies (and (integerp i)
                (integerp maximum))
           (<= (scan-past-whitespace s i maximum) maximum))
  :rule-classes :linear)

(verify-guards scan-past-whitespace)

; Start termination and guards for fmx-cw-fn etc.

(defthm character-alistp-append
  (implies (true-listp x)
           (equal (character-alistp (append x y))
                  (and (character-alistp x)
                       (character-alistp y)))))

(verify-termination fmx-cw-msg-1) ; and guards
(verify-termination fmx-cw-msg) ; and guards
(verify-termination fmx-cw-fn-guard) ; and guards
(verify-termination fmx-cw-fn) ; and guards
(verify-termination fmx!-cw-fn) ; and guards

; Support for guard verification for fmx-cw and fmx!-cw calls.

(defthm fmx-cw-msg-1-opener

; It seems very unlikely that this rule will loop, given its syntaxp
; hypothesis.  If that happens, then of course one can simply disable it.

; It also seems that it could be helpful to increase applicability of this rule
; by removing (quotep i) from the syntaxp hypothesis, perhaps at the risk of
; incraseing the chance of looping.  Time will tell.  This lemma might be one
; for users to modify.

  (implies (syntaxp (and (quotep s) (quotep i)))
           (equal (fmx-cw-msg-1 s alist i maximum clk)
                  (fmx-cw-msg-1-body)))
  :hints (("Goal"
           :expand
           ((:free (clk) (fmx-cw-msg-1 s alist i maximum clk))))))

;;; Example of guard verification for an fmx-cw call.
(local (defun test1 (x)
         (declare (xargs :guard (true-listp x)))
         (fmx-cw "ab~&0cd" x)))

;;; Example of guard verification for an fmx-cw call.
(local (defun test2 (x)
         (declare (xargs :guard t))
         (fmx!-cw "~@0" (msg "Hello~|~x0~|" x))))
