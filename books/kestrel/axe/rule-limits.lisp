; Limiting how many times a rule can fire
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "stored-rules")
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)

;; The rule-limits is a map from rule names to the number of additional times we can try them
(defund rule-limitsp (limits)
  (declare (xargs :guard t))
  (and (symbol-alistp limits)
       ;; may go negative if we exhaust the limit when relieving hyps and the decrement once more:
       (all-integerp (strip-cdrs limits))))

;; LIMITS is an alist that maps rule names to natural numbers (the number of
;; allowed rule applications remaining). Usually LIMITS will be nil, or at
;; least a very small alist.
(defund limit-reachedp (stored-rule limits print)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep
                                                           rule-limitsp)))))
  (let* ((rule-symbol (stored-rule-symbol stored-rule))
         (res (assoc-eq rule-symbol limits)))
    (if (not res)
        nil ;limit not reached since there is no limit for this rule
      (let ((limit (rfix (cdr res)))) ;todo: drop the rfix
        (if (<= limit 0)
            (prog2$ (and print (cw "(NOTE: Limit reached for rule ~x0.)~%" rule-symbol))
                    t)
          nil)))))

;; this repeats some work done in limit-reachedp
(defund decrement-rule-limit (stored-rule limits)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep
                                                           rule-limitsp)))))
  (let* ((rule-symbol (stored-rule-symbol stored-rule))
         (res (assoc-eq rule-symbol limits)))
    (if (not res)
        limits
      (let ((limit (cdr res)))
        ;todo: drop the rfix
        (acons rule-symbol (+ -1 (rfix limit)) limits))))) ;todo: could delete the old pair in the alist

(defthm rule-limitsp-of-decrement-rule-limit
  (implies (and (rule-limitsp limits)
                ;; (not (limit-reachedp stored-rule limits))
                (stored-axe-rulep stored-rule))
           (rule-limitsp (decrement-rule-limit stored-rule limits)))
  :hints (("Goal" :in-theory (enable decrement-rule-limit rule-limitsp LIMIT-REACHEDP))))
