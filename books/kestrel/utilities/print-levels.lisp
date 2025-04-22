; Print verbosity levels
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider using numeric print levels for faster comparison

(defund print-levelp (print-level)
  (declare (xargs :guard t))
  (if (member-eq print-level '(nil ; don't print
                               :brief
                               t ; print normally
                               :verbose
                               :verbose!
                               ))
      t
    nil))

(defthm print-levelp-forward-to-symbolp
  (implies (print-levelp print-level)
           (symbolp print-level))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable print-levelp))))

;; Not strictly boolean despite the name ending in p, to be used in a boolean context
(defund-inline print-level-at-least-briefp (print-level)
  (declare (xargs :guard (print-levelp print-level)))
  (if print-level t nil) ; anything non-nil is at least :brief
  )

(defund-inline print-level-at-least-tp (print-level)
  (declare (xargs :guard (print-levelp print-level)))
  (if (member-eq print-level '(t :verbose :verbose!)) t nil))

(defund-inline print-level-at-least-verbosep (print-level)
  (declare (xargs :guard (print-levelp print-level)))
  (if (member-eq print-level '(:verbose :verbose!)) t nil))

;; (defund-inline print-level-at-least-verbose!p (print-level)
;;   (declare (xargs :guard (print-levelp (print-level))))
;;   (eq print-level ':verbose!))

(defund reduce-print-level (print-level)
  (declare (xargs :guard (print-levelp print-level)
                  :guard-hints (("Goal" :in-theory (enable print-levelp)))))
  (cond
    ((eq nil print-level) nil)
    ((eq :brief print-level) nil)
    ((eq t print-level) :brief)
    ((eq :verbose print-level) t)
    ((eq :verbose! print-level) :verbose)
    (t (er hard 'reduce-print-level "Bad print level: ~x0." print-level))))

(defthm print-levelp-of-reduce-print-level
  (implies (print-levelp print-level)
           (print-levelp (reduce-print-level print-level)))
  :hints (("Goal" :in-theory (enable reduce-print-level
                                     print-levelp))))
