; Print verbosity levels
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider using numeric print levels for faster comparison

(defund axe-print-levelp (print-level)
  (declare (xargs :guard t))
  (member-eq print-level '(nil
                           :brief
                           t
                           :verbose
                           :verbose!
                           )))

(defthm axe-print-levelp-forward-to-symbolp
  (implies (axe-print-levelp print-level)
           (symbolp print-level))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-print-levelp))))

;; Not strictly boolean despite the name ending in p, to be used in a boolean context
(defund-inline print-level-at-least-briefp (print-level)
  (declare (xargs :guard (axe-print-levelp print-level)))
  print-level ; anything non-nil is at least :brief
  )

(defund-inline print-level-at-least-tp (print-level)
  (declare (xargs :guard (axe-print-levelp print-level)))
  (member-eq print-level '(t :verbose :verbose!))
  )

(defund-inline print-level-at-least-verbosep (print-level)
  (declare (xargs :guard (axe-print-levelp print-level)))
  (member-eq print-level '(:verbose :verbose!)))

;; (defund-inline print-level-at-least-verbose!p (print-level)
;;   (declare (xargs :guard (axe-print-levelp (print-level))))
;;   (eq print-level ':verbose!))
