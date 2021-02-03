; A tool to make sure certain theorems exist
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/theorem-symbolp" :dir :system) ;todo: reduce?

;;;
;;; ensure-rules-known
;;;

;; Throws an error if RULE-NAME is not an existing theorem or function (i.e., a
;; "definition" rule) in WRLD.
(defun ensure-rule-known (rule-name wrld)
  (declare (xargs :guard (and (symbolp rule-name)
                              (ilks-plist-worldp wrld))))
  (let* (;; ((when (eq 'quote rule-name))
       ;;  (er hard? 'ensure-rule-known "QUOTE is an illegal name for an Axe rule."))
       ;; TODO: Actually, I can make an ACL2 theorem called QUOTE
       (theoremp (theorem-symbolp rule-name wrld))
       (functionp (function-symbolp rule-name wrld)))
    (if (or functionp theoremp)
        :ok
      (er hard? 'ensure-rule-known "~x0 does not seem to be a theorem or defun." rule-name))))

;; Throws an error if any of the RULE-NAMES is not an existing theorem or
;; function (i.e., a "definition" rule) in WRLD.
(defun ensure-rules-known-fn (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-names)
      :ok
    (and (ensure-rule-known (first rule-names) wrld)
         (ensure-rules-known-fn (rest rule-names) wrld))))

;; Throws an error if any of the RULE-NAMES is not an existing theorem or
;; function (i.e., a "definition" rule).
;; TODO: Compare to ENSURE-ALL-THEOREMSP
(defmacro ensure-rules-known (rule-names)
  `(assert-event (ensure-rules-known-fn ,rule-names (w state))))
