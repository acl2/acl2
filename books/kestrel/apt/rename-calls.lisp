; A transformation to rename called functions
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: Use APT package?

(include-book "utilities/def-equality-transformation")

;; Produces a list of symbols representing rules to be enabled for proofs.  The
;; rules justify renaming calls of all functions that have been registered in
;; the table.
;; TODO: Or just did the rules about of the world and don't have the table?
(defund rename-calls-enables (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((alist (table-alist 'renaming-rule-table wrld)))
    (if (alistp alist)
        (strip-cdrs alist)
      (er hard? 'rename-calls-enables "Ill-formed renaming-table alist."))))

;; The core function for rename-calls.  Renames calls in the UNTRANSLATED-BODY
;; according to EXTRA-FUNCTION-RENAMING.  (Recursive calls get renamed
;; elsewhere.)  Such functions always take: fn, untranslated-body, state, and
;; then transformation-specific args (none for rename-calls).
(defun rename-calls-function-body-transformer (fn
                                               untranslated-body
                                               state
                                               extra-function-renaming)
  (declare (xargs :guard (and (symbolp fn)
                              (doublet-listp extra-function-renaming))
                  :stobjs state
                  :mode :program)
           (ignore fn))
  (let ((renaming-to-apply (doublets-to-alist extra-function-renaming)))
    (rename-functions-in-untranslated-term untranslated-body renaming-to-apply state)))

(def-equality-transformation
  rename-calls ; name of the transformation to create
  rename-calls-function-body-transformer ; core function to transform a function body
  (extra-function-renaming) ; required arg, can't be called "function-renaming" since there already is one (TODO: maybe rename the other one to "recursive-call-renaming")
  nil                       ; keyword args and defaults
  :enables (rename-calls-enables (w state)) ; form to compute the enables for the 'becomes theorem'
  :short "Change calls made by a function according to the given renaming."
  ;; todo: put this sort of thing in automatically?:
  :description "<p>To inspect the resulting forms, call @('show-rename-calls') on the same
arguments.</p>"
  :transform-specific-arg-descriptions
  ;; TODO: Think about the best way to specify which functions to rename, what they get renamed to (if mulitple options exist) and how to to find the corresponding rules.
  ((extra-function-renaming "The renaming to apply to called functions (each entry should have a corresponding entry in the renaming-rule-table).")))
