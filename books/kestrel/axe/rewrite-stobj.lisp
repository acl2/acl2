; A stobj to gather data structures used in rewriting
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "interpreted-function-alistp")
(include-book "rule-alists")

;; Note that none of the information in the rewrite-stobj changes during
;; rewriting, so the stobj does not have to be returned by the functions in the
;; main rewriter clique.

;; See also rewrite-stobj2.lisp, for a stobj that includes fields that do change.

;; TODO: Consider adding more things to this?

(defstobj+ rewrite-stobj
  ;; Functions that are known to be boolean in the current world:
  (known-booleans :type (satisfies symbol-listp) :initially nil)
  ;; Names of rules we are monitoring:
  (monitored-symbols :type (satisfies symbol-listp) :initially nil)
  ;; How much to print while rewriting:
  (print :type (satisfies print-levelp) :initially nil)
  ;; Whether to use our special-purpose code to normalize nests of XORs:
  (normalize-xors :type (satisfies booleanp) :initially nil)
  ;; Definitions of functions not built into the evaluator:
  ;; TODO: Require this alist to be complete?
  (interpreted-function-alist :type (satisfies interpreted-function-alistp) :initially nil)
  ;; Rules to be applied when rewriting, stored as a rule-alist:
  (rule-alist :type (satisfies rule-alistp) :initially nil)
  ;; Functions to elide when printing failure info for monitored rules (e.g.,
  ;; when printing the refined-assumption-alist, which can include large
  ;; terms):
  (fns-to-elide :type (satisfies symbol-listp) :initially nil)
  :inline t
  ;; Changes the names to be get-XXX and put-XXX:
  :renaming ((known-booleans get-known-booleans)
             (update-known-booleans put-known-booleans)
             (monitored-symbols get-monitored-symbols)
             (update-monitored-symbols put-monitored-symbols)
             (common-lisp::printp printp) ; can we avoid having defstobj define printp, which just calls print-levelp?
             (common-lisp::print get-print)
             (common-lisp::update-print put-print)
             (normalize-xors get-normalize-xors)
             (update-normalize-xors put-normalize-xors)
             (interpreted-function-alistp interpreted-function-alist-fieldp) ; since interpreted-function-alistp is already used!  can we suppress the recognizer in this case?
             (interpreted-function-alist get-interpreted-function-alist)
             (update-interpreted-function-alist put-interpreted-function-alist)
             (rule-alistp rule-alist-fieldp) ; since rule-alistp is already used!  can we suppress the recognizer in this case?
             (rule-alist get-rule-alist)
             (update-rule-alist put-rule-alist)
             (fns-to-elide get-fns-to-elide)
             (update-fns-to-elide put-fns-to-elide)))

;; In case we turn off tau.
(defthm true-listp-of-get-monitored-symbols
  (implies (rewrite-stobjp rewrite-stobj)
           (true-listp (get-monitored-symbols rewrite-stobj)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rewrite-stobjp get-monitored-symbols))))
