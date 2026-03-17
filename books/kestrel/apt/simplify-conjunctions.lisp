; A transformation to simplify conjunctions in function bodies
;
; Copyright (C) 2022-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: Use APT package?

;; TODO: Handle conjunctions not at the top-level of the body.

;; TODO: Make the proof more automatic/robust.

(include-book "utilities/def-equality-transformation")
(include-book "kestrel/axe/rewriter-basic" :dir :system)
(include-book "kestrel/utilities/directed-untranslate-dollar" :dir :system)
(local (include-book "kestrel/terms-light/all-fnnames1" :dir :system))

;; The core function for simplify-conjunctions.  Such functions always take:
;; fn, untranslated-body, state, and then transformation-specific args (none
;; for simplify-conjunctions).
(defun simplify-conjunctions-function-body-transformer (fn
                                                        untranslated-body
                                                        state
                                                        ;; extra-function-renaming
                                                        untranslate
                                                        )
  (declare (xargs :guard (and (symbolp fn)
                              ;; (doublet-listp extra-function-renaming)
                              (member-eq untranslate '(t nil :nice))
                              )
                  :stobjs state
                  :mode :program ;; because of translate
                  )
           (ignore fn))
  (b* ((wrld (w state))
       (translated-body (translate-term untranslated-body 'simplify-conjunctions-function-body-transformer wrld)) ; todo: untranslate later
       (conjuncts (get-conjuncts-of-term2 translated-body))
       ;; todo: handle conjunctions not at the top level:
       ((mv erp new-conjuncts &) (simplify-conjunction-basic conjuncts
                                                             nil ; rule-alist
                                                             (known-booleans wrld)
                                                             nil ; monitored-symbols
                                                             nil ; no-warn-ground-functions
                                                             nil ; memoizep
                                                             nil ; count-hits
                                                             t ; warn-missingp
                                                             ))
       ((when erp) (er hard? 'simplify-conjunctions-function-body-transformer "Error simplifying conjunctions: ~x0." erp))
       (new-body (if nil ;; (perm new-conjuncts conjuncts) ;todo: get this to work, but consider duplicate removal when getting conjuncts
                     (prog2$ (cw "No change!~%")
                             untranslated-body ; no change! todo: supporting making this an error
                             )
                   (let ((new-body (make-conjunction-from-list new-conjuncts)))
                     (if (eq nil untranslate)
                         new-body ;TODO clean up macros at least?  clean up mvs too?
                       (if (eq t untranslate)
                           (untranslate new-body nil wrld)
                         (directed-untranslate$ new-body untranslated-body wrld)))))))
    new-body))

(defund simplify-conjunctions-enables (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (b* ((body (fn-body fn t wrld))
       (fns (all-fnnames body)))
    ;; enable the :executable-counterpart of every function in the body:
    (make-doublets (repeat (len fns) :executable-counterpart) fns)))

(def-equality-transformation
  simplify-conjunctions ; name of the transformation to create
  simplify-conjunctions-function-body-transformer ; core function to transform a function body
  (;extra-function-renaming ; required arg, can't be called "function-renaming" since there already is one (TODO: maybe rename the other one to "recursive-call-renaming")
   )
  ((untranslate 't))                       ; keyword args and defaults
  :enables (simplify-conjunctions-enables fn (w state)) ; form to compute the enables for the 'becomes theorem' ; TODO: Allow the function-body-transformer to return pre-events and hints?
  :short "Simplify conjunctions in a function using the Axe Rewriter."
  ;; todo: put this sort of thing in automatically?:
  :description "<p>To inspect the resulting forms, call @('show-simplify-conjunctions') on the same
arguments.</p>"
  :transform-specific-arg-descriptions
  ;; TODO: Think about the best way to specify which functions to rename, what they get renamed to (if mulitple options exist) and how to find the corresponding rules.
  (;; (extra-function-renaming "The renaming to apply to called functions (each entry should have a corresponding entry in the renaming-rule-table).")
   (untranslate "How to untranslate the function body after changing it.")
   ))
