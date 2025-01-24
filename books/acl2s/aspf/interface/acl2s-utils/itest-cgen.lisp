#|

Adapted from prove-cgen.lisp and top.lisp in acl2s/cgen

|#

(in-package "CGEN")

(program)
(set-verify-guards-eagerness 1)

(defun itest?-extract-assignment
    (A top-vars elided-var-map counteregp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-doublet-listp A)
                              (implies (consp A) (consp (car A)))
                              (symbol-alistp elided-var-map)
                              (symbol-listp top-vars)
                              (booleanp counteregp))))
  (b* ((top-A (filter-alist-keys A top-vars))
       (vals  (acl2::make-evalable-lst-how 
               (strip-cadrs top-A) 
               (acl2::get-evalable-printing-abstractions state)))
       (?top-A (list-up-lists (strip-cars top-A) vals))
       ((er (list ? top-A)) ;;note that ? here is true if top-A is consistent with the top-level form
        (get-top-level-assignment A top-vars t 
                                        elided-var-map counteregp state))
       (vals  (acl2::make-evalable-lst-how 
               (strip-cadrs top-A) 
               (acl2::get-evalable-printing-abstractions state)))
       (top-A (list-up-lists (strip-cars top-A) vals)))
      (value top-A)))

(defun itest?-extract-assignments 
    (A-lst top-vars elided-var-map counteregp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-alist-listp A-lst)
                              (symbol-listp top-vars)
                              (symbol-alistp elided-var-map)
                              (booleanp counteregp))))
  (if (endp A-lst)
      (value nil)
    (b* (((er r) (itest?-extract-assignment (car A-lst) top-vars
                                     elided-var-map counteregp state))
         ((er Rs) (itest?-extract-assignments (cdr A-lst) top-vars 
                                       elided-var-map counteregp state)))
        (value (cons r Rs)))))

#|

; Old version. The idea of the new version is to collect together all
; the counterexamples and witnesses discovered, not just the ones from
; the last checkpoint and not just the number requested. For example,
; if we requested 3 counterexamples and 3 witnesses, but we found 7
; counterexamples and 3 witnesses, then return everything we found.

(defun itest?-print-cts/wts (s-hist cts-p top-vars state)
  (declare (xargs :stobjs (state)))
  (if (endp s-hist)
      (value nil)
    (b* (((cons ? s-hist-entry%) (car s-hist))
         (test-outcomes% (access s-hist-entry% test-outcomes))
         (A-lst (if cts-p 
                    (access test-outcomes% cts)
                  (access test-outcomes% wts)))
         (elide-map (access s-hist-entry% elide-map))
         ((when (endp A-lst)) 
          (itest?-print-cts/wts (cdr s-hist) cts-p top-vars state)))
      (itest?-extract-assignments A-lst top-vars elide-map cts-p state))))

|#

(defun itest?-print-cts/wts (s-hist cts-p top-vars state)
  (declare (xargs :stobjs (state)))
  (if (endp s-hist)
      (value nil)
    (b* (((cons ? s-hist-entry%) (car s-hist))
         (test-outcomes% (access s-hist-entry% test-outcomes))
         (A-lst (if cts-p 
                    (access test-outcomes% cts)
                  (access test-outcomes% wts)))
         (elide-map (access s-hist-entry% elide-map))
         ((when (endp A-lst)) 
          (itest?-print-cts/wts (cdr s-hist) cts-p top-vars state))
         ((mv & res1 state)
          (itest?-extract-assignments A-lst top-vars elide-map cts-p state))
         ((mv & res2 state)
          (itest?-print-cts/wts (cdr s-hist) cts-p top-vars state)))
      (value (remove-duplicates (append res1 res2) :test 'equal)))))

; adapted from print-testing-summary-fn
(defun extract-cgen (cgen-state state)
  (declare (xargs :stobjs (state)))
  (b* ((s-hist (cget s-hist))
       (gcs%   (cget gcs))
       (vl     (cget verbosity-level)))
      (case-match gcs%
        (('gcs% (& & . &) 
                (& . &))
         (b* ((top-term (cget user-supplied-term))
              (top-vars (all-vars top-term))
              ((er cts) (itest?-print-cts/wts
                         s-hist 
                         T
                         top-vars 
                         state))
              ((er wts) (itest?-print-cts/wts
                         s-hist 
                         nil
                         top-vars 
                         state)))
           (value (list cts wts))))
        (& (value (cw? 
                   (normal-output-flag vl) 
                   "~|ITEST? error: BAD gcs% in cgen-state.~|"))))))
