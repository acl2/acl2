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
          (itest?-print-cts/wts (cdr s-hist) cts-p 
                             top-vars state)))
        (itest?-extract-assignments A-lst top-vars elide-map cts-p state))))

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
              ((er res)  (itest?-print-cts/wts
                          s-hist 
                          T
                          top-vars 
                          state)))
             (value res)))
        (& (value (cw? 
                   (normal-output-flag vl) 
                   "~|ITEST? error: BAD gcs% in cgen-state.~|"))))))
