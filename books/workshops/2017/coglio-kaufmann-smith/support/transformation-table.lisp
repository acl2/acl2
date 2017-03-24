(in-package "ACL2")

;; A table to store transformations, to check for redundancy:

(defun get-transformation-table (state)
  (declare (xargs :stobjs state))
  (table-alist 'transformation-table (w state)))

;; Returns the event that this transformation-form yielded last time, if any.
;; Otherwise, returns nil.
(defun previous-transformation-expansion (transformation-form state)
  (declare (xargs :stobjs state))
  (let* ((table-alist (get-transformation-table state)))
    (if (not (alistp table-alist))
        (hard-error 'previous-transformation-expansion "Invalid table alist for transformation-table: ~x0."
                    (acons #\0 table-alist nil))
      (let ((res (assoc-equal transformation-form table-alist)))
        (if res
            (prog2$ (cw "NOTE: The transformation ~x0 is redundant.~%" transformation-form)
                    (cdr res))
          ;; No previous occurrence of this transformation:
          nil)))))
