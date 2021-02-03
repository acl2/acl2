; A table to store results of transformations, to check for redundancy
;
; Copyright (C) 2016-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "transformation-table")

(defun get-transformation-table (state)
  (declare (xargs :stobjs state))
  (table-alist 'apt::transformation-table (w state)))

;; Returns the event that this transformation-form yielded last time, if any.
;; Otherwise, returns nil.
(defund previous-transformation-expansion (transformation-form state)
  (declare (xargs :stobjs state))
  (let* ((table-alist (get-transformation-table state)))
    (if (not (alistp table-alist))
        (hard-error 'previous-transformation-expansion "Invalid table alist for transformation-table: ~x0."
                    (acons #\0 table-alist nil))
      (let ((res (assoc-equal transformation-form table-alist)))
        (if res
            (prog2$ (cw "The transformation ~x0 is redundant.~%" transformation-form)
                    (cdr res))
          ;; No previous occurrence of this transformation:
          nil)))))

(defund previous-transformation-expansion2 (elaborated-form ;has all required + all optional args, with defaults if not supplied
                                            whole-form ;;the original form submitted
                                            state)
  (declare (xargs :stobjs state))
  (let* ((table-alist (get-transformation-table state)))
    (if (not (alistp table-alist))
        (hard-error 'previous-transformation-expansion "Invalid table alist for transformation-table: ~x0."
                    (acons #\0 table-alist nil))
      (let ((res (assoc-equal elaborated-form table-alist)))
        (if res
            (prog2$ (cw "The transformation ~x0 is redundant.~%" whole-form)
                    (cdr res))
          ;; No previous occurrence of this transformation:
          nil)))))


;not currently used (see email from matt kaufmann about how to do this better)
;; (defun store-transformation-event (transformation-form event state)
;;   (declare (xargs :stobjs state :mode :program))
;;   (TABLE-FN 'apt::transformation-table (list transformation-form event) state :fake-event
;; ;            `(table apt::transformation-table ',transformation-form ',event)
;;             ))
