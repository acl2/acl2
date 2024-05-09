; Utilities involving tables
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Since TABLE and related functions can't be called from code.
;; Returns a new world.
;; TODO: What if the table has a guard?
(defun table-programmatic (table-name key-name value wrld)
  (declare (xargs :guard (and (symbolp table-name)
                              ;; no constraint on the key?
                              ;; no constraint on the value
                              (plist-worldp wrld))))
  (let ((old-alist (table-alist table-name wrld)))
    (if (not (alistp old-alist))
        (er hard? 'table-programmatic "Table-alist for ~x0 is not an alist: ~x1." table-name old-alist)
      (putprop table-name
               'table-alist
               (put-assoc-equal key-name value old-alist)
               wrld))))

;; Overwrites the entire table named TABLE-NAME with ALIST.
;; Returns an error triple, (mv erp val state).
(defun overwrite-table-programmatic (table-name alist state)
  (declare (xargs :mode :program :stobjs state))
  (with-output! :off :all ; silence TABLE-FN (Is this needed?)
    (table-fn table-name
              (list nil (kwote alist) :clear)
              state
              `(table ,table-name nil ',alist :clear))))

;; Sets KEY to VALUE in the table whose name is TABLE-NAME.
;; Returns an error triple, (mv erp val state).
(defun set-table-entry-programmatic (table-name key value state)
  (declare (xargs :guard (symbolp table-name) ; keys and values can be anything
                  :mode :program :stobjs state))
  (with-output! :off :all ; silence TABLE-FN (Is this needed?)
    (table-fn table-name
              (list (kwote key) (kwote value))
              state
              `(table ,table-name nil ',key ',value))))
