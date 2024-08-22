; A stobj to gather parameters used in rewriting
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Unlike rewrite-stobj, this includes values, such as the DAG, that change during rewriting.  So it has to be returned by most functions.

(include-book "kestrel/utilities/defstobj-plus" :dir :system)

(include-book "wf-dagp") ; reduce, or apply this as an invariant over the fields

(defstobj+ rewrite-stobj2
  ;; Functions that are known to be boolean in the current world:
  (dag-array :type t :initially nil) ; todo: strenghthen preds?
  (dag-len :type (satisfies natp) ; using (integer 0 *) led to guards and theorems that didn't mention natp
           :initially 0)
  (the-dag-parent-array :type t :initially nil)
  ;; we add "the-" to the names to avoid name clashes:
  (the-dag-constant-alist :type (satisfies dag-constant-alistp) :initially nil)
  (the-dag-variable-alist :type (satisfies dag-variable-alistp) :initially nil)
  :inline t
  :renaming ((dag-array get-dag-array)
             (update-dag-array put-dag-array)

             (dag-len get-dag-len)
             (update-dag-len put-dag-len)

             (the-dag-parent-array get-dag-parent-array)
             (update-the-dag-parent-array put-dag-parent-array)

             (the-dag-constant-alist get-dag-constant-alist)
             (update-the-dag-constant-alist put-dag-constant-alist)

             (the-dag-variable-alist get-dag-variable-alist)
             (update-the-dag-variable-alist put-dag-variable-alist)))

;; todo: use this more
;; disable?
(defun wf-rewrite-stobj2 (rewrite-stobj2)
  (declare (xargs :stobjs rewrite-stobj2))
  (wf-dagp 'dag-array (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) 'dag-parent-array (get-dag-parent-array rewrite-stobj2) (get-dag-constant-alist rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2)))

(include-book "dag-array-builders")

;; returns (mv erp nodenum rewrite-stobj2)
;; todo: disable
(defun add-variable-to-dag-array-in-stobj (var rewrite-stobj2)
  (declare (xargs :guard (and (symbolp var)
                              (wf-rewrite-stobj2 rewrite-stobj2))
                  :stobjs rewrite-stobj2))
  (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-variable-alist)
    (add-variable-to-dag-array var (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) (get-dag-parent-array rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2))
    (if erp
        (mv erp 0 rewrite-stobj2)
      (let* ((rewrite-stobj2 (put-dag-array dag-array rewrite-stobj2))
             (rewrite-stobj2 (put-dag-len dag-len rewrite-stobj2))
             (rewrite-stobj2 (put-dag-parent-array dag-parent-array rewrite-stobj2))
           ;; (rewrite-stobj2 (put-dag-constant-alist dag-constant-alist rewrite-stobj2))
             (rewrite-stobj2 (put-dag-variable-alist dag-variable-alist rewrite-stobj2)))
        (mv nil nodenum rewrite-stobj2)))))

(defthm add-variable-to-dag-array-in-stobj-return-type
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))) ; no error
                (symbolp var)
                (wf-rewrite-stobj2 rewrite-stobj2))
           (and (natp (mv-nth 1 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))
                (wf-rewrite-stobj2 (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))
                (< (mv-nth 1 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))
                   (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-in-stobj))))


;; rule for (WF-DAGP 'DAG-ARRAY (GET-DAG-ARRAY REWRITE-STOBJ2) (GET-DAG-LEN REWRITE-STOBJ2) 'DAG-PARENT-ARRAY (GET-DAG-PARENT-ARRAY REWRITE-STOBJ2) (GET-DAG-CONSTANT-ALIST REWRITE-STOBJ2) (GET-DAG-VARIABLE-ALIST REWRITE-STOBJ2))
