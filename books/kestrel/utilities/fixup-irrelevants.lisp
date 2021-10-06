(in-package "ACL2")

(include-book "std/system/irrelevant-formals" :dir :system)
(include-book "declares0")
(include-book "defun-forms")
(include-book "mutual-recursion-forms")

;; TODO: Doesn't currently work right for mutual-recursion, due to bug in
;; irrelevant-formals-info.

;; Returns the new defun-form.
(defund set-irrelevant-declare-in-defun-form (defun-form irrelevant-formals)
  (declare (xargs :guard (and (symbol-listp irrelevant-formals)
                              (defun-formp defun-form))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun-form))
         (declares (set-irrelevant-declare-in-declares irrelevant-formals declares))
         (defun-form (replace-declares-in-defun defun-form declares)))
    defun-form))

;; Irrelevant formals can depend on the ignore declares, so set those first.
(defun fixup-irrelevants-in-defun-form (defun-form
                                         state ;todo: reduce to just world?
                                         )
  (declare (xargs :guard (defun-formp defun-form)
                  :mode :program
                  :stobjs state))
  (let* ((irrelevant-formals (irrelevant-formals-info defun-form)))
    (set-irrelevant-declare-in-defun-form defun-form irrelevant-formals)))

(defun set-irrelevant-declares-in-defun-forms (defun-forms name-to-irrelevant-formals-alist)
  (declare (xargs :guard (and (all-defun-formp defun-forms)
                              (true-listp defun-forms)
                              (symbol-alistp name-to-irrelevant-formals-alist)
                              (symbol-list-listp (strip-cdrs name-to-irrelevant-formals-alist)))))
  (if (endp defun-forms)
      nil
    (let* ((defun-form (first defun-forms))
           (name (get-name-from-defun defun-form))
           (irrelevant-formals (cdr (assoc-eq name name-to-irrelevant-formals-alist)))
           (defun-form (set-irrelevant-declare-in-defun-form defun-form irrelevant-formals)))
      (cons defun-form (set-irrelevant-declares-in-defun-forms (rest defun-forms) name-to-irrelevant-formals-alist)))))

(defun fixup-irrelevants-in-mutual-recursion (mut-rec
                                              state ;todo: reduce to just world?
                                              )
  (declare (xargs :guard (mutual-recursion-formp mut-rec)
                  :mode :program
                  :stobjs state))
  (let* ((name-to-irrelevant-formals-alist (irrelevant-formals-info mut-rec)))
    (set-irrelevant-declares-in-defun-forms (cdr mut-rec) name-to-irrelevant-formals-alist)))
