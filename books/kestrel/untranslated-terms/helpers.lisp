; Helper functions for manipulating untranslated terms
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../utilities/acl2-defaults-table")
(include-book "kestrel/utilities/forms" :dir :system) ; for farg1, etc.

;move
;clash
;similar to flatten
;; The CLAUSES can have length 1 or 2.  All we have to do is flatten.
;; Doesn't require the lists to be true-lists -- todo: why not?
;; TODO: Better guard
(defun extract-terms-from-cond-clauses (clauses)
  (declare (xargs :guard (true-listp clauses)))
  (if (endp clauses)
      nil
    (append (true-list-fix (first clauses))
            (extract-terms-from-cond-clauses (rest clauses)))))

;; Sets the ignore-ok property in WRLD to t.
;; Returns a new world.
(defund set-ignore-ok-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (putprop 'acl2-defaults-table
           'table-alist
           (acons :ignore-ok t (acl2-defaults-table-alist wrld))
           wrld))

;; Dumb replacement, without trying to determine whether symbols are vars,
;; function names, stuff passed to macros, etc.  TODO: Maybe stop if 'QUOTE is
;; encountered?
(defun replace-symbols-in-tree (tree alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (if (atom tree)
      (if (symbolp tree)
          ;; Attempt to replace the symbol using the alist:
          (let ((res (assoc-eq tree alist)))
            (if res
                (cdr res)
              tree))
        ;; Non-symbol atom:
        tree)
    ;; TREE must be a cons:
    (cons (replace-symbols-in-tree (car tree) alist)
          (replace-symbols-in-tree (cdr tree) alist))))

;; Replace the terms in the CLAUSES with the corresponding NEW-TERMS, which
;; come in order and correspond to the terms in the existing CLAUSES.  Note
;; that each element of CLAUSES may have length 1 or 2.
(defun recreate-cond-clauses (clauses new-terms)
  (if (endp clauses)
      nil
    (let* ((clause (first clauses))
           (clause-len (len clause)) ;can be 1 or 2
           )
      (cons (take clause-len new-terms) ; the new clause
            (recreate-cond-clauses (rest clauses)
                                   (nthcdr clause-len new-terms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
