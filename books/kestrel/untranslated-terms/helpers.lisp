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
;; Doesn't require the lists to be true-lists
(defun append-all2 (lists)
  (declare (xargs :guard (true-listp lists)))
  (if (endp lists)
      nil
    (append (true-list-fix (first lists))
            (append-all2 (rest lists)))))

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

;; Extract the bodies of the items.  These are the untranslated terms that need to be handled.
;; TODO: What about a decl of (type (satisfies foo)) where perhaps FOO is a function to replace?
(defun extract-terms-from-case-match-cases (cases ;each is either (<pat> <body>) or (<pat> <dcl> <body>).
                                            )
  (declare (xargs :guard (true-list-listp cases)))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (second case) (extract-terms-from-case-match-cases (rest cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (third case) (extract-terms-from-case-match-cases (rest cases)))))))

;; Whenever there is a term in the cases, use the corresponding term from new-terms-from-cases.
(defun recreate-case-match-cases (cases new-terms-from-cases)
  (declare (xargs :guard (and (true-list-listp cases)
                              (true-listp new-terms-from-cases))))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (list (first case) (first new-terms-from-cases))
                (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (list (first case) (second case) (first new-terms-from-cases))
              (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
