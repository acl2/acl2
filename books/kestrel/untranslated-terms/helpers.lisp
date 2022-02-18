; Helper functions for manipulating untranslated terms
;
; Copyright (C) 2021-2022 Kestrel Institute
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

(defun supported-b*-bindingp (binding)
  (declare (xargs :guard t))
  (and (true-listp binding)
       (consp binding)
       (let ((binder (first binding)))
         (if (atom binder)
             (or (eq binder '-) ; (- <term> ... <term>) for any number of terms
                 (and (symbolp binder) ; (<var> <term)
                      (= 1 (len (fargs binding)))))
           (case (car binder)
             ((when if unless) (= 1 (len (fargs binder)))) ; ((when <term>) <term> ... <term>)
             (mv (and (symbol-listp (fargs binder)) ; ((mv <var> ... <var>) <term>)
                      (= 1 (len (fargs binding)))))
             ;; todo: add more kinds of supported binder
             (otherwise nil))))))

(defun supported-b*-bindingsp (bindings)
  (declare (xargs :guard t))
  (if (atom bindings)
      (null bindings)
    (and (supported-b*-bindingp (first bindings))
         (supported-b*-bindingsp (rest bindings)))))

(defund extract-terms-from-b*-binding (binding)
  (declare (xargs :guard (supported-b*-bindingp binding)))
  (let ((binder (first binding)))
    (if (symbolp binder)
        (if (eq binder '-) ; (- <term> ... <term>) for any number of terms
            (fargs binding)
          ;; it's a variable:
          (list (farg1 binding)))
      (case (car binder)
        ((when if unless) (cons (farg1 binder) (fargs binding)))
        (mv (list (farg1 binding)))
        ;; Should never happen:
        (t (er hard 'extract-terms-from-b*-binding "Unsupported b* binder: ~x0." binding))))))

(defthm true-listp-of-extract-terms-from-b*-binding
  (implies (supported-b*-bindingp binding)
           (true-listp (extract-terms-from-b*-binding binding)))
  :hints (("Goal" :in-theory (enable extract-terms-from-b*-binding))))

;; Extracts all the terms in the b* bindings, in order
(defun extract-terms-from-b*-bindings (bindings)
  (declare (xargs :guard (supported-b*-bindingsp bindings)))
  (if (endp bindings)
      nil
    (append (extract-terms-from-b*-binding (first bindings))
            (extract-terms-from-b*-bindings (rest bindings)))))

;; Returns (mv new-binding rest-new-terms).
(defun recreate-b*-binding (binding new-terms)
  (declare (xargs :guard (and (supported-b*-bindingp binding)
                              (true-listp new-terms))))
  (let* ((binder (first binding)))
    (if (symbolp binder)
        (if (eq binder '-) ; (- <term> ... <term>) for any number of terms
            (let ((num-terms (len (fargs binding))))
              (mv `(,binder ,@(take num-terms new-terms))
                  (nthcdr num-terms new-terms)))
          ;; it's a variable:
          (mv `(,binder ,(first new-terms)) ; (<var> <term)
              (rest new-terms)))
      (case (car binder)
        ((when if unless) ; ((when <term>) <term> ... <term>)
         (let ((num-args (len (fargs binding))))
           (mv `((,(car binder) ,(first new-terms)) ,@(take num-args (rest new-terms)))
               (nthcdr (+ 1 num-args) new-terms))))
        (mv ; ((mv <var> ... <var>) <term>)
         (mv `((mv ,@(fargs binder)) ,(first new-terms))
             (rest new-terms)))
        ;; Should never happen:
        (otherwise (progn$ (er hard 'recreate-b*-binding "Unsupported b* binder: ~x0." binding)
                           (mv nil nil)))))))

(defun recreate-b*-bindings (bindings new-terms)
  (declare (xargs :guard (and (supported-b*-bindingsp bindings)
                              (true-listp new-terms))))
  (if (endp bindings)
      nil
    (mv-let (new-first new-terms)
      (recreate-b*-binding (first bindings) new-terms)
      (let ((new-rest (recreate-b*-bindings (rest bindings) new-terms)))
        (cons new-first new-rest)))))
