; Standard Association Lists Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection remove-assocs
  :parents (std/alists alists)
  :short "Remove all pairs with given keys from an alist."
  :long
  (xdoc::topstring
   (xdoc::codeblock
    "General Forms:"
    "(remove-assocs keys alist)"
    "(remove-assocs keys alist :test 'eql)   ; same as above (eql as equality test)"
    "(remove-assocs keys alist :test 'eq)    ; same, but eq is equality test"
    "(remove-assocs keys alist :test 'equal) ; same, but equal is equality test")
   (xdoc::p
    "This generalizes @(tsee remove-assoc) to multiple keys.")
   (xdoc::p
    "The optional keyword, @(':test'), has no effect logically,
     but provides the test (default @(tsee eql)) used for comparing
     the keys of the alist with the ones to remove.")
   (xdoc::p
    "The @(see guard) for a call of @('remove-assocs') depends on the test.
     In all cases, the first argument must satisfy @(tsee true-listp)
     and the second argument must satisfy @(tsee alistp).
     If the test is @(tsee eql),
     the first argument must satisfy @(tsee eqlable-listp)
     or the second argument must satisfy @(tsee eqlable-alistp)
     (or both).
     If the test is @(tsee eq),
     the first argument must satisfy @(tsee symbol-listp)
     or the second argument must satisfy @(tsee symbol-alistp)
     (or both).")
   (xdoc::p
    "See @(see equality-variants) for a discussion of
     the relation between @('remove-assocs') and its variants:")
   (xdoc::blockquote
    (xdoc::p
     "@('(remove-assocs-eq keys alist)') is equivalent to
      @('(remove-assocs keys alist :test 'eq)');")
    (xdoc::p
     "@('(remove-assocs-equal keys alist)') is equivalent to
      @('(remove-assocs keys alist :test 'equal)')."))
   (xdoc::p
    "In particular, reasoning about any of these primitives
     reduces to reasoning about the function @('remove-assocs-equal')."))

  ;; definitions:

  (defun remove-assocs-equal (keys alist)
    (declare (xargs :guard (and (true-listp keys) (alistp alist))))
    (cond ((endp alist) nil)
          ((member-equal (car (car alist))
                         keys) (remove-assocs-equal keys (cdr alist)))
          (t (cons (car alist) (remove-assocs-equal keys (cdr alist))))))

  (defun-with-guard-check remove-assocs-eq-exec (keys alist)
    (if (symbol-listp keys)
        (alistp alist)
      (and (true-listp keys)
           (symbol-alistp alist)))
    (cond ((endp alist) nil)
          ((member-eq (car (car alist))
                      keys) (remove-assocs-eq-exec keys (cdr alist)))
          (t (cons (car alist) (remove-assocs-eq-exec keys (cdr alist))))))

  (defun-with-guard-check remove-assocs-eql-exec (keys alist)
    (if (eqlable-listp keys)
        (alistp alist)
      (and (true-listp keys)
           (eqlable-alistp alist)))
    (cond ((endp alist) nil)
          ((member (car (car alist))
                   keys) (remove-assocs-eql-exec keys (cdr alist)))
          (t (cons (car alist) (remove-assocs-eql-exec keys (cdr alist))))))

  (defmacro remove-assocs (keys alist &key (test ''eql))
    (declare (xargs :guard (or (equal test ''eq)
                               (equal test ''eql)
                               (equal test ''equal))))
    (cond
     ((equal test ''eq)
      `(let-mbe ((keys ,keys) (alist ,alist))
                :logic (remove-assocs-equal keys alist)
                :exec  (remove-assocs-eq-exec keys alist)))
     ((equal test ''eql)
      `(let-mbe ((keys ,keys) (alist ,alist))
                :logic (remove-assocs-equal keys alist)
                :exec  (remove-assocs-eql-exec keys alist)))
     (t ; (equal test 'equal)
      `(remove-assocs-equal ,keys ,alist))))

  (defmacro remove-assocs-eq (keys alist)
    `(remove-assocs ,keys ,alist :test 'eq))

  ;; basic theorems:

  (defthm remove-assocs-eq-exec-is-remove-assocs-equal
    (equal (remove-assocs-eq-exec keys alist)
           (remove-assocs-equal keys alist)))

  (defthm remove-assocs-eql-exec-is-remove-assocs-equal
    (equal (remove-assocs-eql-exec keys alist)
           (remove-assocs-equal keys alist)))

  ;; these will just rewrite to REMOVE-ASSOCS-EQUAL:

  (in-theory (disable remove-assocs-eq-exec remove-assocs-eql-exec))

  ;; additional theorems:

  (defthm alistp-of-remove-assocs-equal
    (implies (alistp alist)
             (alistp (remove-assocs-equal keys alist))))

  (defthm symbol-alistp-of-remove-assocs-equal
    (implies (symbol-alistp alist)
             (symbol-alistp (remove-assocs-equal keys alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable remove-assocs-equal))
