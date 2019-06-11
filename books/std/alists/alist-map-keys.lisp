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

(local (include-book "std/alists/remove-assoc-equal" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc alist-map-keys
  :parents (std/alists alists)
  :short "Keys of the map represented by an alist."
  :long
  (xdoc::topstring
   (xdoc::codeblock
    "General Forms:"
    "(alist-map-keys alist)"
    "(alist-map-keys alist :test 'eql)   ; same as above (eql as equality test)"
    "(alist-map-keys alist :test 'eq)    ; same, but eq is equality test"
    "(alist-map-keys alist :test 'equal) ; same, but equal is equality test")
   (xdoc::p
    "This returns the ordered list of keys of the alist,
     after removing any shadowed pairs.
     When an alist represents a map, any shadowed pairs are irrelevant.
     This function is similar to @(tsee strip-cars) and @(tsee alist-keys),
     except that these two may return lists with duplicates,
     which @('alist-map-keys') always returns a list without duplicates.
     This function is a companion of @(tsee alist-map-vals).")
   (xdoc::p
    "The optional keyword, @(':test'), has no effect logically,
     but provides the test (default @(tsee eql)) used for comparing
     the keys of the alist in order to remove shadowed pairs.")
   (xdoc::p
    "The @(see guard) for a call of @('alist-map-keys') depends on the test.
     In all cases, the argument must satisfy @(tsee alistp).
     If the test is @(tsee eql),
     the argument must satisfy @(tsee eqlable-alistp).
     If the test is @(tsee eq),
     the argument must satisfy @(tsee symbol-alistp).")
   (xdoc::p
    "See @(see equality-variants) for a discussion of
     the relation between @('alist-map-keys') and its variants:")
   (xdoc::blockquote
    (xdoc::p
     "@('(alist-map-keys-eq alist)') is equivalent to
      @('(alist-map-keys alist :test 'eq)');")
    (xdoc::p
     "@('(alist-map-keys-equal alist)') is equivalent to
      @('(alist-map-keys alist :test 'equal)')."))
   (xdoc::p
    "In particular, reasoning about any of these primitives
     reduces to reasoning about the function @('alist-map-keys-equal').")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection alist-map-keys-functions-and-macros
  :parents (alist-map-keys)
  :short "Definitions of the @(tsee alist-map-keys) functions and macros,
          and basic theorems about them."

  ;; definitions:

  (defun alist-map-keys-equal (alist)
    (declare (xargs :guard (alistp alist)))
    (cond ((endp alist) nil)
          (t (let ((key (caar alist)))
               (cons key (alist-map-keys-equal
                          (remove-assoc-equal key (cdr alist))))))))

  (defun-with-guard-check alist-map-keys-eq-exec (alist)
    (symbol-alistp alist)
    (cond ((endp alist) nil)
          (t (let ((key (caar alist)))
               (cons key (alist-map-keys-eq-exec
                          (remove-assoc-eq key (cdr alist))))))))

  (defun-with-guard-check alist-map-keys-eql-exec (alist)
    (eqlable-alistp alist)
    (cond ((endp alist) nil)
          (t (let ((key (caar alist)))
               (cons key (alist-map-keys-eql-exec
                          (remove-assoc-eql-exec key (cdr alist))))))))

  (defmacro alist-map-keys (alist &key (test ''eql))
    (declare (xargs :guard (or (equal test ''eq)
                               (equal test ''eql)
                               (equal test ''equal))))
    (cond
     ((equal test ''eq)
      `(let-mbe ((alist ,alist))
                :logic (alist-map-keys-equal alist)
                :exec  (alist-map-keys-eq-exec alist)))
     ((equal test ''eql)
      `(let-mbe ((alist ,alist))
                :logic (alist-map-keys-equal alist)
                :exec  (alist-map-keys-eql-exec alist)))
     (t ; (equal test 'equal)
      `(alist-map-keys-equal ,alist))))

  (defmacro alist-map-keys-eq (alist)
    `(alist-map-keys ,alist :test 'eq))

  ;; basic theorems:

  (defthm alist-map-keys-eq-exec-is-alist-map-keys-equal
    (equal (alist-map-keys-eq-exec alist)
           (alist-map-keys-equal alist)))

  (defthm alist-map-keys-eql-exec-is-alist-map-keys-equal
    (equal (alist-map-keys-eql-exec alist)
           (alist-map-keys-equal alist)))

  ;; these will just rewrite to ALIST-MAP-KEYS-EQUAL:

  (in-theory (disable alist-map-keys-eq-exec alist-map-keys-eql-exec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection alist-map-keys-theorems
  :parents (alist-map-keys)
  :short "Theorems about @(tsee alist-map-keys)."

  (defthm true-listp-of-alist-map-keys-equal
    (implies (alistp alist)
             (true-listp (alist-map-keys-equal alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable alist-map-keys-equal))
