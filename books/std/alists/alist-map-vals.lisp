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

(defxdoc alist-map-vals
  :parents (std/alists alists)
  :short "Values of the map represented by an alist."
  :long
  (xdoc::topstring
   (xdoc::codeblock
    "General Forms:"
    "(alist-map-vals alist)"
    "(alist-map-vals alist :test 'eql)   ; same as above (eql as equality test)"
    "(alist-map-vals alist :test 'eq)    ; same, but eq is equality test"
    "(alist-map-vals alist :test 'equal) ; same, but equal is equality test")
   (xdoc::p
    "This returns the list of values of the alist,
     after removing any shadowed pairs.
     When an alist represents a map, any shadowed pairs are irrelevant.
     This function is similar to @(tsee strip-cdrs) and @(tsee alist-vals),
     except that these two may return values from shadowed pairs.
     This function is a companion of @(tsee alist-map-keys).
     This function returns the range or image (depending on nomenclature)
     of the map represented by an alist.")
   (xdoc::p
    "The optional keyword, @(':test'), has no effect logically,
     but provides the test (default @(tsee eql)) used for comparing
     the keys of the alist in order to remove shadowed pairs.")
   (xdoc::p
    "The @(see guard) for a call of @('alist-map-vals') depends on the test.
     In all cases, the argument must satisfy @(tsee alistp).
     If the test is @(tsee eql),
     the argument must satisfy @(tsee eqlable-alistp).
     If the test is @(tsee eq),
     the argument must satisfy @(tsee symbol-alistp).")
   (xdoc::p
    "See @(see equality-variants) for a discussion of
     the relation between @('alist-map-vals') and its variants:")
   (xdoc::blockquote
    (xdoc::p
     "@('(alist-map-vals-eq alist)') is equivalent to
      @('(alist-map-vals alist :test 'eq)');")
    (xdoc::p
     "@('(alist-map-vals-equal alist)') is equivalent to
      @('(alist-map-vals alist :test 'equal)')."))
   (xdoc::p
    "In particular, reasoning about any of these primitives
     reduces to reasoning about the function @('alist-map-vals-equal').")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection alist-map-vals-functions-and-macros
  :parents (alist-map-vals)
  :short "Definitions of the @(tsee alist-map-vals) functions and macros,
          and basic theorems about them."

  ;; definitions:

  (defun alist-map-vals-equal (alist)
    (declare (xargs :guard (alistp alist)))
    (cond ((endp alist) nil)
          (t (let* ((pair (car alist))
                    (key (car pair))
                    (val (cdr pair)))
               (cons val (alist-map-vals-equal
                          (remove-assoc-equal key (cdr alist))))))))

  (defun-with-guard-check alist-map-vals-eq-exec (alist)
    (symbol-alistp alist)
    (cond ((endp alist) nil)
          (t (let* ((pair (car alist))
                    (key (car pair))
                    (val (cdr pair)))
               (cons val (alist-map-vals-eq-exec
                          (remove-assoc-eq key (cdr alist))))))))

  (defun-with-guard-check alist-map-vals-eql-exec (alist)
    (eqlable-alistp alist)
    (cond ((endp alist) nil)
          (t (let* ((pair (car alist))
                    (key (car pair))
                    (val (cdr pair)))
               (cons val (alist-map-vals-eql-exec
                          (remove-assoc-eql-exec key (cdr alist))))))))

  (defmacro alist-map-vals (alist &key (test ''eql))
    (declare (xargs :guard (or (equal test ''eq)
                               (equal test ''eql)
                               (equal test ''equal))))
    (cond
     ((equal test ''eq)
      `(let-mbe ((alist ,alist))
                :logic (alist-map-vals-equal alist)
                :exec  (alist-map-vals-eq-exec alist)))
     ((equal test ''eql)
      `(let-mbe ((alist ,alist))
                :logic (alist-map-vals-equal alist)
                :exec  (alist-map-vals-eql-exec alist)))
     (t ; (equal test 'equal)
      `(alist-map-vals-equal ,alist))))

  (defmacro alist-map-vals-eq (alist)
    `(alist-map-vals ,alist :test 'eq))

  ;; basic theorems:

  (defthm alist-map-vals-eq-exec-is-alist-map-vals-equal
    (equal (alist-map-vals-eq-exec alist)
           (alist-map-vals-equal alist)))

  (defthm alist-map-vals-eql-exec-is-alist-map-vals-equal
    (equal (alist-map-vals-eql-exec alist)
           (alist-map-vals-equal alist)))

  ;; these will just rewrite to ALIST-MAP-VALS-EQUAL:

  (in-theory (disable alist-map-vals-eq-exec alist-map-vals-eql-exec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection alist-map-vals-theorems
  :parents (alist-map-vals)
  :short "Theorems about @(tsee alist-map-vals)."

  (defthm true-listp-of-alist-map-vals-equal
    (implies (alistp alist)
             (true-listp (alist-map-vals-equal alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable alist-map-vals-equal))
