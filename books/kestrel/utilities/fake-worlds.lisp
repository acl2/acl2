; Creating worlds with fake entries for functions not yet defined
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-var-names")

;; The main use case for this is so that you can translate terms that call
;; functions that are not yet defined.

(defun fn-arities (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp-with-formals wrld))))
  (if (endp names)
      nil
    (cons (nfix (arity (first names) wrld)) ;todo: drop the nfix (would require everything to be defined)
          (fn-arities (rest names) wrld))))

;; Extends WRLD with a fake entry for each function in the ALIST, giving it a
;; 'FORMALS property.  ALIST maps function symbols to arities.  The length of
;; each new fake 'FORMALS property is the arity associated with the function in
;; the ALIST.
(defun add-fake-fns-to-world (name-to-arity-alist wrld)
  (declare (xargs :guard (and (symbol-alistp name-to-arity-alist)
                              (nat-listp (strip-cdrs name-to-arity-alist))
                              (plist-worldp wrld))))
  (if (endp name-to-arity-alist)
      wrld
    (let* ((pair (first name-to-arity-alist))
           (fn (car pair))
           (arity (cdr pair))
           ;; the names of the formals don't matter:
           (wrld (putprop fn 'formals (make-var-names arity 'fake-formal) wrld)))
      (add-fake-fns-to-world (rest name-to-arity-alist) wrld))))
