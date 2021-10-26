; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Utilities for dealing with the SYNDEF package.

;; Summary:
;; * The SYNDEF package does not import any symbols.
;; * Syntheto definition names, field names, composite type names, parameter
;;   and let-variable def and ref names, are all interned in SYNDEF.
;; * Derived symbols such as SEQ[INT]-P and automatically generated theorems
;;   are interned in the package of the symbol they were derived from, so
;;   they are also in SYNDEF.

;; See package.lsp for more detailed discussion


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "kestrel/utilities/pack" :dir :system)

(defund intern-syndef (str)
  (declare (xargs :guard (stringp str)))
  (intern-in-package-of-symbol str 'syndef::foo))

(defthm symbolp-of-intern-syndef
  (implies (stringp str)
           (symbolp (intern-syndef str)))
  :hints (("Goal" :in-theory (enable intern-syndef))))

(defmacro pack-1 (&rest rst)
  `(acl2::intern-in-package-of-symbol ,(acl2::pack$-fn rst) ,(car rst)))

(defund translate-names (strs)
  (declare (xargs :guard (string-listp strs)))
  (if (endp strs)
      ()
    (cons (intern-syndef (car strs))
          (translate-names (cdr strs)))))

(defthm symbol-listp-of-translate-names
  (implies (string-listp strs)
           (symbol-listp (translate-names strs)))
  :hints (("Goal" :in-theory (enable translate-names))))

;; Get an error if symbol is not in syndef.  This should be used a lot.
(defun err-if-not-in-syndef (symbol)
  (declare (xargs :guard (symbolp symbol)))
  (if (not (equal "SYNDEF" (symbol-package-name symbol)))
      (er hard? 'top-level "Bad package ~x0 for type name ~x1"
          (symbol-package-name symbol) symbol)
    nil))
