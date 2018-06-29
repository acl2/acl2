; Kestrel Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "acceptable-rewrite-rule-p")
(include-book "all-vars-theorems")
(include-book "apply-fn-if-known")
(include-book "arglistp-theorems")
(include-book "assert")
(include-book "auto-instance")
(include-book "auto-termination")
(include-book "characters")
(include-book "copy-def")
(include-book "defchoose-queries")
(include-book "define-sk")
(include-book "defthmr")
(include-book "defmacroq")
(include-book "defun-sk-queries")
(include-book "digits-any-base")
(include-book "digits-any-base-pow2")
(include-book "directed-untranslate")
(include-book "doublets")
(include-book "enumerations")
(include-book "er-soft-plus")
(include-book "error-checking")
(include-book "event-forms")
(include-book "fixbytes/instances")
(include-book "fixbytes/instances-listoflen")
(include-book "fresh-names")
(include-book "include-book-paths")
(include-book "install-not-norm-event")
(include-book "integer-range-fixing")
(include-book "integer-range-lists")
(include-book "integers-from-to")
(include-book "keyword-value-lists")
(include-book "list-set-theorems")
(include-book "list-theorems")
(include-book "magic-macroexpand")
(include-book "make-executable")
(include-book "make-termination-theorem")
(include-book "maybe-msgp")
(include-book "maybe-unquote")
(include-book "minimize-ruler-extenders")
(include-book "named-formulas")
(include-book "nati")
; Skipping the following, because it requires a trust tag:
; (include-book "non-ascii-pathnames" :ttags (:non-ascii-pathnames))
(include-book "numbered-names")
(include-book "orelse")
(include-book "oset-theorems")
(include-book "osets")
(include-book "paired-names")
(include-book "proof-builder-macros")
(include-book "prove-interface")
(include-book "skip-in-book")
(include-book "strings")
(include-book "symbol-symbol-alists")
(include-book "symbol-true-list-alists")
(include-book "symbols")
(include-book "terms")
(include-book "testing")
(include-book "trans-eval-error-triple")
(include-book "true-list-listp-theorems")
(include-book "typed-list-theorems")
(include-book "typed-tuples")
(include-book "ubi")
(include-book "untranslate-preprocessing")
(include-book "user-interface")
(include-book "verify-guards-program")
(include-book "world-queries")
(include-book "world-theorems")
(include-book "xdoc-constructors")
(include-book "zp-lists")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-utilities
  :parents (kestrel-books)
  :short "Utilities that are part of the
          <see topic='@(url kestrel-books)'>Kestrel Books</see>.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc theorems-about-non-kestrel-books
  :parents (kestrel-utilities)
  :short "Theorems about functions defined outside the
          <see topic='@(url kestrel-books)'>Kestrel Books</see>.")
