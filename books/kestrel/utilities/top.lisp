; Kestrel Utilities
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-logic-fns")
(include-book "apply-fn-if-known")
(include-book "auto-instance")
(include-book "auto-termination")
(include-book "bits-as-digits")
(include-book "bits-and-bytes-as-digits")
(include-book "bits-and-ubyte11s-as-digits")
(include-book "bytes-as-digits")
(include-book "copy-def")
(include-book "defmacroq")
(include-book "deftest")
(include-book "defthmr")
(include-book "digits-any-base/top")
(include-book "directed-untranslate")
(include-book "doublets")
(include-book "enumerations")
(include-book "erp")
(include-book "er-soft-plus")
(include-book "error-checking/top")
(include-book "event-tuples-between")
(include-book "gen-xdoc-for-file")
(include-book "include-book-paths")
(include-book "integer-arithmetic/top")
(include-book "integer-range-fixing")
(include-book "integer-range-lists")
(include-book "integers-from-to")
(include-book "integers-from-to-as-set")
(include-book "keyword-value-lists")
(include-book "lists/top")
(include-book "magic-macroexpand")
(include-book "magic-macroexpand1-dollar")
(include-book "make-executable")
(include-book "make-termination-theorem")
(include-book "maybe-unquote")
(include-book "messages")
(include-book "minimize-ruler-extenders")
; Skipping the following, because it requires a trust tag:
; (include-book "non-ascii-pathnames" :ttags (:non-ascii-pathnames))
(include-book "omaps/with-fixing-theorems")
(include-book "orelse")
(include-book "oset-theorems")
(include-book "osets")
(include-book "proof-builder-macros")
(include-book "prove-interface")
(include-book "signed-byte-fixing")
(include-book "signed-byte-list-fixing")
(include-book "skip-in-book")
(include-book "strings/top")
(include-book "sublis-expr-plus")
(include-book "system/top")
(include-book "trans-eval-error-triple")
(include-book "true-list-listp-theorems")
(include-book "typed-lists/top")
(include-book "typed-tuples")
(include-book "ubi")
(include-book "ubyte11s-as-digits")
(include-book "unsigned-byte-fixing")
(include-book "unsigned-byte-list-fixing")
(include-book "untranslate-preprocessing")
(include-book "user-interface")
(include-book "verify-guards-program")
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
