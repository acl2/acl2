; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ collect-idents
  :parents (utilities)
  :short "A utility to collect identifiers within a C program."
  :long
  (xdoc::topstring
    (xdoc::p
      "This returns all identifiers within a C AST. Eventually, we may wish
       to extend this utility to only collect the identifiers occuring in
       particular scopes or name spaces.")
    (xdoc::p
      "This utility is intended to operate on unambiguous ASTs. It may or may
       not collect identifiers appearing in ambiguous AST nodes.")
    (xdoc::p
      "This utility is expected to be useful for checking for freshness of
       variable names."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce collect-idents
  :types (ident
          ident-option
          c$::ident-list
          c$::exprs/decls/stmts
          fundef
          c$::fundef-option
          c$::extdecl
          c$::extdecl-list
          transunit
          c$::filepath-transunit-map
          transunit-ensemble)
  :result ident-setp
  :default nil
  :combine union
  :override ((ident (insert (ident-fix ident) nil))))
