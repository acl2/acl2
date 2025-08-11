; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/fty/deffold-map" :dir :system)

(include-book "../syntax/abstract-syntax-trees")
(include-book "../syntax/code-ensembles")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rename
  :parents (transformation-tools)
  :short "A C-to-C transformation to rename identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
     "This transformation will rename all identifiers according to a provided
      alist. Note, it does nothing to ensure substitutions preserve semantic
      equivalence. For instance, a substitution might introduce variable names
      which conflict with existing variables.")
   (xdoc::p
     "Eventually we may wish for a renaming transformation with options to
      limit substitution by type of identifier, scope, restrict to free
      variables, etc."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist ident-ident-alist
  :key-type c$::ident
  :val-type c$::ident
  :pred ident-ident-alistp
  :true-listp t
  :prepwork ((set-induction-depth-limit 1)))

(defrulel identp-of-cdr-of-assoc-equal-of-alist-when-ident-ident-alistp
  (implies (and (assoc-equal ident alist)
                (ident-ident-alistp alist))
           (c$::identp (cdr (assoc-equal ident alist))))
  :induct t
  :enable assoc-equal)

(define ident-ident-subst
  ((ident c$::identp)
   (alist ident-ident-alistp))
  :returns (new-ident c$::identp)
  (b* ((lookup (assoc-equal (c$::ident-fix ident)
                            (ident-ident-alist-fix alist))))
    (c$::ident-fix
      (if lookup
          (cdr lookup)
        ident)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename
  :types #!c$(ident
              ident-list
              ident-option
              iconst
              iconst-option
              const
              const-option
              attrib-name
              exprs/decls/stmts
              fundef
              extdecl
              extdecl-list
              transunit
              filepath-transunit-map
              transunit-ensemble)
  :extra-args ((subst ident-ident-alistp))
  :override ((ident (ident-ident-subst ident subst))))

(define code-ensemble-rename ((code code-ensemblep)
                              (subst ident-ident-alistp))
  :returns (new-code code-ensemblep)
  (change-code-ensemble
   code
   :transunits
   (transunit-ensemble-rename (code-ensemble->transunits code) subst)))
