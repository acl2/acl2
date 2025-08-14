; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "code-ensembles")
(include-book "keywords")

(include-book "../language/portable-ascii-identifiers")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ascii-identifiers
  :parents (syntax-for-tools)
  :short "ASCII identifiers in the C abstract syntax of tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our abstract syntax allows identifiers to be anything,
     for the reasons explained in @(tsee ident).
     Nonetheless, given our current concrete syntax definition,
     parsed identifiers always consist of ASCII characters
     satisfying certain restrictions (start with a letter, etc.).
     Disambiguator and validator preserve this property of identifiers.
     The printer currently checks, at run time,
     that identifiers satisfy a weaker property than this,
     but it should really only be used to print
     abstract syntax whose identifiers satisfy
     the stronger property that is being discussed and defined here.
     C-to-C transformations may intentionally break this property
     (see the discussion in @(tsee ident)),
     but the abstract syntax should be eventually transformed
     into a printable form before actually printing it.")
   (xdoc::p
    "Here we formalize the notion of ASCII identifiers,
     and we define predicates on the abstract syntax
     that check that all the identifiers satisfy this property.
     More precisely, we define two sets of predicates:
     one is for standard C, and one is for C with GCC extensions.
     The difference is that the letter has more keywords,
     and thus (finitely) fewer identifiers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-ident-stringp (x (gcc booleanp))
  :returns (yes/no booleanp)
  :short "Recognize an ACL2 string that is a C ASCII identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('gcc') flag determines whether GCC extensions
     should be considered or not,
     since the notion varies slightly, as explained shortly.")
   (xdoc::p
    "For standard C (i.e. no GCC extensions),
     this notion is the same as the one of "
    (xdoc::seetopic "c::portable-ascii-identifiers" "portable ASCII identifiers")
    " defined in the language formalization;
     in fact, we use a function defined here as part of the definition here.
     The notion is that the string must start with a letter or underscore,
     consists of only letters, digits, and underscores,
     and be distinct from the standard C keywords.")
   (xdoc::p
    "With GCC extensions, the notion is strenghtened
     to also exclude the GCC keywords."))
  (and (stringp x)
       (c::paident-char-listp (str::explode x))
       (not (member-equal x *keywords*))
       (or (not gcc) (not (member-equal x *gcc-keywords*))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce aidentp
  :short "Definition of the predicates that check whether
          all the identifiers in the abstract syntax
          are ASCII and valid, with or without GCC extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
   (xdoc::p
    "These predicates are all parameterized by
     a flag saying whether GCC extensions are supported or not,
     which changes the exact notion of valid ASCII identifier;
     see @(tsee ascii-ident-stringp).")
   (xdoc::p
    "The @(':default') value is @('t'),
     because constructs without identifiers satisfy the property.")
   (xdoc::p
    "The @(':combine') operator is @(tsee and),
     because we need to check all the identifiers, recursively.")
   (xdoc::p
    "We only need to override the predicate for the @(tsee ident) type,
     to call @(tsee ascii-ident-stringp) on the unwrapped value."))
  :types (ident
          ident-list
          ident-option
          const
          attrib-name
          exprs/decls/stmts
          fundef
          extdecl
          extdecl-list
          transunit
          filepath-transunit-map
          transunit-ensemble)
  :extra-args ((gcc booleanp))
  :result booleanp
  :default t
  :combine and
  :override ((ident (ascii-ident-stringp (ident->unwrap ident) gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled expr-aidentp-of-expr-ident
  (equal (expr-aidentp (expr-ident ident info) gcc)
         (ident-aidentp ident gcc))
  :enable expr-aidentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled expr-aidentp-of-expr-const
  (equal (expr-aidentp (expr-const const) gcc)
         (const-aidentp const gcc))
  :enable expr-aidentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled transunit-aidentp-of-head-when-filepath-transunit-map-aidentp
  (implies (and (filepath-transunit-mapp tumap)
                (filepath-transunit-map-aidentp tumap gcc)
                (not (omap::emptyp tumap)))
           (transunit-aidentp (mv-nth 1 (omap::head tumap)) gcc))
  :enable filepath-transunit-map-aidentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled filepath-transunit-map-aidentp-of-transunit-ensemble->unwrap
  (implies (transunit-ensemble-aidentp tunits gcc)
           (filepath-transunit-map-aidentp
            (transunit-ensemble->unwrap tunits) gcc))
  :enable transunit-ensemble-aidentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-to-ruleset abstract-syntax-aidentp-rules
                '(expr-aidentp-of-expr-ident
                  expr-aidentp-of-expr-const
                  transunit-aidentp-of-head-when-filepath-transunit-map-aidentp
                  filepath-transunit-map-aidentp-of-transunit-ensemble->unwrap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-ensemble-aidentp ((code code-ensemblep))
  :returns (yes/no booleanp)
  :short "Check if a code ensemble only uses, in its translation unit ensemble,
          ASCII identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The condition is checked w.r.t.
     the GCC flag in the implementation environment."))
  (transunit-ensemble-aidentp (code-ensemble->transunits code)
                              (ienv->gcc (code-ensemble->ienv code)))
  :hooks (:fix))
