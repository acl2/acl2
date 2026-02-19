; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "code-ensembles")

(include-book "../language/portable-ascii-identifiers")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ascii-identifiers
  :parents (abstract-syntax)
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
     More precisely, we define a family of predicates:
     one for each supported version of C.
     The non-standard versions have more keywords,
     and thus (finitely) fewer identifiers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-ident-stringp (x (version c::versionp))
  :returns (yes/no booleanp)
  :short "Recognize an ACL2 string that is a C ASCII identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "For standard C17,
     this notion is the same as the one of "
    (xdoc::seetopic "c::portable-ascii-identifiers" "portable ASCII identifiers")
    " defined in the language formalization;
     in fact, we use a function defined there as part of the definition here.
     The notion is that the string must start with a letter or underscore,
     consists of only letters, digits, and underscores,
     and be distinct from the standard C keywords.")
   (xdoc::p
    "If the @('version') is not C17,
     we adjust the keywords to be excluded accordingly."))
  (and (stringp x)
       (c::paident-char-listp (str::explode x))
       (not (member-equal x (c::keywords-for version))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce aidentp
  :short "Definition of the predicates that check whether
          all the identifiers in the abstract syntax
          are ASCII and valid, w.r.t a particular version of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
   (xdoc::p
    "These predicates are all parameterized by the C version,
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
          ident-list-list
          ident-option
          const
          attrib-name
          exprs/decls/stmts
          fundef
          ext-declon
          ext-declon-list
          transunit
          filepath-transunit-map
          transunit-ensemble)
  :extra-args ((version c::versionp))
  :result booleanp
  :default t
  :combine and
  :override ((ident (ascii-ident-stringp (ident->unwrap ident) version))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-ensemble-aidentp ((code code-ensemblep))
  :returns (yes/no booleanp)
  :short "Check if a code ensemble only uses, in its translation unit ensemble,
          ASCII identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The condition is checked w.r.t.
     the @(see c::version) in the implementation environment."))
  (transunit-ensemble-aidentp (code-ensemble->transunits code)
                              (ienv->version (code-ensemble->ienv code)))
  :hooks (:fix))
