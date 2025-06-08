; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-trees")
(include-book "abstract-syntax-operations")
(include-book "convenience-constructors")
(include-book "indexed-names")
(include-book "syntax-abstraction")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (pfcs)
  :short "Abstract syntax of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define an abstract syntax
     straightforwardly derived from the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ".")
   (xdoc::p
    "Besides the abstract syntax trees (ASTs),
     we define some operations on ASTs,
     and some constructors to conveniently build ASTs.
     We also define a notion of indexed names,
     useful for building ``parameterized'' PFCSes.")
   (xdoc::p
    "We also formalize the mapping
     from the concrete syntax trees (CSTs) defined by the grammar
     to the corresponding ASTs."))
  :order-subtopics (abstract-syntax-trees
                    abstract-syntax-operations
                    convenience-constructors
                    indexed-names
                    syntax-abstraction))
