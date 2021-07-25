; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")

(include-book "kestrel/utilities/strings/char-kinds" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (yul)
  :short "Static semantics of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the static semantics of Yul
     via functions that check that the abstract syntax of Yul
     satisfy a number of constraints.")
   (xdoc::p
    "Since, as explained in @(see abstract-syntax), we omit types for now,
     type checking is prominently missing for now.
     We will probably want to introduce some notion of types soon."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-wfp ((iden identifierp))
  :returns (yes/no booleanp)
  :short "Check if an identifier is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of only
     letter (lowercase and uppercase),
     (decimal) digits,
     underscores, and
     dollars.
     It must be non-empty and not start with a digit.")
   (xdoc::p
    "We may move these requirements into an invariant of @(tsee identifier),
     but for now we state them as part of the static semantics."))
  (b* ((chars (str::explode (identifier->get iden))))
    (and (consp chars)
         (acl2::alpha/uscore/dollar-char-p (car chars))
         (acl2::alpha/digit/uscore/dollar-charlist-p (cdr chars))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist identifier-list-wfp (x)
  :guard (identifier-listp x)
  :short "Check if all the identifiers in a list are well-formed."
  (identifier-wfp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-wfp ((path pathp))
  :returns (yes/no booleanp)
  :short "Check if a path is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of one or more well-formed identifiers.")
   (xdoc::p
    "We may move the non-emptiness requirement
     into an invariant of @(tsee path),
     but for now we state it as part of the static semantics."))
  (b* ((idens (path->get path)))
    (and (consp idens)
         (identifier-list-wfp idens)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-wfp ((lit literalp))
  :returns (yes/no booleanp)
  :short "Check if a literal is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Restrictions on the Grammar],
     literals cannot be larger than their types,
     and the largest type is that of unsigned 256-bit integers.
     For now we do not model types (i.e. we assume one type),
     so we limit the size to 256 bits.
     This is straighforward for numeric literals.
     For (non-hex) string, it boils down to a limit of 32 on the length
     (since every character represents 8 bits).
     For hex strigns, it boils down to a limit of 32 on the number of hex pairs;
     hex strings must also be non-empty, according to the grammar.
     Boolean literals are always well-formed;
     they are not, and they do not represent, numbers anyways.")
   (xdoc::p
    "We do not impose other restrictions on (non-hex) strings here,
     such as that a string surrounded by double quotes
     cannot contain (unescaped) double quotes.
     Those are simply syntactic restrictions."))
  (literal-case
   lit
   :boolean t
   :dec-number (< lit.get
                  (expt 2 256))
   :hex-number (< (str::hex-digit-chars-value (hex-digit-list->chars lit.get))
                  (expt 2 256))
   :string (<= (len lit.content) 32)
   :hex-string (and (< 0 (len lit.content))
                    (<= (len lit.content) 32)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add symbol tables and define wfp of expressions, statements, etc.
