; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "keywords")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "std/strings/letter-chars" :dir :system)
(include-book "std/strings/letter-digit-uscore-chars" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifiers
  :parents (abstract-syntax)
  :short "Leo identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Leo, identifiers are non-empty sequences of ASCII characters,
     starting with a letter
     and containing only letters, digits, and underscore.
     They must also be distinct from
     all the keywords and the boolean literals.
     They must also not be, or start with, @('aleo1').")
   (xdoc::p
    "Since the ASCII characters are
     a subset of ACL2's ISO 8851-1 characters,
     it is adequate to represent Leo identifiers
     as sequences of ACL2 characters, i.e. as ACL2 strings."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-grammar-chars-p ((chars character-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of characters forms a Leo identifier
          according to the ABNF grammar rule for identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list must start with a letter
     and only contain letters, digits, and underscores.
     This is exactly what the grammar rule requires,
     but there are also extra-grammatical requirements,
     captured in @(tsee identifier-string-p)"))
  (b* ((chars (str::character-list-fix chars)))
    (and (consp chars)
         (str::letter-char-p (car chars))
         (str::letter/digit/uscore-charlist-p (cdr chars))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-string-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if a string is a valid Leo identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string's characters must follow the grammar rule.
     In addition, the string must not be a keyword or boolean literal,
     and must not be or start with @('aleo1')."))
  (and (identifier-grammar-chars-p (str::explode string))
       (not (member-equal (str-fix string) *keywords*))
       (not (equal (str-fix string) "true"))
       (not (equal (str-fix string) "false"))
       (not (prefixp (str::explode "aleo1") (str::explode string))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod identifier
  :short "Fixtype of Leo identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We wrap the string into a one-component product type
     for better encapsulation and abstraction.")
   (xdoc::p
    "It also facilitates the addition of information (e.g. metadata),
     if needed at some point."))
  ((name string :reqfix (if (identifier-string-p name) name "o")))
  :require (identifier-string-p name)
  :tag :identifier
  :pred identifierp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist identifier-list
  :short "Fixtype of lists of Leo identifiers."
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption identifier-option
  identifier
  :short "Fixtype of optional Leo identifiers."
  :pred identifier-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset identifier-set
  :short "Fixtype of osets of Leo identifiers."
  :elt-type identifier
  :elementp-of-nil nil
  :pred identifier-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-result
  :short "Fixtype of errors and Leo identifiers."
  :ok identifier
  :pred identifier-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-list-result
  :short "Fixtype of errors and lists of Leo identifiers."
  :ok identifier-list
  :pred identifier-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-option-result
  :short "Fixtype of errors and optional Leo identifiers."
  :ok identifier-option
  :pred identifier-option-resultp
  :prepwork ((local (in-theory (enable identifierp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod programid
  :short "Fixtype of program IDs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A program ID consists of a name and a network, both identifiers.
     Requirements on the network are expressed elsewhere,
     not in the abstract syntax."))
  ((name identifier)
   (network identifier))
  :tag :programid
  :pred programidp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult programid-result
  :short "Fixtype of errors and Leo program IDs."
  :ok programid
  :pred programid-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod locator
  :short "Fixtype of locators."
  :long
  (xdoc::topstring
   (xdoc::p
    "A locator consists of a program ID and an identifier.
     The latter denotes an item in the program denoted by the program ID."))
  ((program programid)
   (name identifier))
  :tag :locator
  :pred locatorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult locator-result
  :short "Fixtype of errors and Leo locators."
  :ok locator
  :pred locator-resultp)
