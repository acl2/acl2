; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "notation/top")
(include-book "grammar-parser/top")
(include-book "grammar-printer/top")
(include-book "grammar-definer/top")
(include-book "operations/top")
(include-book "parsing-tools/top")
(include-book "examples/top")
(include-book "tree-utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abnf

  :parents (acl2::projects)

  :short "A library for ABNF (Augmented Backus-Naur Form)."

  :long

  (xdoc::topstring

   (xdoc::p
    "ABNF is a standardized formal grammar notation
     used in several Internet syntax specifications,
     e.g. "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "URI") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "HTTP") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5322" "IMF") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5321" "SMTP") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3501" "IMAP") ", and "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7159" "JSON")
    ". ABNF is specified by "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5234" "RFC 5234")
    " and "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7405" "RFC 7405")
    "; the latter updates two portions of the former.
     The syntax of ABNF is specified in ABNF itself.")

   (xdoc::p
    "This ACL2 library provides:")
   (xdoc::ul
    (xdoc::li
     "A "
     (xdoc::seetopic "notation" "formalization")
     " of the syntax and semantics of the ABNF notation.")
    (xdoc::li
     "A "
     (xdoc::seetopic "grammar-parser" "verified parser")
     " that turns ABNF grammar text
      (e.g. from the HTTP RFC)
      into a formal representation suitable for formal specification
      (e.g. for HTTP parsing).")
    (xdoc::li
     "Executable @(see operations) on ABNF grammars,
      e.g. to check their well-formedness and to compose them.")
    (xdoc::li
     "A @(tsee defgrammar) tool
      for building ACL2 representations of grammar from files,
      using the aforementioned verified parser,
      and for automatically proving
      certain properties such as well-formedness.")
    (xdoc::li
     "Some basic "
     (xdoc::seetopic "parsing-primitives-defresult" "parsing primitives")
     ", also available in "
     (xdoc::seetopic "parsing-primitives-seq" "another variant")
     ", usable as part of larger parsers.")
    (xdoc::li
     "A @(tsee defdefparse) tool
      for generating some very preliminary tools to generate
      parsing functions from grammar rules.")
    (xdoc::li
     "Some @(see examples) of
      use of @(tsee defgrammar) and some grammar @(see operations)
      on a few real-world ABNF grammars (e.g. for HTTP)."))

   (xdoc::p
    "Besides the aforementioned examples,
     @(tsee defgrammar) and some grammar @(see operations) have been used on "
    (xdoc::seetopic "java::grammar" "an ABNF grammar of Java")
    ", "
    (xdoc::seetopic "yul::concrete-syntax" "two ABNF grammars of Yul")
    ", and "
    (xdoc::seetopic "c::grammar" "an ABNF grammar of a subset of C")
    ". The @(tsee defdefparse) tool has been used to generate part of "
    (xdoc::seetopic "yul::lexer" "a Yul lexer")
    ".")

   (xdoc::p
    "In the documentation of this library,
     `[RFC]' refers to the result of updating RFC 5234 as specified by RFC 7405.
     Sections and subsections of [RFC] are referenced
     by appending their designations separated by colon:
     for example, `[RFC:3]' refers to Section 3 of RFC 5234.
     As another example, `[RFC:2.3]' refers to
     the result of updating Section 2.3 of RFC 5234
     as specified in Section 2.1 of RFC 7405.
     These square-bracketed references may be used
     as nouns or parenthetically.")

   (xdoc::p
    "This "
    (xdoc::ahref "https://alessandrocoglio.info/vstte-2018.pdf"
                 "VSTTE 2018 paper")
    " provides an overview
     of the ABNF notation formalization
     and of the verified parser
     (but not of the operations on ABNF grammars,
     of the parsing primitives,
     of the parsing generation tools,
     or of the real-world examples).
     The differences between the paper and the ABNF library
     are described "
    (xdoc::seetopic "differences-with-paper" "here")
    "."))

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc differences-with-paper

  :parents (abnf)

  :short "Differences with the paper."

  :long

  (xdoc::topstring

   (xdoc::p
    "For brevity, the paper makes the following slight simplfications
     compared to the ABNF library:")

   (xdoc::ul

    (xdoc::li
     "The forms in the paper omit
      guards,
      rule classes,
      measures,
      hints,
      keyed options for documentation (e.g. @(':short')),
      and some keyed options for "
     (xdoc::seetopic "fty::fty" "FTY")
     " types (e.g. @(':pred')).")

    (xdoc::li
     "The paper uses
      @(tsee defun),
      @(tsee mutual-recursion),
      @(tsee defthm), and
      @(tsee defun-sk)
      instead of
      @(tsee define),
      @(tsee defines),
      @(tsee defrule), and
      @(tsee define-sk).")

    (xdoc::li
     "The paper uses slightly shorter names
      for the parameters of some functions
      (e.g. @('alt') instead of @('alternation')).")

    (xdoc::li
     "The paper uses @('*abnf-grammar*')
      as the name of the constant @(tsee *grammar*)."))))
