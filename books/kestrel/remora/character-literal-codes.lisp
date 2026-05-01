; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "std/util/defprojection" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ character-literal-codes
  :parents (abstract-syntax)
  :short "Numeric codes of character literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Character literals may be ``direct'' characters or escapes.
     Our ASTs represent the former directly as their codes,
     while it represents escapes in a more structured way.
     Here we define mappings from all kinds of character literals
     to their corresponding coded.")
   (xdoc::p
    "This mapping is used to define "
    (xdoc::seetopic "abstract-syntax-desugaring" "desugaring")
    ", but it may be also used to define the dynamic semantics
     (if the latter is defined on the full ASTs, not just the core ones)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-escape-code ((esc char-escapep))
  :returns (code natp)
  :short "Code of a character escape."
  (char-escape-case
   esc
   :a 7
   :b 8
   :f 12
   :n 10
   :r 13
   :t 9
   :v 11
   :bslash (char-code #\\)
   :dquote (char-code #\")
   :squote (char-code #\')))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-escape-code ((esc ascii-escapep))
  :returns (code natp)
  :short "Code of an ASCII escape."
  (ascii-escape-case
   esc
   :nul-to-sp esc.code
   :del 127))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define caret-escape-code ((esc caret-escapep))
  :returns (code natp)
  :short "Code of a caret escape."
  (caret-escape->code esc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define num-escape-code ((esc num-escapep))
  :returns (code natp)
  :short "Code of a numeric escape."
  (num-escape-case
   esc
   :dec (str::dec-digit-chars-value esc.digits)
   :oct (str::oct-digit-chars-value esc.digits)
   :hex (str::hex-digit-chars-value esc.digits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define escape-code ((esc escapep))
  :returns (code natp)
  :short "Code of an escape."
  (escape-case
   esc
   :char (char-escape-code esc.escape)
   :ascii (ascii-escape-code esc.escape)
   :caret (caret-escape-code esc.escape)
   :num (num-escape-code esc.escape)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-lit-code ((lit char-litp))
  :returns (code natp)
  :short "Code of a character literal."
  (char-lit-case
   lit
   :char lit.code
   :escape (escape-code lit.escape)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection char-lit-list-codes ((x char-lit-listp))
  :returns (codes nat-listp)
  :short "Codes of a list of character literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return a list of codes, in the same order as the literals."))
  (char-lit-code x))
