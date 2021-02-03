; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "unicode-characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod unicode-input-char
  :parents (syntax)
  :short "Fixtype of Unicode input characters [JLS:3.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the grammar rule for @('unicode-input-character') [JLS:3.3],
     a Unicode input character is
     either a ``raw'' Unicode character (i.e. the character itself)
     or a Unicode escape (which consists of ASCII code).
     The first lexical translation step,
     which we formalize in @(tsee unicode-escapes),
     turns Unicode escapes into the corresponding (raw) Unicode characters.")
   (xdoc::p
    "When representing the abstract syntax of a Java program,
     it is convenient, for certain purposes,
     to include information about Unicode escapes.
     This information is useful mainly for characters
     that are part of identifiers or of character and string literals,
     because that is where escapes are normally used in a Java program,
     as alternatives to the raw characters (normally when not ASCII).
     While it is permitted to use escapes for any part of a Java program,
     e.g. for the characters that form keywords or integer literals,
     there seems to be no good reason to do that in a Java program,
     given that more readable ASCII characters can be used instead.")
   (xdoc::p
    "The information about Unicode escapes is useful, in the abstract syntax,
     to represent Java programs more precisely.
     For example, if the abstract syntax is obtained by parsing a Java program,
     we can retain the information of which characters of the program
     were escapes in (the concrete syntactic representation of) the program.
     As another example, a Java code generator may produce
     more nuanced or customizable code
     by choosing Unicode escapes for certain characters.")
   (xdoc::p
    "Thus, here we formalize a Unicode input character
     (following the nomenclature of @('unicode-input-character') in the grammar)
     as a record of two components.
     One component is just the plain (raw) Unicode character
     that is denoted either by a itself or by an escape.
     The other component indicates whether the character is raw or an escape.
     A boolean flag would suffice to distinguish these two cases,
     but we want to include even more information here:
     we use the number of @('u') characters in the escape to indicate an escape
     (and to indicate how many @('u')s it uses in the concrete syntax);
     we use the number 0 to denote a raw character.
     Recall that the grammar rule for @('unicode-marker') in [JLS:3.3]
     allows one or more @('u') characters.
     So a natural number captures the information that we need here."))
  ((unicode unicode)
   (umarker nat))
  :layout :list
  :tag :unicode-input-char)
