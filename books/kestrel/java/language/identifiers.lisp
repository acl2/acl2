; Java Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "null-literal")
(include-book "boolean-literals")
(include-book "keywords")

(include-book "std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifiers
  :parents (syntax)
  :short "Java identifiers [JLS25:3.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Java identifiers are sequences of characters that, among other things,
     must differ from Java keywords.
     Since, as discussed in the "
    (xdoc::seetopic "keywords" "topic on keywords")
    ", there are reserved and contextual Java keywords,
     correspondingly there are slightly different kinds of Java identifiers.
     One, and the main, kind excludes only reserved keywords:
     these identifiers are usable in most contexts,
     and correspond to the grammar rule for @('identifier').
     The other two kinds further exclude
     some of the contextual keywords,
     and correspond to the grammar rules for
     @('type-identifier') and @('unqualified-method-identifier').")
   (xdoc::p
    "Here we formalize these three kinds of identifiers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-identifier-ignore-p ((char asciip))
  :returns (yes/no booleanp)
  :short "Check if an ASCII character is ignorable in identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "[JLS25:3.8] introduces the notion of `ignorable' character in identifiers:
     two identifiers are considered `equal' when,
     after ignoring (i.e. removing) the ignorable characters,
     the two identifiers are the same (i.e. same characters in the same order).
     [JLS25:3.8] defines this notion in terms of
     the API method @('Character.isIdentifierIgnorable(int)').
     [JAPIS25] says that this method returns true on the Unicode characters
     with codes 0 to 8, 14 to 27, and 127 to 159,
     as well as the ones with the @('FORMAT') general category value.")
   (xdoc::p
    "Running OpenJDK 21's implementation of this API method
     on all the ASCII codes (i.e. the integers from 0 to 127),
     reveals that the ignorable ASCII characters are the ones with the codes
     0 to 8, 14 to 27, and 127, and no others.
     Ideally, this should be confirmed with the Unicode standard,
     in regard to the @('FORMAT') general category."))
  (b* ((char (mbe :logic (ascii-fix char) :exec char)))
    (or (and (<= 0 char) (<= char 8))
        (and (<= 14 char) (<= char 27))
        (= char 127)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonascii-identifier-ignore-p
  :short "Check if a non-ASCII Java Unicode character
          is ignorable in identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee ascii-identifier-ignore-p),
     but for Unicode characters that are not ASCII.")
   (xdoc::p
    "For now we leave this predicate almost completely unspecified,
     by introducing it as a weakly constrained function.
     We only require it
     to have a guard consisting of the non-ASCII Java Unicode characters,
     to return a boolean,
     and to fix its input to a Java Unicode character.")
   (xdoc::p
    "Defining this predicate completely may require
     the development of a Unicode library in ACL2
     that formalizes categories and related notions."))

  (encapsulate
    (((nonascii-identifier-ignore-p *) => *
      :formals (char)
      :guard (and (unicodep char) (not (asciip char)))))

    (local
     (defun nonascii-identifier-ignore-p (char)
       (declare (ignore char))
       nil))

    (defrule booleanp-of-nonascii-identifier-ignore-p
      (booleanp (nonascii-identifier-ignore-p char))
      :rule-classes (:type-prescription :rewrite))

    (fty::deffixequiv nonascii-identifier-ignore-p
      :args ((char unicodep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-ignore-p ((char unicodep))
  :returns (yes/no booleanp)
  :short "Check if a Java Unicode character is ignorable in identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This puts together @(tsee ascii-identifier-ignore-p)
     and @(tsee nonascii-identifier-ignore-p)."))
  (b* ((char (mbe :logic (unicode-fix char) :exec char)))
    (cond ((asciip char) (ascii-identifier-ignore-p char))
          (t (nonascii-identifier-ignore-p char))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist no-identifier-ignore-p (x)
  (identifier-ignore-p x)
  :short "Check if a list of Java Unicode characters
          does not include any character that is ignorable in identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may be useful, for example, to check that
     an identifier has no ignorable characters,
     i.e. that it is in some sense ``canonical''."))
  :guard (unicode-listp x)
  :negatedp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-identifier-start-p ((char asciip))
  :returns (yes/no booleanp)
  :short "Check if an ASCII character can start identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "[JLS25:3.8] introduces the notion of `Java letter'
     as a character that can be used to start an identifier.
     [JLS25:3.8] defines this notion in terms of
     the API method @('Character.isJavaIdentifierStart(int)').
     [JCAPIS25] specifies this method in terms of Unicode notions.")
   (xdoc::p
    "[JLS25:3.8] says that this notion includes the ASCII
     uppercase and lowercase Latin letters, as well as dollar and underscore.
     Running OpenJDK 21's
     implementation of @('Character.isJavaIdentifierStart(int)')
     on all the ASCII codes (i.e. the integers from 0 to 127)
     returns true for the characters with the codes
     36 (dollar),
     65 to 90 (uppercase letters),
     95 (underscore),
     97-122 (lowercase letters),
     and no others;
     these are exactly the ASCII characters mentioned by [JLS25:3.8].
     Ideally, this should be confirmed with the Unicode standard."))
  (b* ((char (mbe :logic (ascii-fix char) :exec char)))
    (or (= char (char-code #\$))
        (and (<= (char-code #\A) char) (<= char (char-code #\Z)))
        (= char (char-code #\_))
        (and (<= (char-code #\a) char) (<= char (char-code #\z)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonascii-identifier-start-p
  :short "Check if a non-ASCII Java Unicode character can start identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee ascii-identifier-start-p),
     but for Unicode characters that are not ASCII.")
   (xdoc::p
    "For now we leave this predicate almost completely unspecified,
     by introducing it as a weakly constrained function.
     We only require it
     to have a guard consisting of the non-ASCII Java Unicode characters,
     to return a boolean,
     and to fix its input to a Java Unicode character.")
   (xdoc::p
    "Defining this predicate completely may require
     the development of a Unicode library in ACL2
     that formalizes categories and related notions."))

  (encapsulate
    (((nonascii-identifier-start-p *) => *
      :formals (char)
      :guard (and (unicodep char) (not (asciip char)))))

    (local
     (defun nonascii-identifier-start-p (char)
       (declare (ignore char))
       nil))

    (defrule booleanp-of-nonascii-identifier-start-p
      (booleanp (nonascii-identifier-start-p char))
      :rule-classes (:type-prescription :rewrite))

    (fty::deffixequiv nonascii-identifier-start-p
      :args ((char unicodep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-start-p ((char unicodep))
  :returns (yes/no booleanp)
  :short "Check if a Java Unicode character can start identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This puts together @(tsee ascii-identifier-start-p)
     and @(tsee nonascii-identifier-start-p)."))
  (b* ((char (mbe :logic (unicode-fix char) :exec char)))
    (cond ((asciip char) (ascii-identifier-start-p char))
          (t (nonascii-identifier-start-p char))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-identifier-part-p ((char asciip))
  :returns (yes/no booleanp)
  :short "Check if an ASCII character can be non-starting part of identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "[JLS25:3.8] introduces the notion of `Java letter or digit'
     as a character that can be used in an identifier, not at the start.
     [JLS25:3.8] defines this notion in terms of
     the API method @('Character.isJavaIdentifierPart(int)').
     [JCAPIS25] specifies this method in terms of Unicode notions,
     and mentions that it includes ignorable characters
     (see @(tsee ascii-identifier-ignore-p)).
     [JLS25:3.8] says that a `Java digit' includes the ASCII decimal digits;
     this, together with the statement made by [JLS25:3.8] about `Java letters'
     (see @(tsee ascii-identifier-start-p)),
     implies that `Java letters and digits' include
     uppercase and lowercase Latin letters,
     decimal digits, dollar, and underscore.")
   (xdoc::p
    "Running OpenJDK 21's
     implementation of @('Character.isJavaIdentifierPart(int)')
     on all the ASCII codes (i.e. the integers from 0 to 127)
     returns true for the characters with the codes
     0 to 8,
     14 to 27,
     36 (dollar),
     48 to 57 (decimal digits),
     65 to 90 (uppercase letters),
     95 (underscore),
     97-122 (lowercase letters),
     127,
     and no others;
     these are exactly the ASCII characters mentioned by [JLS25:3.8],
     plus the ignorable ASCII characters
     (see @(tsee ascii-identifier-ignore-p)).
     Ideally, this should be confirmed with the Unicode standard."))
  (b* ((char (mbe :logic (ascii-fix char) :exec char)))
    (or (and (<= 0 char) (<= char 8))
        (and (<= 14 char) (<= char 27))
        (= char (char-code #\$))
        (and (<= (char-code #\A) char) (<= char (char-code #\Z)))
        (= char (char-code #\_))
        (and (<= (char-code #\a) char) (<= char (char-code #\z)))
        (and (<= (char-code #\0) char) (<= char (char-code #\9)))
        (= char 127)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonascii-identifier-part-p
  :short "Check if a non-ASCII Java Unicode character
          can be non-starting part of identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee ascii-identifier-part-p),
     but for Unicode characters that are not ASCII.")
   (xdoc::p
    "For now we leave this predicate almost completely unspecified,
     by introducing it as a weakly constrained function.
     We only require it
     to have a guard consisting of the non-ASCII Java Unicode characters,
     to return a boolean,
     and to fix its input to a Java Unicode character.")
   (xdoc::p
    "Defining this predicate completely may require
     the development of a Unicode library in ACL2
     that formalizes categories and related notions."))

  (encapsulate
    (((nonascii-identifier-part-p *) => *
      :formals (char)
      :guard (and (unicodep char) (not (asciip char)))))

    (local
     (defun nonascii-identifier-part-p (char)
       (declare (ignore char))
       nil))

    (defrule booleanp-of-nonascii-identifier-part-p
      (booleanp (nonascii-identifier-part-p char))
      :rule-classes (:type-prescription :rewrite))

    (fty::deffixequiv nonascii-identifier-part-p
      :args ((char unicodep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-part-p ((char unicodep))
  :returns (yes/no booleanp)
  :short "Check if a Java Unicode character
          can be non-starting part of identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This puts together @(tsee ascii-identifier-part-p)
     and @(tsee nonascii-identifier-part-p)."))
  (b* ((char (mbe :logic (unicode-fix char) :exec char)))
    (cond ((asciip char) (ascii-identifier-part-p char))
          (t (nonascii-identifier-part-p char))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist identifier-part-listp (x)
  (identifier-part-p x)
  :short "Check if a list of Java Unicode characters consists of
          only characters that can be non-starting parts of identifiers."
  :guard (unicode-listp x)
  :elementp-of-nil t
  ///

  (fty::deffixequiv identifier-part-listp
    :args ((x unicode-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection identifier
  :short "Fixtype of Java identifiers, for most contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are Java identifiers that exclude just the reserved keywords,
     as discussed in the "
    (xdoc::seetopic "identifiers" "topic on identifiers")
    ". Since these are used in most contexts
     (except for some module-related contexts),
     we use the general name @('identifierp') for this recognizer.")
   (xdoc::p
    "We model these Java identifiers as lists of Java Unicode characters
     that are not empty,
     that start with a character satisfying @(tsee identifier-start-p),
     that continue with characters satisfying @(tsee identifier-part-p),
     that differ from all the non-restricted keywords,
     and that differ from the boolean and null literals.
     See [JLS25:3.8]."))

  (define identifierp (x)
    :returns (yes/no booleanp)
    :short "Recognizer for @(tsee identifier)."
    (and (unicode-listp x)
         (consp x)
         (identifier-start-p (car x))
         (identifier-part-listp (cdr x))
         (not (reserved-keywordp x))
         (not (boolean-literalp x))
         (not (null-literalp x))))

  (std::deffixer identifier-fix
    :pred identifierp
    :body-fix (list (char-code #\$))
    :short "Fixer for @(tsee identifierp).")

  (fty::deffixtype identifier
    :pred identifierp
    :fix identifier-fix
    :equiv identifier-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist identifier-list
  :short "Fixtype of lists of Java identifiers, for most contexts."
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection tidentifier
  :short "Fixtype of Java type identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar rule for @('type-identifier') in [JLS25:3.8]
     defines a type identifier as a regular identifier that is not
     @('permits'), @('record'), @('sealed'), @('var'), or @('yield').")
   (xdoc::p
    "Accordingly, we model Java type identifiers as regular identifiers
     that differ from the Unicode sequences for those keywords."))

  (define tidentifierp (x)
    :returns (yes/no booleanp)
    :short "Recognizer for @(tsee tidentifier)."
    (and (identifierp x)
         (not (equal x (string=>unicode "permits")))
         (not (equal x (string=>unicode "record")))
         (not (equal x (string=>unicode "sealed")))
         (not (equal x (string=>unicode "var")))
         (not (equal x (string=>unicode "yield")))))

  (std::deffixer tidentifier-fix
    :pred tidentifierp
    :body-fix (list (char-code #\$))
    :short "Fixer for @(tsee tidentifierp).")

  (fty::deffixtype tidentifier
    :pred tidentifierp
    :fix tidentifier-fix
    :equiv tidentifier-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection umidentifier
  :short "Fixtype of Java unqualified method identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar rule for @('unqualified-method-identifier') in [JLS25:3.8]
     defines an unqualified method identifier as a regular identifier
     that is not @('yield').")
   (xdoc::p
    "Accordingly, we model Java unqualified method identifiers as
     regular identifiers
     that differ from the Unicode sequence for @('yield')."))

  (define umidentifierp (x)
    :returns (yes/no booleanp)
    :short "Recognizer for @(tsee umidentifier)."
    (and (identifierp x)
         (not (equal x (string=>unicode "yield")))))

  (std::deffixer umidentifier-fix
    :pred umidentifierp
    :body-fix (list (char-code #\$))
    :short "Fixer for @(tsee umidentifierp).")

  (fty::deffixtype umidentifier
    :pred umidentifierp
    :fix umidentifier-fix
    :equiv umidentifier-equiv
    :define t
    :forward t))
