; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "keywords")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/letter-digit-uscore-chars" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ portable-ascii-identifiers
  :parents (language)
  :short "Portable ASCII identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A portable ASCII identifier is
     a non-empty sequence of ASCII characters that:")
   (xdoc::ul
    (xdoc::li
     "Consists of only
      the 26 uppercase Latin letters,
      the 26 lowercase Latin letters,
      the 10 numeric digits,
      and the underscore.")
    (xdoc::li
     "Starts with a letter or underscore.")
    (xdoc::li
     "Differs from all the "
     (xdoc::seetopic "*keywords*" "keywords")
     "."))
   (xdoc::p
    "The rationale behind this notion is the following.")
   (xdoc::p
    "[C17:6.4.2] allows the following characters in identifiers:")
   (xdoc::ol
    (xdoc::li
     "The ten numeric digits (but not in the starting position).")
    (xdoc::li
     "The 26 uppercase Latin letters,
      the 26 lowercase Latin letter,
      and the underscore.")
    (xdoc::li
     "Some ranges of universal characters
      (some of which cannot occur in the starting position).")
    (xdoc::li
     "Other implementation-defined characters."))
   (xdoc::p
    "The characters in (1) and (2) are part of the "
    (xdoc::seetopic "basic-source-charp" "basic source character set")
    ". The characters in (3) are presumably not
     part of the basic source character set,
     because they are non-ASCII Unicode characters,
     while the basic source character set
     maps naturally to ASCII Unicode characters;
     we say `presumably' because [C17] does not seem to explicitly prohibit
     the use of non-ASCII Unicode characters in the basic source character set
     (although it seems odd to do that).
     The characters in (4) may or may not be
     part of the basic source character set;
     [C17] imposes no constraints on them.")
   (xdoc::p
    "Recall that [C17] does not require the basic source character set
     to consist of ASCII characters (see @(see source-character-set)).
     If it does consist of ASCII characters, then
     the characters in (1) and (2) above are ASCII,
     the characters in (3) are not ASCII,
     and the characters in (4) may or may not be ASCII.")
   (xdoc::p
    "In our formalization of C, we currently assume that
     source characters include ASCII characters
     and the basic source character set consists of ASCII characters.
     Our model of "
    (xdoc::seetopic "ident" "identifiers")
    " uses ACL2 strings, which are a superset of the ASCII characters.")
   (xdoc::p
    "Thus, in order for our identifiers to be both ASCII and portable,
     they must consist exclusively of characters from (1) and (2) above,
     without any characters from (3) or (4).
     If they included characters from (3), they would not be ASCII.
     If they included characters from (4), they would not be portable,
     because those additional characters may vary across implementations.")
   (xdoc::p
    "This leads to our definition of portably ASCII identifiers,
     which consists of ASCII letters and digits and underscore,
     with the first character not a digit.
     They must also be distinct from keywords [C17:6.4.2.1/4]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define paident-char-listp ((chs character-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of ACL2 characters is not empty,
          consists only of ASCII letters, digits, and underscores,
          and does not start with a digit."
  :long
  (xdoc::topstring-p
   "Sequences of characters satisfying these conditions may be "
   (xdoc::seetopic "portable-ascii-identifiers" "portable ASCII identifiers")
   ", provided they are distinct from keywords.")
  (and (consp chs)
       (str::letter/digit/uscore-charlist-p chs)
       (not (str::dec-digit-char-p (car chs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define paident-stringp ((str stringp))
  :returns (yes/no booleanp)
  :short (xdoc::topstring
          "Check if an ACL2 string is a "
          (xdoc::seetopic "portable-ascii-identifiers"
                          "portable ASCII identifier")
          ".")
  (and (paident-char-listp (str::explode str))
       (not (member-equal str *keywords*))))
