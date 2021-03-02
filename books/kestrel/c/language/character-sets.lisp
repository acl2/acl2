; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/strings/coerce" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ character-sets
  :parents (language)
  :short "Source and execution character sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are described in [C:5.2.1].")
   (xdoc::p
    "The members of these sets are more abstract entities
     than the values of the character types [C:6.2.5/15].
     The assignment of values to the members of the execution character set
     is implementation-defined [C:5.2.1/1],
     subject to some constraints.
     The source and execution character sets may be different,
     subject to certain constraints and correspondences.")
   (xdoc::p
    "Our formalization is parameterized over the specifics of
     the source and execution character sets.
     We represent these character sets via
     suitably constrained ACL2 predicates and mappings."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ source-character-set
  :parents (character-sets)
  :short "Source character set."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C:5.2.1] prescribes the presence of certain members
     in the source character set.
     These prescribed members
     form the basic source character set,
     and correspond naturally to certain (ACL2) ASCII characters.
     However, [C] does not prescribe ASCII,
     even though many C implementations may use (some extension of) ASCII.")
   (xdoc::p
    "We formalize the source character set as a constrained ACL2 predicate,
     along with an injection into them from the ASCII characters mentioned above
     (i.e. the ones that correspond naturally to the ones prescribed by [C]).
     The image of the injection is the basic source character set,
     whose members are the basic source characters.
     The whole constrained predicate is the extended source character set,
     whose members that are not basic source characters
     are extended source characters.
     This is according to the nomenclature in [C:5.2.1].")
   (xdoc::p
    "Because the extended source character set
     is formalized here as a constrained predicate,
     there is no immediate way to refer to the extended characters
     (while the basic ones may be referenced via the aforementioned injection).
     Thus, we introduce a second injection,
     from the constrained predicate into the natural numbers:
     this means that each character has a unique associated number,
     which may be used to refer to the character.
     This second injection and numbering has no counterpart in [C]:
     its significance is limited to our ACL2 formalization.")
   (xdoc::p
    "[C:5.2.1.2] discusses encodings of source characters,
     including a notion of shift states that affect the encodings.
     This encoding provides a way
     to refer to the members of the source characters set;
     this is how source files are read.
     However, because of the constraints on single bytes for basic characters,
     and because of the possibility of shift states,
     this encoding does not seem the most straightforward way
     to refer to the source character set's members in our formalization.
     This is why we introduce the second injection described above.
     We plan to formalize the encoding discussed in [C:5.2.1.2] elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-basic-source-charp (x)
  :returns (yes/no booleanp)
  :short "Fixtype of the ACL2 ASCII characters that correspond to
          the members of the basic source character set in C."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are
     uppercase and lowercase letters,
     decimal digits,
     graphic characters,
     space,
     horizontal tab,
     vertical tab, and
     form feed
     [ISO:5.2.1/3].")
   (xdoc::p
    "Note that the double quote character and the backslash character
     must be escaped (i.e. preceded by a backslash) in ACL2 strings.
     The ACL2 character @('#\\Space') has ASCII code 32
     and corresponds to space.
     The ACL2 character @('#\\Tab') has ASCII code 9
     and corresponds to horizontal tab.
     The ACL2 character with ASCII code 11 corresponds to vertical tab.
     The ACL2 character @('#\\Page') has ASCII code 12
     and corresponds to form feed."))
  (or (and (member x (str::explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ")) t)
      (and (member x (str::explode "abcdefghijklmnopqrstuvwxyz")) t)
      (and (member x (str::explode "0123456789")) t)
      (and (member x (str::explode "!\"#%&'()*+,-./:;<=>?[\\]^_{|}~")) t)
      (and (member x (list #\Space
                           #\Tab
                           (code-char 11)
                           #\Page))
           t))
  :no-function t
  ///

  (defrule characterp-when-ascii-basic-source-charp
    (implies (ascii-basic-source-charp x)
             (characterp x))
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;

(std::deffixer ascii-basic-source-char-fix
  :short "Fixer for @(tsee ascii-basic-source-char)."
  :pred ascii-basic-source-charp
  :body-fix #\Space)

;;;;;;;;;;;;;;;;;;;;

(defsection ascii-basic-source-char
  :short "Fixtype for @(tsee ascii-basic-source-charp)."
  (fty::deffixtype ascii-basic-source-char
    :pred ascii-basic-source-charp
    :fix ascii-basic-source-char-fix
    :equiv ascii-basic-source-char-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection source-char-recognizer+fixer+mappings+fixtype
  :short "Constrained recognizer and fixer and mappings, and fixtype,
          for the source character set."
  :long
  (xdoc::topstring
   (xdoc::p
    "We constrain the recognizer to return a boolean.")
   (xdoc::p
    "Besides the recognizer, we also introduce a fixer,
     with the usual properties.
     This will let us define a fixtype for the source characters.")
   (xdoc::p
    "We constrain the mapping from the ASCII characters
     to fix its argument,
     to return source characters,
     and to be injective.")
   (xdoc::p
    "We constrain the function to the character numbers
     to fix its argument,
     to return natural numbers,
     and to be injective.
     We also constrain it to always return
     a number below an unspecified bound:
     this ensures that there is a finite number of source characters.")
   (xdoc::p
    "The bound itself is a constrained nullary function,
     constrained to return a positive integer."))

  (encapsulate

    ;; functions:

    (((source-charp *) => *)

     ((source-char-fix *) => *
      :formals (x)
      :guard (source-charp x))

     ((ascii-to-source-char *) => *
      :formals (x)
      :guard (ascii-basic-source-charp x))

     ((source-char-to-number *) => *
      :formals (x)
      :guard (source-charp x))

     ((source-char-to-number-bound) => *))

    ;; witnesses:

    (local
     (defun source-charp (x)
       (declare (xargs :guard t))
       (ascii-basic-source-charp x)))

    (local
     (defun source-char-fix (x)
       (declare (xargs :guard (source-charp x)))
       (ascii-basic-source-char-fix x)))

    (local
     (defun ascii-to-source-char (x)
       (declare (xargs :guard (ascii-basic-source-charp x)))
       (ascii-basic-source-char-fix x)))

    (local
     (defun source-char-to-number (x)
       (declare (xargs :guard (source-charp x)))
       (char-code (ascii-basic-source-char-fix x))))

    (local
     (defun source-char-to-number-bound ()
       (declare (xargs :guard t))
       256))

    ;; constraints:

    (defrule booleanp-of-source-charp
      (booleanp (source-charp x))
      :rule-classes :type-prescription)

    (defrule source-charp-of-source-char-fix
      (source-charp (source-char-fix x)))

    (defrule source-char-fix-when-source-charp
      (implies (source-charp x)
               (equal (source-char-fix x) x)))

    (defrule ascii-to-source-char-of-ascii-basic-source-char-fix
      (equal (ascii-to-source-char (ascii-basic-source-char-fix x))
             (ascii-to-source-char x)))

    (defrule source-charp-of-ascii-to-source-char
      (source-charp (ascii-to-source-char x)))

    (defrule ascii-to-source-char-injective
      (equal (equal (ascii-to-source-char x)
                    (ascii-to-source-char y))
             (ascii-basic-source-char-equiv x y)))

    (defrule source-char-to-number-of-source-char-fix
      (equal (source-char-to-number (source-char-fix x))
             (source-char-to-number x)))

    (defrule natp-of-source-char-to-number
      (natp (source-char-to-number x))
      :rule-classes :type-prescription)

    (defruled source-char-to-number-injective-lemma ; used below
      (equal (equal (source-char-to-number x)
                    (source-char-to-number y))
             (equal (source-char-fix x)
                    (source-char-fix y))))

    (defrule posp-of-source-char-to-number-bound
      (posp (source-char-to-number-bound))
      :rule-classes :type-prescription)

    (defrule source-char-to-number-below-bound
      (< (source-char-to-number x)
         (source-char-to-number-bound))
      :rule-classes :linear))

  (fty::deffixtype source-char
    :pred source-charp
    :fix source-char-fix
    :equiv source-char-equiv
    :define t
    :forward t)

  (defrule source-char-to-number-injective
    (equal (equal (source-char-to-number x)
                  (source-char-to-number y))
           (source-char-equiv x y))
    :enable source-char-to-number-injective-lemma)

  (fty::deffixequiv ascii-to-source-char
    :args ((x ascii-basic-source-charp)))

  (fty::deffixequiv source-char-to-number
    :args ((x source-charp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk basic-source-charp (x)
  :returns (yes/no booleanp)
  :short "Recognize the basic source characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the characters in
     the image of the injection from the ASCII characters."))
  (exists (ascii)
          (and (ascii-basic-source-charp ascii)
               (equal x (ascii-to-source-char ascii))))
  ///

  (defrule source-charp-when-basic-source-charp
    (implies (basic-source-charp x)
             (source-charp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ext-source-charp (x)
  :returns (yes/no booleanp)
  :short "Recognize the extended source characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the non-basic source-characters."))
  (and (source-charp x)
       (not (basic-source-charp x)))
  ///

  (defruled source-charp-alt-def
    (equal (source-charp x)
           (or (basic-source-charp x)
               (ext-source-charp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-to-source-char-number ((x ascii-basic-source-charp))
  :returns (number natp :rule-classes :type-prescription)
  :short "Number of the basic source character
          corresponding to an ASCII character."
  (source-char-to-number (ascii-to-source-char x))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ exec-character-set
  :parents (character-sets)
  :short "Execution character set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The execution character set is analogous to the source character set
     except that it has a few additional basic characters [C:5.2.1].")
   (xdoc::p
    "We formalize the execution characters
     analogously to the source characters,
     i.e. as a constrained predicate
     with an injection from the ASCII basic ones
     and an injection to numbers.
     These numbers are not the values of the execution characters,
     which will be formalized elsewhere;
     the significance of these number is limited to our ACL2 formalization.
     See @(see source-character-set) for details."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-basic-exec-charp (x)
  :returns (yes/no booleanp)
  :short "Fixtype of the ACL2 ASCII characters that correspond to
          the members of the basic execution character set in C."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the ones for the basic source character set, plus
     null character,
     alert,
     backspace,
     carriage return, and
     new line
     [C:5.2.1/2-3].")
   (xdoc::p
    "The ACL2 character with ASCII code 0 corresponds to the null character.
     The ACL2 character with ASCII code 7 corresponds to alert.
     The ACL2 character with ASCII code 8 corresponds to backspace.
     The ACL2 charater @('#\\Return') has ASCII code 13
     and corresponds to carriage return.
     The ACL2 character @('#\\Newline') has ASCII code 10
     and corresponds to new line."))
  (or (ascii-basic-source-charp x)
      (and (member x (list (code-char 0)
                           (code-char 7)
                           (code-char 8)
                           #\Return
                           #\Newline))
           t))
  :no-function t
  ///

  (defrule characterp-when-ascii-basic-exec-charp
    (implies (ascii-basic-exec-charp x)
             (characterp x))
    :rule-classes :compound-recognizer))

;;;;;;;;;;;;;;;;;;;;

(std::deffixer ascii-basic-exec-char-fix
  :short "Fixer for @(tsee ascii-basic-exec-char)."
  :pred ascii-basic-exec-charp
  :body-fix #\Space)

;;;;;;;;;;;;;;;;;;;;

(defsection ascii-basic-exec-char
  :short "Fixtype for @(tsee ascii-basic-exec-charp)."
  (fty::deffixtype ascii-basic-exec-char
    :pred ascii-basic-exec-charp
    :fix ascii-basic-exec-char-fix
    :equiv ascii-basic-exec-char-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-char-recognizer+fixer+mappings+fixtype
  :short "Constrained recognizer and fixer and mappings, and fixtype,
          for the execution character set."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are analogous to the ones for the source character set.
     See @(see source-char-recognizer+fixer+mappings+fixtype)."))

  (encapsulate

    ;; functions:

    (((exec-charp *) => *)

     ((exec-char-fix *) => *
      :formals (x)
      :guard (exec-charp x))

     ((ascii-to-exec-char *) => *
      :formals (x)
      :guard (ascii-basic-exec-charp x))

     ((exec-char-to-number *) => *
      :formals (x)
      :guard (exec-charp x))

     ((exec-char-to-number-bound) => *))

    ;; witnesses:

    (local
     (defun exec-charp (x)
       (declare (xargs :guard t))
       (ascii-basic-exec-charp x)))

    (local
     (defun exec-char-fix (x)
       (declare (xargs :guard (exec-charp x)))
       (ascii-basic-exec-char-fix x)))

    (local
     (defun ascii-to-exec-char (x)
       (declare (xargs :guard (ascii-basic-exec-charp x)))
       (ascii-basic-exec-char-fix x)))

    (local
     (defun exec-char-to-number (x)
       (declare (xargs :guard (exec-charp x)))
       (char-code (ascii-basic-exec-char-fix x))))

    (local
     (defun exec-char-to-number-bound ()
       (declare (xargs :guard t))
       256))

    ;; constraints:

    (defrule booleanp-of-exec-charp
      (booleanp (exec-charp x))
      :rule-classes :type-prescription)

    (defrule exec-charp-of-exec-char-fix
      (exec-charp (exec-char-fix x)))

    (defrule exec-char-fix-when-exec-charp
      (implies (exec-charp x)
               (equal (exec-char-fix x) x)))

    (defrule ascii-to-exec-char-of-ascii-basic-exec-char-fix
      (equal (ascii-to-exec-char (ascii-basic-exec-char-fix x))
             (ascii-to-exec-char x)))

    (defrule exec-charp-of-ascii-to-exec-char
      (exec-charp (ascii-to-exec-char x)))

    (defrule ascii-to-exec-char-injective
      (equal (equal (ascii-to-exec-char x)
                    (ascii-to-exec-char y))
             (ascii-basic-exec-char-equiv x y)))

    (defrule exec-char-to-number-of-exec-char-fix
      (equal (exec-char-to-number (exec-char-fix x))
             (exec-char-to-number x)))

    (defrule natp-of-exec-char-to-number
      (natp (exec-char-to-number x))
      :rule-classes :type-prescription)

    (defruled exec-char-to-number-injective-lemma ; used below
      (equal (equal (exec-char-to-number x)
                    (exec-char-to-number y))
             (equal (exec-char-fix x)
                    (exec-char-fix y))))

    (defrule posp-of-exec-char-to-number-bound
      (posp (exec-char-to-number-bound))
      :rule-classes :type-prescription)

    (defrule exec-char-to-number-below-bound
      (< (exec-char-to-number x)
         (exec-char-to-number-bound))
      :rule-classes :linear))

  (fty::deffixtype exec-char
    :pred exec-charp
    :fix exec-char-fix
    :equiv exec-char-equiv
    :define t
    :forward t)

  (defrule exec-char-to-number-injective
    (equal (equal (exec-char-to-number x)
                  (exec-char-to-number y))
           (exec-char-equiv x y))
    :enable exec-char-to-number-injective-lemma)

  (fty::deffixequiv ascii-to-exec-char
    :args ((x ascii-basic-exec-charp)))

  (fty::deffixequiv exec-char-to-number
    :args ((x exec-charp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk basic-exec-charp (x)
  :returns (yes/no booleanp)
  :short "Recognize the basic execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the characters in
     the image of the injection from the ASCII characters."))
  (exists (ascii)
          (and (ascii-basic-exec-charp ascii)
               (equal x (ascii-to-exec-char ascii))))
  ///

  (defrule exec-charp-when-basic-exec-charp
    (implies (basic-exec-charp x)
             (exec-charp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ext-exec-charp (x)
  :returns (yes/no booleanp)
  :short "Recognize the extended execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the non-basic exec-characters."))
  (and (exec-charp x)
       (not (basic-exec-charp x)))
  ///

  (defruled exec-charp-alt-def
    (equal (exec-charp x)
           (or (basic-exec-charp x)
               (ext-exec-charp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-to-exec-char-number ((x ascii-basic-exec-charp))
  :returns (number natp :rule-classes :type-prescription)
  :short "Number of the basic execution character
          corresponding to an ASCII character."
  (exec-char-to-number (ascii-to-exec-char x))
  :hooks (:fix))
