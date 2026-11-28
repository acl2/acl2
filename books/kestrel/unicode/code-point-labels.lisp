; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "code-point-types")
(include-book "name-aliases")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "std/typed-lists/character-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-point-labels
  :parents (unicode)
  :short "The labels of the code points that have no name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code points of five of the seven basic types
     (see @(see code-point-types)) have no name:
     the value of their @('Name') property is the empty string.
     For those the Unicode Standard has labels
     [Unicode, Section 4.8.2, Table 4-9].
     A label is made of the type in small letters, a hyphen,
     and the code point in hexadecimal with four to six digits
     (see @(tsee code-point-hex)):")
   (xdoc::ul
    (xdoc::li "@('control-0009') for the control code U+0009;")
    (xdoc::li "@('private-use-E000') for the private-use code point U+E000;")
    (xdoc::li "@('surrogate-D800') for the surrogate code point U+D800;")
    (xdoc::li "@('noncharacter-FFFF') for the noncharacter U+FFFF;")
    (xdoc::li "@('reserved-0378') for U+0378,
               which is reserved in the supported versions."))
   (xdoc::p
    "The label of a code point depends on the version of Unicode
     only in that a reserved code point of a version
     can be assigned to a character in a later version,
     and then it has a name and no label.")
   (xdoc::p
    "The labels are in the namespace of
     the names of the characters and of their aliases
     (see @(see names) and @(see name-aliases)):
     no label matches a name or an alias,
     even by the loose matching of names
     [UAX #44, Section 5.9.2, rule UAX44-LM2].
     The Unicode Character Database, and other documents,
     write a label between angle brackets,
     as in @('<control-0009>'),
     to tell it from a name;
     the brackets are not part of the label.")
   (xdoc::p
    "@(tsee code-point-label) gives the label of a code point,
     and the empty string for a code point that has a name.
     @(tsee code-point-name-or-label) gives
     the name of a code point that has one and the label of the others,
     so that every code point has an identifier
     [Unicode, Section 4.8.3].
     @(tsee label-code-point) gives the code point of a label,
     and @(tsee loose-label-code-point) does the same with loose matching.
     The theorems are in @(see code-point-labels-theorems)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define basic-type-label-prefix ((type basic-type-p))
  :returns (prefix stringp)
  :short "The start of the labels of the code points of a basic type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type in small letters followed by a hyphen
     [Unicode, Section 4.8.2, Table 4-9].
     It is the empty string for the two types
     whose code points have names and no labels."))
  (basic-type-case type
                   :graphic ""
                   :format ""
                   :control "control-"
                   :private-use "private-use-"
                   :surrogate "surrogate-"
                   :noncharacter "noncharacter-"
                   :reserved "reserved-")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-label ((cp code-point-p) (ver versionp))
  :returns (label stringp)
  :short "The label of a code point, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The label is the start that goes with the type of the code point,
     followed by the code point in hexadecimal
     [Unicode, Section 4.8.2].
     The result is the empty string
     for a graphic or format code point,
     which has a name and no label."))
  (b* ((prefix (basic-type-label-prefix (code-point-basic-type cp ver)))
       ((when (equal prefix "")) ""))
    (string-append prefix (code-point-hex cp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-name-or-label ((cp code-point-p) (ver versionp))
  :returns (string stringp)
  :short "The name of a code point that has one, and the label of the others,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is what the Unicode Standard suggests
     for an interface that has to show something for every code point
     [Unicode, Section 4.8.3].
     The result is never the empty string,
     and no two code points have the same one
     (see @(see code-point-labels-theorems))."))
  (b* ((name (code-point-name cp ver))
       ((unless (equal name "")) name))
    (code-point-label cp ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define key-chars-value-after ((prefix stringp) (key-chars character-listp))
  :returns (value? acl2::maybe-natp)
  :short "The number written in hexadecimal after a given start,
          in the characters of a key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the characters do not begin with the start,
     or if what follows it is empty
     or is not made of digits and of the small letters @('a') to @('f')."))
  (b* ((prefix-chars (coerce (acl2::str-fix prefix) 'list))
       ((unless (and (< (len prefix-chars) (len key-chars))
                     (equal (take (len prefix-chars) key-chars)
                            prefix-chars)))
        nil))
    (hex-chars-value (nthcdr (len prefix-chars) key-chars) 0))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define label-key-value ((key stringp))
  :returns (value? acl2::maybe-natp)
  :short "The number at the end of the key of a label."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key of a label is the label without its hyphens
     and with small letters only (see @(tsee name-loose-key)):
     for example, the key of @('private-use-E000')
     is @('privateusee000').
     This function recognizes the five starts of such keys
     and reads the number that follows.
     The result is @('nil') if the string does not have that form.
     It can be a number for a string that is not the key of a label,
     for example if the number has too many digits;
     @(tsee label-key-code-point) checks that."))
  (b* ((key-chars (coerce (acl2::str-fix key) 'list)))
    (or (key-chars-value-after "control" key-chars)
        (key-chars-value-after "privateuse" key-chars)
        (key-chars-value-after "surrogate" key-chars)
        (key-chars-value-after "noncharacter" key-chars)
        (key-chars-value-after "reserved" key-chars)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define label-key-code-point ((key stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point whose label has a given key,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if no label has that key.
     The code point is read from the end of the key,
     and it is the result only if the key of its label is the given key."))
  (b* ((key (acl2::str-fix key))
       (ver (version-fix ver))
       (value? (label-key-value key)))
    (and value?
         (code-point-p value?)
         (equal (name-loose-key (code-point-label value? ver)) key)
         value?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define loose-label-code-point ((label stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point whose label matches a string loosely,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the loose matching of names
     [UAX #44, Section 5.9.2, rule UAX44-LM2] applied to the labels:
     the string matches a label if the two have the same key
     (see @(tsee name-loose-key)).
     For example, @('CONTROL-0009'), @('control 0009')
     and @('Control_0009') all give U+0009.
     The number of digits is not loose:
     @('control-9') and @('control-00009') match no label.
     The result is @('nil') if the string matches no label."))
  (label-key-code-point (name-loose-key label) ver)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define label-code-point ((label stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point that has a given label, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the string is not the label of a code point.
     The string has to be the label exactly, without angle brackets:
     the code point is found by loose matching,
     and it is the result only if its label is the string."))
  (b* ((label (acl2::str-fix label))
       (cp? (loose-label-code-point label ver)))
    (and cp?
         (equal (code-point-label cp? ver) label)
         cp?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection code-point-labels-theorems
  :short "Every code point has a name or a label and not both,
          a label gives its code point back,
          no label matches a name or an alias loosely,
          and a label is the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code points without a name are those of five basic types;
     this is the theorem of @(see names-theorems)
     about the general categories of those code points,
     put in terms of the types.
     The code points without a label are those of the other two types.
     So the label of a code point is the empty string
     exactly when its name is not,
     and @(tsee code-point-name-or-label) is never the empty string.")
   (xdoc::p
    "From the label of a code point,
     @(tsee loose-label-code-point) and @(tsee label-code-point)
     find the code point.
     In the other direction, by the definitions,
     the code point that @(tsee label-code-point) gives for a string
     has that string as its label.
     The first is proved from a check on every code point
     with each of the five starts of labels:
     the number at the end of the key of the label is the code point.")
   (xdoc::p
    "No name and no alias matches a label loosely,
     and no label matches a name or an alias.
     This is proved from a check on every code point, for each version:
     the key of its name, and of each of its aliases,
     is not the key of a label.
     Two aliases come close:
     the keys of @('PRIVATE USE-1') and @('PRIVATE USE-2'),
     which are aliases of the control codes U+0091 and U+0092,
     are @('privateuse1') and @('privateuse2').
     They are not keys of labels,
     because a label has at least four digits.
     With the theorems about names and aliases
     (see @(see names-theorems) and @(see name-aliases-theorems)),
     this is the promise of the Unicode Standard
     that names, aliases and labels are unique in one namespace
     [Unicode, Section 4.8],
     for the names, aliases and labels of a version.
     So two code points for which @(tsee code-point-name-or-label)
     gives strings that match loosely are the same code point.")
   (xdoc::p
    "The last theorem follows from the one about the types
     (see @(see code-point-types-theorems)):
     a code point that is not reserved in a version
     has the same label, or no label, in every later version.
     It is disabled by default."))

  ;; The names and the labels in terms of the types.

  (defruled code-point-name-is-empty-in-terms-of-basic-type
    (equal (equal (code-point-name cp ver) "")
           (b* ((type (code-point-basic-type cp ver)))
             (not (or (basic-type-case type :graphic)
                      (basic-type-case type :format)))))
    :enable (code-point-name-is-empty-in-terms-of-general-category
             code-point-basic-type))

  ;; What is checked on every code point:
  ;; with each of the five starts of labels,
  ;; the label is not empty
  ;; and the number at the end of its key is the code point.

  (local
   (define label-with-prefix-ok ((cp code-point-p) (prefix stringp))
     :returns (yes/no booleanp)
     (b* ((label (string-append prefix (code-point-hex cp))))
       (and (not (equal label ""))
            (equal (label-key-value (name-loose-key label))
                   (code-point-fix cp))))
     :hooks nil))

  (local
   (define label-ok ((cp code-point-p))
     :returns (yes/no booleanp)
     (and (label-with-prefix-ok cp "control-")
          (label-with-prefix-ok cp "private-use-")
          (label-with-prefix-ok cp "surrogate-")
          (label-with-prefix-ok cp "noncharacter-")
          (label-with-prefix-ok cp "reserved-"))
     :hooks nil))

  (local
   (std::deflist label-ok-listp (x)
     :guard (code-point-listp x)
     (label-ok x)))

  (defrulel label-ok-listp-of-all-code-points
    (label-ok-listp (all-code-points))
    :enable ((:e all-code-points))
    :disable label-ok-listp-of-cons)

  (defrulel label-ok-holds
    (label-ok cp)
    :rule-classes nil
    :use (:instance label-ok-when-member-equal-of-label-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points)))
    :enable (label-ok
             label-with-prefix-ok)
    :disable label-ok-when-member-equal-of-label-ok-listp)

  (defruled code-point-label-is-empty-in-terms-of-basic-type
    (equal (equal (code-point-label cp ver) "")
           (b* ((type (code-point-basic-type cp ver)))
             (or (basic-type-case type :graphic)
                 (basic-type-case type :format))))
    :enable (code-point-label
             basic-type-label-prefix
             label-ok
             label-with-prefix-ok)
    :use label-ok-holds)

  (defrule code-point-label-is-empty
    (equal (equal (code-point-label cp ver) "")
           (not (equal (code-point-name cp ver) "")))
    :enable (code-point-label-is-empty-in-terms-of-basic-type
             code-point-name-is-empty-in-terms-of-basic-type))

  (defrule code-point-name-or-label-is-not-empty
    (not (equal (code-point-name-or-label cp ver) ""))
    :enable code-point-name-or-label)

  ;; A label gives its code point back.

  (defrule label-key-value-of-name-loose-key-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (equal (label-key-value
                     (name-loose-key (code-point-label cp ver)))
                    (code-point-fix cp)))
    :enable (code-point-label
             basic-type-label-prefix
             code-point-name-is-empty-in-terms-of-basic-type
             label-ok
             label-with-prefix-ok)
    :disable code-point-label-is-empty
    :use label-ok-holds)

  (defrule label-key-code-point-of-name-loose-key-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (equal (label-key-code-point
                     (name-loose-key (code-point-label cp ver))
                     ver)
                    (code-point-fix cp)))
    :enable label-key-code-point)

  (defrule loose-label-code-point-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (equal (loose-label-code-point (code-point-label cp ver) ver)
                    (code-point-fix cp)))
    :enable loose-label-code-point)

  (defrule label-code-point-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (equal (label-code-point (code-point-label cp ver) ver)
                    (code-point-fix cp)))
    :enable label-code-point)

  ;; In the other direction.

  (defrule code-point-label-of-label-code-point
    (implies (label-code-point label ver)
             (equal (code-point-label (label-code-point label ver) ver)
                    (acl2::str-fix label)))
    :enable label-code-point)

  (defrule name-loose-key-of-code-point-label-of-loose-label-code-point
    (implies (loose-label-code-point label ver)
             (equal (name-loose-key
                     (code-point-label (loose-label-code-point label ver)
                                       ver))
                    (name-loose-key label)))
    :enable (loose-label-code-point
             label-key-code-point))

  ;; What is checked on every code point, for each version:
  ;; the key of its name, and of each of its aliases,
  ;; is not the key of a label.

  (local
   (define name-alias-not-label-ok ((alias name-alias-p) (ver versionp))
     :returns (yes/no booleanp)
     (not (label-key-code-point (name-loose-key (name-alias->name alias))
                                ver))
     :hooks nil))

  (local
   (std::deflist name-alias-not-label-ok-listp (x ver)
     :guard (and (name-alias-listp x)
                 (versionp ver))
     (name-alias-not-label-ok x ver)))

  (local
   (define not-label-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp))
          (ver (version-fix ver)))
       (and (not (label-key-code-point
                  (name-loose-key (code-point-name cp ver))
                  ver))
            (name-alias-not-label-ok-listp (code-point-name-aliases cp ver)
                                           ver)))
     :hooks nil))

  (local
   (std::deflist not-label-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (not-label-ok x ver)))

  (defrulel not-label-ok-listp-of-all-code-points
    (not-label-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable not-label-ok-listp-of-cons)

  (defrulel not-label-ok-holds
    (not-label-ok cp ver)
    :rule-classes nil
    :use (:instance not-label-ok-when-member-equal-of-not-label-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable not-label-ok)

  ;; No name and no alias matches a label loosely.

  (defrule not-label-key-code-point-of-name-loose-key-of-code-point-name
    (not (label-key-code-point (name-loose-key (code-point-name cp ver))
                               ver))
    :use not-label-ok-holds
    :enable not-label-ok)

  (defrulel name-alias-not-label-ok-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (name-alias-not-label-ok alias (version-fix ver)))
    :rule-classes nil
    :use not-label-ok-holds
    :enable not-label-ok)

  (defrule not-label-key-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (label-key-code-point
                   (name-loose-key (name-alias->name alias))
                   ver)))
    :use name-alias-not-label-ok-when-member-of-code-point-name-aliases
    :enable name-alias-not-label-ok)

  (defrule not-loose-label-code-point-of-code-point-name
    (not (loose-label-code-point (code-point-name cp ver) ver))
    :enable loose-label-code-point)

  (defrule not-label-code-point-of-code-point-name
    (not (label-code-point (code-point-name cp ver) ver))
    :enable label-code-point)

  (defrule not-loose-label-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (loose-label-code-point (name-alias->name alias) ver)))
    :enable loose-label-code-point)

  (defrule not-label-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (label-code-point (name-alias->name alias) ver)))
    :enable label-code-point)

  ;; No label matches a name or an alias loosely.

  (defrule not-loose-name-code-point-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (not (loose-name-code-point (code-point-label cp ver) ver)))
    :disable (not-label-key-code-point-of-name-loose-key-of-code-point-name
              name-loose-key-of-code-point-name-of-loose-name-code-point)
    :use ((:instance
           name-loose-key-of-code-point-name-of-loose-name-code-point
           (name (code-point-label cp ver)))
          (:instance
           not-label-key-code-point-of-name-loose-key-of-code-point-name
           (cp (loose-name-code-point (code-point-label cp ver) ver)))))

  (defrule not-name-code-point-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (not (name-code-point (code-point-label cp ver) ver)))
    :enable name-code-point)

  (defrule not-loose-name-alias-code-point-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (not (loose-name-alias-code-point (code-point-label cp ver)
                                               ver)))
    :disable (not-label-key-code-point-when-member-of-code-point-name-aliases
              find-name-alias-by-key-of-loose-name-alias-code-point
              name-loose-key-of-find-name-alias-by-key
              member-equal-of-find-name-alias-by-key)
    :use ((:instance
           find-name-alias-by-key-of-loose-name-alias-code-point
           (name (code-point-label cp ver)))
          (:instance
           name-loose-key-of-find-name-alias-by-key
           (key (name-loose-key (code-point-label cp ver)))
           (aliases (code-point-name-aliases
                     (loose-name-alias-code-point (code-point-label cp ver)
                                                  ver)
                     ver)))
          (:instance
           member-equal-of-find-name-alias-by-key
           (key (name-loose-key (code-point-label cp ver)))
           (aliases (code-point-name-aliases
                     (loose-name-alias-code-point (code-point-label cp ver)
                                                  ver)
                     ver)))
          (:instance
           not-label-key-code-point-when-member-of-code-point-name-aliases
           (alias (find-name-alias-by-key
                   (name-loose-key (code-point-label cp ver))
                   (code-point-name-aliases
                    (loose-name-alias-code-point (code-point-label cp ver)
                                                 ver)
                    ver)))
           (cp (loose-name-alias-code-point (code-point-label cp ver)
                                            ver)))))

  (defrule not-name-alias-code-point-of-code-point-label
    (implies (equal (code-point-name cp ver) "")
             (not (name-alias-code-point (code-point-label cp ver) ver)))
    :enable name-alias-code-point)

  ;; No two code points have the same name or label.

  (defrule code-points-equal-when-names-or-labels-match-loosely
    (implies (equal (name-loose-key (code-point-name-or-label cp1 ver))
                    (name-loose-key (code-point-name-or-label cp2 ver)))
             (equal (code-point-fix cp1)
                    (code-point-fix cp2)))
    :rule-classes nil
    :enable (code-point-name-or-label
             loose-name-code-point)
    :disable (name-key-code-point-of-name-loose-key-of-code-point-name
              label-key-code-point-of-name-loose-key-of-code-point-label
              not-loose-name-code-point-of-code-point-label)
    :use ((:instance
           name-key-code-point-of-name-loose-key-of-code-point-name
           (cp cp1))
          (:instance
           name-key-code-point-of-name-loose-key-of-code-point-name
           (cp cp2))
          (:instance
           label-key-code-point-of-name-loose-key-of-code-point-label
           (cp cp1))
          (:instance
           label-key-code-point-of-name-loose-key-of-code-point-label
           (cp cp2))
          (:instance not-loose-name-code-point-of-code-point-label
                     (cp cp1))
          (:instance not-loose-name-code-point-of-code-point-label
                     (cp cp2))))

  (defrule code-points-equal-when-names-or-labels-equal
    (implies (equal (code-point-name-or-label cp1 ver)
                    (code-point-name-or-label cp2 ver))
             (equal (code-point-fix cp1)
                    (code-point-fix cp2)))
    :rule-classes nil
    :use code-points-equal-when-names-or-labels-match-loosely)

  ;; The label of a code point in a later version.

  (defruled code-point-label-of-later-version
    (implies (and (version<= ver1 ver2)
                  (not (basic-type-case (code-point-basic-type cp ver1)
                                        :reserved)))
             (equal (code-point-label cp ver2)
                    (code-point-label cp ver1)))
    :enable (code-point-label
             code-point-basic-type-of-later-version)))
