; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "names")
(include-book "data/v16.0.0/name-aliases")
(include-book "data/v17.0.0/name-aliases")
(include-book "data/v18.0.0/name-aliases")

(include-book "std/util/defconsts" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "std/typed-lists/character-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ name-aliases
  :parents (unicode)
  :short "The aliases of the names of the characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some code points have one or more aliases,
     which are further names for them
     [Unicode, Section 4.8].
     They are the values of the property @('Name_Alias')
     [UAX #44, Section 5.1],
     and the file @('NameAliases.txt')
     of the Unicode Character Database lists them.
     Each alias has one of five types (see @(tsee name-alias-type)).
     For example, the control code U+000A, which has no name,
     has the aliases @('LINE FEED'), @('NEW LINE') and @('END OF LINE')
     of type @('control'),
     and @('LF'), @('NL') and @('EOL') of type @('abbreviation');
     and U+FEFF ZERO WIDTH NO-BREAK SPACE
     has the alias @('BYTE ORDER MARK') of type @('alternate'),
     and @('BOM') and @('ZWNBSP') of type @('abbreviation').")
   (xdoc::p
    "An alias is written like a name,
     and the names and the aliases are in one namespace:
     no alias is the name of a code point
     or the alias of another code point,
     even when the strings are compared
     by the loose matching of names
     [UAX #44, Section 5.9.2, rule UAX44-LM2],
     for which see @(tsee name-loose-key).
     So a name or an alias identifies one code point.")
   (xdoc::p
    "@(tsee code-point-name-aliases) gives the aliases of a code point,
     with their types, in the order of the file.
     @(tsee name-alias-code-point) gives the code point
     of which a string is an alias,
     and @(tsee loose-name-alias-code-point) does the same
     with loose matching.
     @(tsee name-or-alias-code-point)
     and @(tsee loose-name-or-alias-code-point)
     accept a name or an alias.
     The theorems are in @(see name-aliases-theorems).")
   (xdoc::p
    "A program that accepts only the aliases of some types
     can find the type of the alias that a string is
     with @(tsee find-name-alias),
     in the aliases of the code point that
     @(tsee name-alias-code-point) gives.")
   (xdoc::p
    "The Unicode Standard has two more kinds of identifiers
     in the same namespace:
     the labels of the code points without a name,
     for which see @(see code-point-labels),
     and the names of sequences of code points
     (file @('NamedSequences.txt')),
     which this library does not have."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-alias-table ((ver versionp))
  :returns (map name-alias-mapp)
  :short "The table of the aliases of names, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode 16.0.0 has 477 aliases, of 384 code points;
     Unicode 17.0.0 and 18.0.0 have 481, of 388 code points."))
  (version-case ver
                :v16.0.0 *name-aliases-v16.0.0*
                :v17.0.0 *name-aliases-v17.0.0*
                :v18.0.0 *name-aliases-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-name-aliases ((cp code-point-p) (ver versionp))
  :returns (aliases name-alias-listp)
  :short "The aliases of the name of a code point
          (the property @('Name_Alias')), in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the list of the aliases, each with its type,
     in the order of the file @('NameAliases.txt').
     It is the empty list for a code point that has no alias,
     which is the case of most code points."))
  (name-alias-map-lookup cp (name-alias-table ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-name-alias ((name stringp) (aliases name-alias-listp))
  :returns (alias? name-alias-option-p)
  :short "The first alias of a list that is a given string."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if no alias of the list is that string.
     The alias found has the string and its type."))
  (b* (((when (endp aliases)) nil)
       (alias (name-alias-fix (car aliases)))
       ((when (equal (name-alias->name alias) (acl2::str-fix name))) alias))
    (find-name-alias name (cdr aliases)))
  :hooks (:fix)

  ///

  (defrule name-alias->name-of-find-name-alias
    (implies (find-name-alias name aliases)
             (equal (name-alias->name (find-name-alias name aliases))
                    (acl2::str-fix name)))
    :induct t)

  (defrule member-equal-of-find-name-alias
    (implies (and (find-name-alias name aliases)
                  (name-alias-listp aliases))
             (member-equal (find-name-alias name aliases) aliases))
    :induct t)

  (defrule find-name-alias-when-member-equal
    (implies (member-equal alias aliases)
             (find-name-alias (name-alias->name alias) aliases))
    :induct t))

;;;;;;;;;;;;;;;;;;;;

(define find-name-alias-by-key ((key stringp) (aliases name-alias-listp))
  :returns (alias? name-alias-option-p)
  :short "The first alias of a list whose string has a given key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key of a string is what is left of it
     when the differences that the loose matching of names ignores
     are removed (see @(tsee name-loose-key)).
     The result is @('nil')
     if the string of no alias of the list has that key."))
  (b* (((when (endp aliases)) nil)
       (alias (name-alias-fix (car aliases)))
       ((when (equal (name-loose-key (name-alias->name alias))
                     (acl2::str-fix key)))
        alias))
    (find-name-alias-by-key key (cdr aliases)))
  :hooks (:fix)

  ///

  (defrule name-loose-key-of-find-name-alias-by-key
    (implies (find-name-alias-by-key key aliases)
             (equal (name-loose-key
                     (name-alias->name (find-name-alias-by-key key aliases)))
                    (acl2::str-fix key)))
    :induct t)

  (defrule member-equal-of-find-name-alias-by-key
    (implies (and (find-name-alias-by-key key aliases)
                  (name-alias-listp aliases))
             (member-equal (find-name-alias-by-key key aliases) aliases))
    :induct t)

  (defrule find-name-alias-by-key-when-member-equal
    (implies (member-equal alias aliases)
             (find-name-alias-by-key
              (name-loose-key (name-alias->name alias)) aliases))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-alias-keys-add-aliases ((aliases name-alias-listp)
                                     (cp code-point-p)
                                     (keys name-key-mapp))
  :returns (new-keys name-key-mapp)
  :short "Add the keys of the aliases of a code point
          to a map from keys to code points."
  (b* (((when (endp aliases)) (name-key-map-fix keys))
       (keys (treemap::update (name-loose-key
                               (name-alias->name (car aliases)))
                              (code-point-fix cp)
                              (name-key-map-fix keys))))
    (name-alias-keys-add-aliases (cdr aliases) cp keys))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define name-alias-keys-add ((cps code-point-listp)
                             (table name-alias-mapp)
                             (keys name-key-mapp))
  :returns (new-keys name-key-mapp)
  :short "Add the keys of the aliases of some code points
          to a map from keys to code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is how the table that goes back from an alias to its code point
     is computed from the table of the aliases,
     when this book is certified."))
  (b* (((when (endp cps)) (name-key-map-fix keys))
       (cp (code-point-fix (car cps)))
       (keys (name-alias-keys-add-aliases (name-alias-map-lookup cp table)
                                          cp
                                          keys)))
    (name-alias-keys-add (cdr cps) table keys))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(defconsts *name-alias-keys-v16.0.0*
  (name-alias-keys-add (all-code-points)
                       *name-aliases-v16.0.0*
                       (treemap::empty)))

(defconsts *name-alias-keys-v17.0.0*
  (name-alias-keys-add (all-code-points)
                       *name-aliases-v17.0.0*
                       (treemap::empty)))

(defconsts *name-alias-keys-v18.0.0*
  (name-alias-keys-add (all-code-points)
                       *name-aliases-v18.0.0*
                       (treemap::empty)))

; The keys are as many as the aliases: no two aliases have the same key.

(assert-event (name-key-mapp *name-alias-keys-v16.0.0*))
(assert-event (name-key-mapp *name-alias-keys-v17.0.0*))
(assert-event (name-key-mapp *name-alias-keys-v18.0.0*))

(assert-event (equal (treemap::size *name-alias-keys-v16.0.0*) 477))
(assert-event (equal (treemap::size *name-alias-keys-v17.0.0*) 481))
(assert-event (equal (treemap::size *name-alias-keys-v18.0.0*) 481))

;;;;;;;;;;;;;;;;;;;;

(define name-alias-keys ((ver versionp))
  :returns (keys name-key-mapp)
  :short "The table from the keys of the aliases to their code points,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *name-alias-keys-v16.0.0*
                :v17.0.0 *name-alias-keys-v17.0.0*
                :v18.0.0 *name-alias-keys-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-alias-key-code-point ((key stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point that has an alias with a given key,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if no alias has that key.
     The code point is looked up in the table of the keys,
     and it is the result only if one of its aliases has the key:
     so the result has such an alias
     whatever is in the table of the keys."))
  (b* ((key (acl2::str-fix key))
       (cp? (name-key-map-lookup key (name-alias-keys ver))))
    (and cp?
         (find-name-alias-by-key key (code-point-name-aliases cp? ver))
         cp?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define loose-name-alias-code-point ((name stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point that has an alias that matches a string loosely,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the loose matching of names
     [UAX #44, Section 5.9.2, rule UAX44-LM2] applied to the aliases:
     the string matches an alias if the two have the same key
     (see @(tsee name-loose-key)).
     For example, @('line feed'), @('Line_Feed') and @('LINEFEED')
     all give U+000A.
     The result is @('nil') if the string matches no alias."))
  (name-alias-key-code-point (name-loose-key name) ver)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-alias-code-point ((name stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point of which a string is an alias,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the string is not an alias.
     The string has to be the alias exactly:
     the code point is found by loose matching,
     and it is the result only if the string is one of its aliases."))
  (b* ((cp? (loose-name-alias-code-point name ver)))
    (and cp?
         (find-name-alias name (code-point-name-aliases cp? ver))
         cp?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-or-alias-code-point ((name stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point of which a string is the name or an alias,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the string is neither.
     No string is both
     (see @(see name-aliases-theorems))."))
  (or (name-code-point name ver)
      (name-alias-code-point name ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define loose-name-or-alias-code-point ((name stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point whose name or one of whose aliases
          matches a string loosely, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the string matches
     no name and no alias.
     No string matches both a name and an alias
     (see @(see name-aliases-theorems))."))
  (or (loose-name-code-point name ver)
      (loose-name-alias-code-point name ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection name-aliases-theorems
  :short "An alias gives its code point back,
          no alias matches a name or another alias loosely,
          aliases are written like names,
          and an alias of a version is an alias in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about an alias of a code point are stated
     for a member of the list that @(tsee code-point-name-aliases) gives.
     They are checked on every alias of every code point, for each version.")
   (xdoc::p
    "From an alias of a code point,
     @(tsee loose-name-alias-code-point) and @(tsee name-alias-code-point)
     find the code point.
     So two code points that have aliases with the same key
     are the same code point:
     no alias of a code point matches loosely an alias of another.
     In the other direction, by the definitions,
     the code point that @(tsee name-alias-code-point) gives for a string
     has that string as an alias.")
   (xdoc::p
    "No alias matches a name loosely, and no name matches an alias.
     With the theorems about names (see @(see names-theorems)),
     this is the promise of the Unicode Standard
     that the names and the aliases are unique in one namespace
     [Unicode, Section 4.8] [UAX #44, Section 5.9.2],
     for the names and the aliases of a version.
     So @(tsee name-or-alias-code-point)
     and @(tsee loose-name-or-alias-code-point)
     give the code point back
     both from its name and from each of its aliases.")
   (xdoc::p
    "An alias, like a name, is made of
     capital letters, digits, spaces and hyphens,
     and is not empty.")
   (xdoc::p
    "The last theorem is the stability of aliases
     [Unicode, Section 4.8]:
     an alias of a code point in a version, with its type,
     is an alias of that code point in every later version.
     It is disabled by default."))

  ;; What is checked on each alias of a code point:
  ;; it is made of the characters of names and is not empty;
  ;; its key gives the code point;
  ;; and its key is the key of no name.

  (local
   (define name-alias-ok ((alias name-alias-p)
                          (cp code-point-p)
                          (ver versionp))
     :returns (yes/no booleanp)
     (b* ((name (name-alias->name alias))
          (key (name-loose-key name)))
       (and (name-char-listp (coerce name 'list))
            (not (equal name ""))
            (equal (name-alias-key-code-point key ver)
                   (code-point-fix cp))
            (not (name-key-code-point key ver))))
     :hooks nil))

  (local
   (std::deflist name-alias-ok-listp (x cp ver)
     :guard (and (name-alias-listp x)
                 (code-point-p cp)
                 (versionp ver))
     (name-alias-ok x cp ver)))

  ;; What is checked on every code point:
  ;; the above for each of its aliases,
  ;; and that the key of its name is the key of no alias.

  (local
   (define name-aliases-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp))
          (ver (version-fix ver)))
       (and (name-alias-ok-listp (code-point-name-aliases cp ver) cp ver)
            (not (name-alias-key-code-point
                  (name-loose-key (code-point-name cp ver))
                  ver))))
     :hooks nil))

  (local
   (std::deflist name-aliases-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (name-aliases-ok x ver)))

  (defrulel name-aliases-ok-listp-of-all-code-points
    (name-aliases-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable name-aliases-ok-listp-of-cons)

  (defrulel name-aliases-ok-holds
    (name-aliases-ok cp ver)
    :rule-classes nil
    :use (:instance name-aliases-ok-when-member-equal-of-name-aliases-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable name-aliases-ok)

  (defrulel name-alias-ok-when-member-equal-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (name-alias-ok alias (code-point-fix cp) (version-fix ver)))
    :rule-classes nil
    :use name-aliases-ok-holds
    :enable name-aliases-ok)

  ;; An alias gives its code point back.

  (defrule name-alias-key-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (equal (name-alias-key-code-point
                     (name-loose-key (name-alias->name alias))
                     ver)
                    (code-point-fix cp)))
    :use name-alias-ok-when-member-equal-of-code-point-name-aliases
    :enable name-alias-ok)

  (defrule loose-name-alias-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (equal (loose-name-alias-code-point (name-alias->name alias) ver)
                    (code-point-fix cp)))
    :enable loose-name-alias-code-point)

  (defrule name-alias-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (equal (name-alias-code-point (name-alias->name alias) ver)
                    (code-point-fix cp)))
    :enable name-alias-code-point
    :use (:instance find-name-alias-when-member-equal
                    (aliases (code-point-name-aliases cp ver))))

  ;; In the other direction.

  (defrule find-name-alias-of-name-alias-code-point
    (implies (name-alias-code-point name ver)
             (find-name-alias name
                              (code-point-name-aliases
                               (name-alias-code-point name ver)
                               ver)))
    :enable name-alias-code-point)

  (defrule find-name-alias-by-key-of-loose-name-alias-code-point
    (implies (loose-name-alias-code-point name ver)
             (find-name-alias-by-key (name-loose-key name)
                                     (code-point-name-aliases
                                      (loose-name-alias-code-point name ver)
                                      ver)))
    :enable (loose-name-alias-code-point
             name-alias-key-code-point))

  ;; No two code points have aliases that match loosely.

  (defrule code-points-equal-when-aliases-match-loosely
    (implies (and (member-equal alias1 (code-point-name-aliases cp1 ver))
                  (member-equal alias2 (code-point-name-aliases cp2 ver))
                  (equal (name-loose-key (name-alias->name alias1))
                         (name-loose-key (name-alias->name alias2))))
             (equal (code-point-fix cp1)
                    (code-point-fix cp2)))
    :rule-classes nil
    :disable name-alias-key-code-point-when-member-of-code-point-name-aliases
    :use ((:instance
           name-alias-key-code-point-when-member-of-code-point-name-aliases
           (alias alias1)
           (cp cp1))
          (:instance
           name-alias-key-code-point-when-member-of-code-point-name-aliases
           (alias alias2)
           (cp cp2))))

  ;; No alias matches a name loosely, and no name matches an alias.

  (defrule not-name-key-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (name-key-code-point
                   (name-loose-key (name-alias->name alias))
                   ver)))
    :use name-alias-ok-when-member-equal-of-code-point-name-aliases
    :enable name-alias-ok)

  (defrule not-loose-name-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (loose-name-code-point (name-alias->name alias) ver)))
    :enable loose-name-code-point)

  (defrule not-name-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (name-code-point (name-alias->name alias) ver)))
    :enable name-code-point)

  (defrule not-loose-name-alias-code-point-of-code-point-name
    (not (loose-name-alias-code-point (code-point-name cp ver) ver))
    :enable (loose-name-alias-code-point
             name-aliases-ok)
    :use name-aliases-ok-holds)

  (defrule not-name-alias-code-point-of-code-point-name
    (not (name-alias-code-point (code-point-name cp ver) ver))
    :enable name-alias-code-point)

  ;; A name or an alias gives the code point back.

  (defrule loose-name-or-alias-code-point-of-code-point-name
    (implies (not (equal (code-point-name cp ver) ""))
             (equal (loose-name-or-alias-code-point (code-point-name cp ver)
                                                    ver)
                    (code-point-fix cp)))
    :enable loose-name-or-alias-code-point)

  (defrule name-or-alias-code-point-of-code-point-name
    (implies (not (equal (code-point-name cp ver) ""))
             (equal (name-or-alias-code-point (code-point-name cp ver) ver)
                    (code-point-fix cp)))
    :enable name-or-alias-code-point)

  (defrule
    loose-name-or-alias-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (equal (loose-name-or-alias-code-point (name-alias->name alias)
                                                    ver)
                    (code-point-fix cp)))
    :enable loose-name-or-alias-code-point)

  (defrule name-or-alias-code-point-when-member-of-code-point-name-aliases
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (equal (name-or-alias-code-point (name-alias->name alias) ver)
                    (code-point-fix cp)))
    :enable name-or-alias-code-point)

  ;; Aliases are written like names.

  (defrule name-char-listp-of-name-alias->name-when-member
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (name-char-listp (acl2::explode (name-alias->name alias))))
    :use name-alias-ok-when-member-equal-of-code-point-name-aliases
    :enable name-alias-ok)

  (defrule name-alias->name-not-empty-when-member
    (implies (member-equal alias (code-point-name-aliases cp ver))
             (not (equal (name-alias->name alias) "")))
    :use name-alias-ok-when-member-equal-of-code-point-name-aliases
    :enable name-alias-ok)

  ;; The stability of aliases.

  (local
   (define aliases-stable-ok ((cp code-point-p))
     :returns (yes/no booleanp)
     (and (subsetp-equal (code-point-name-aliases cp (version-v16.0.0))
                         (code-point-name-aliases cp (version-v17.0.0)))
          (subsetp-equal (code-point-name-aliases cp (version-v17.0.0))
                         (code-point-name-aliases cp (version-v18.0.0))))
     :hooks nil))

  (local
   (std::deflist aliases-stable-ok-listp (x)
     :guard (code-point-listp x)
     (aliases-stable-ok x)))

  (defrulel aliases-stable-ok-listp-of-all-code-points
    (aliases-stable-ok-listp (all-code-points))
    :enable ((:e all-code-points))
    :disable aliases-stable-ok-listp-of-cons)

  (defrulel aliases-stable-ok-holds
    (aliases-stable-ok cp)
    :rule-classes nil
    :use (:instance
          aliases-stable-ok-when-member-equal-of-aliases-stable-ok-listp
          (acl2::a (code-point-fix cp))
          (x (all-code-points)))
    :enable aliases-stable-ok
    :disable aliases-stable-ok-when-member-equal-of-aliases-stable-ok-listp)

  (defruledl code-point-name-aliases-in-terms-of-version-case
    (implies (syntaxp (not (quotep ver)))
             (equal (code-point-name-aliases cp ver)
                    (version-case
                     ver
                     :v16.0.0 (code-point-name-aliases cp (version-v16.0.0))
                     :v17.0.0 (code-point-name-aliases cp (version-v17.0.0))
                     :v18.0.0 (code-point-name-aliases cp (version-v18.0.0)))))
    :enable version-fix-in-terms-of-version-case
    :disable code-point-name-aliases-of-version-fix-ver
    :use code-point-name-aliases-of-version-fix-ver)

  (defruled code-point-name-aliases-of-later-version
    (implies (and (version<= ver1 ver2)
                  (member-equal alias (code-point-name-aliases cp ver1)))
             (member-equal alias (code-point-name-aliases cp ver2)))
    :enable (aliases-stable-ok
             version<=
             version-rank
             code-point-name-aliases-in-terms-of-version-case)
    :use aliases-stable-ok-holds))
