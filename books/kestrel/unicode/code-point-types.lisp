; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "general-category")
(include-book "noncharacters")
(include-book "range-operations")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-point-types
  :parents (unicode)
  :short "The seven basic types of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode Standard divides the code points into seven types
     [Unicode, Section 2.4, Table 2-3]
     [Unicode, Section 3.4, Definition D10a, `Code point type'].
     The type of a code point is determined by
     its @('General_Category') (see @(see general-category))
     and, for the code points to which no character is assigned,
     by the property @('Noncharacter_Code_Point')
     (see @(see noncharacters)):")
   (xdoc::ul
    (xdoc::li
     "Graphic: letters, marks, numbers, punctuation, symbols and spaces.
      These are the general categories
      whose abbreviations start with @('L'), @('M'), @('N'), @('P')
      and @('S'), and @('Zs'), which is @('Space_Separator').")
    (xdoc::li
     "Format: characters that are not visible
      and that affect the characters around them,
      and the line and paragraph separators.
      These are the general categories
      @('Cf') (@('Format')), @('Zl') (@('Line_Separator'))
      and @('Zp') (@('Paragraph_Separator')).")
    (xdoc::li
     "Control: the 65 control codes,
      U+0000 to U+001F and U+007F to U+009F.
      This is the general category @('Cc') (@('Control')).")
    (xdoc::li
     "Private-use: the code points whose use
      is left to private agreement.
      This is the general category @('Co') (@('Private_Use')).")
    (xdoc::li
     "Surrogate: the code points U+D800 to U+DFFF,
      which are reserved for the UTF-16 encoding form.
      This is the general category @('Cs') (@('Surrogate')).")
    (xdoc::li
     "Noncharacter: the 66 code points
      that are permanently reserved for internal use.
      Their general category is @('Cn') (@('Unassigned')).")
    (xdoc::li
     "Reserved: the code points that are reserved for future assignment.
      Their general category is also @('Cn')."))
   (xdoc::p
    "The graphic and format code points are the ones
     that have a name (see @(see names));
     each code point of the other five types has a label,
     which is made from its type (see @(see code-point-labels)).")
   (xdoc::p
    "@(tsee code-point-basic-type) gives the type of a code point,
     and @(tsee basic-type-ranges) gives the code points of a type
     as a list of ranges.
     The theorems are in @(see code-point-types-theorems)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum basic-type
  :short "Fixtype of the basic types of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the seven types of
     [Unicode, Section 2.4, Table 2-3],
     which the Unicode Standard calls
     the basic types of code points, or code point types
     [Unicode, Section 3.4, Definition D10a].
     See @(see code-point-types) for what each one is."))
  (:graphic ())
  (:format ())
  (:control ())
  (:private-use ())
  (:surrogate ())
  (:noncharacter ())
  (:reserved ())
  :pred basic-type-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-basic-type ((cp code-point-p) (ver versionp))
  :returns (type basic-type-p)
  :short "The basic type of a code point, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type follows from the @('General_Category') of the code point
     [Unicode, Section 2.4, Table 2-3],
     except that the code points whose general category is @('Unassigned')
     are of two types:
     noncharacter if the code point has
     the property @('Noncharacter_Code_Point'),
     and reserved otherwise.
     The general categories that are not listed in the definition
     are those of the graphic code points."))
  (b* ((gc (code-point-general-category cp ver)))
    (general-category-case
     gc
     :format (basic-type-format)
     :line-separator (basic-type-format)
     :paragraph-separator (basic-type-format)
     :control (basic-type-control)
     :private-use (basic-type-private-use)
     :surrogate (basic-type-surrogate)
     :unassigned (if (noncharacter-p cp ver)
                     (basic-type-noncharacter)
                   (basic-type-reserved))
     :otherwise (basic-type-graphic)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define basic-type-ranges ((type basic-type-p) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points of a given basic type,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges are computed at each call
     from the ranges of the general categories
     and of the noncharacters.
     They are in normal form:
     in increasing order, with at least one code point
     between two consecutive ranges
     (see @(tsee ranges-normalized-p)).
     The theorem says that these are the code points
     to which @(tsee code-point-basic-type) gives the type."))
  (b* ((control
        (general-category-ranges (general-category-control) ver))
       (surrogate
        (general-category-ranges (general-category-surrogate) ver))
       (private-use
        (general-category-ranges (general-category-private-use) ver))
       (unassigned
        (general-category-ranges (general-category-unassigned) ver))
       (format
        (ranges-union
         (general-category-ranges (general-category-format) ver)
         (ranges-union
          (general-category-ranges (general-category-line-separator) ver)
          (general-category-ranges (general-category-paragraph-separator)
                                   ver)))))
    (basic-type-case
     type
     :graphic (ranges-complement
               (ranges-union
                format
                (ranges-union
                 control
                 (ranges-union
                  private-use
                  (ranges-union surrogate unassigned)))))
     :format format
     :control (ranges-normalize control)
     :private-use (ranges-normalize private-use)
     :surrogate (ranges-normalize surrogate)
     :noncharacter (ranges-intersection unassigned
                                        (noncharacter-ranges ver))
     :reserved (ranges-difference unassigned
                                  (noncharacter-ranges ver))))
  :hooks (:fix)

  ///

  (defrule ranges-normalized-p-of-basic-type-ranges
    (ranges-normalized-p (basic-type-ranges type ver)))

  (defruled code-point-in-basic-type-ranges
    (equal (code-point-in-ranges-p cp (basic-type-ranges type ver))
           (equal (code-point-basic-type cp ver)
                  (basic-type-fix type)))
    :enable (code-point-basic-type
             noncharacter-p
             code-point-in-general-category-ranges
             basic-type-fix
             equal-of-general-category-format
             equal-of-general-category-line-separator
             equal-of-general-category-paragraph-separator
             equal-of-general-category-control
             equal-of-general-category-private-use
             equal-of-general-category-surrogate
             equal-of-general-category-unassigned)
    :disable ((:e general-category-format)
              (:e general-category-line-separator)
              (:e general-category-paragraph-separator)
              (:e general-category-control)
              (:e general-category-private-use)
              (:e general-category-surrogate)
              (:e general-category-unassigned)))

  (defruled equal-of-code-point-basic-type
    (equal (equal (code-point-basic-type cp ver) type)
           (and (basic-type-p type)
                (code-point-in-ranges-p cp (basic-type-ranges type ver))))
    :enable code-point-in-basic-type-ranges
    :disable basic-type-ranges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection code-point-types-theorems
  :short "Which code points have four of the types,
          the assigned code points in terms of the types,
          and the type of a code point in a later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first four theorems hold in every supported version;
     they are proved by evaluation on the tables, for each version.
     The control codes are U+0000 to U+001F and U+007F to U+009F
     [Unicode, Section 2.4].
     The private-use code points are U+E000 to U+F8FF,
     and the last two planes without their last two code points:
     U+F0000 to U+FFFFD and U+100000 to U+10FFFD.
     The surrogate code points are those of @(tsee surrogate-p).
     The noncharacters are the code points
     that have the property @('Noncharacter_Code_Point')
     (see @(tsee noncharacter-p), whose theorem says which they are).")
   (xdoc::p
    "A code point is assigned, in the sense of @(tsee assigned-p),
     exactly when it is neither a noncharacter nor reserved.")
   (xdoc::p
    "A code point that is not reserved in a version
     has the same type in every later version.
     For four of the types the Unicode Standard promises as much:
     the control codes, the private-use code points,
     the surrogates and the noncharacters are sets that never change
     [Stability, Property Value Stability].
     A code point to which a character is assigned
     stays assigned to it [Stability, Encoding Stability],
     so a code point that is graphic or format stays one or the other.
     That a graphic character stays graphic
     and a format character stays a format character
     is not promised:
     the @('General_Category') of a character can change.
     It is the case between the supported versions.
     The theorem is proved by evaluation on the tables,
     for each pair of versions:
     each range of the code points of a type in the earlier version
     is within such a range of the later one.
     It is disabled by default."))

  (defrulel basic-type-kind-in-terms-of-equal
    (implies (basic-type-p type)
             (and (equal (equal (basic-type-kind type) :control)
                         (equal type (basic-type-control)))
                  (equal (equal (basic-type-kind type) :private-use)
                         (equal type (basic-type-private-use)))
                  (equal (equal (basic-type-kind type) :surrogate)
                         (equal type (basic-type-surrogate)))
                  (equal (equal (basic-type-kind type) :noncharacter)
                         (equal type (basic-type-noncharacter)))
                  (equal (equal (basic-type-kind type) :reserved)
                         (equal type (basic-type-reserved)))))
    :enable (equal-of-basic-type-control
             equal-of-basic-type-private-use
             equal-of-basic-type-surrogate
             equal-of-basic-type-noncharacter
             equal-of-basic-type-reserved)
    :disable ((:e basic-type-control)
              (:e basic-type-private-use)
              (:e basic-type-surrogate)
              (:e basic-type-noncharacter)
              (:e basic-type-reserved)))

  (defruledl basic-type-ranges-in-terms-of-version-case
    (implies (syntaxp (not (quotep ver)))
             (equal (basic-type-ranges type ver)
                    (version-case
                     ver
                     :v16.0.0 (basic-type-ranges type (version-v16.0.0))
                     :v17.0.0 (basic-type-ranges type (version-v17.0.0))
                     :v18.0.0 (basic-type-ranges type (version-v18.0.0)))))
    :enable version-fix-in-terms-of-version-case
    :disable basic-type-ranges-of-version-fix-ver
    :use basic-type-ranges-of-version-fix-ver)

  ;; The control codes.

  (defrulel control-ranges
    (equal (basic-type-ranges (basic-type-control) ver)
           (list (range #x0000 #x001F)
                 (range #x007F #x009F)))
    :enable basic-type-ranges-in-terms-of-version-case)

  (defruled code-point-basic-type-is-control
    (equal (basic-type-case (code-point-basic-type cp ver) :control)
           (b* ((cp (code-point-fix cp)))
             (or (<= cp #x1F)
                 (and (<= #x7F cp)
                      (<= cp #x9F)))))
    :enable (equal-of-code-point-basic-type
             code-point-in-ranges-p
             code-point-in-range-p)
    :disable ((:e basic-type-control)))

  ;; The private-use code points.

  (defrulel private-use-ranges
    (equal (basic-type-ranges (basic-type-private-use) ver)
           (list (range #xE000 #xF8FF)
                 (range #xF0000 #xFFFFD)
                 (range #x100000 #x10FFFD)))
    :enable basic-type-ranges-in-terms-of-version-case)

  (defruled code-point-basic-type-is-private-use
    (equal (basic-type-case (code-point-basic-type cp ver) :private-use)
           (b* ((cp (code-point-fix cp)))
             (or (and (<= #xE000 cp)
                      (<= cp #xF8FF))
                 (and (<= #xF0000 cp)
                      (<= cp #xFFFFD))
                 (and (<= #x100000 cp)
                      (<= cp #x10FFFD)))))
    :enable (equal-of-code-point-basic-type
             code-point-in-ranges-p
             code-point-in-range-p)
    :disable ((:e basic-type-private-use)))

  ;; The surrogates.

  (defrulel surrogate-ranges
    (equal (basic-type-ranges (basic-type-surrogate) ver)
           (list (range #xD800 #xDFFF)))
    :enable basic-type-ranges-in-terms-of-version-case)

  (defruled code-point-basic-type-is-surrogate
    (equal (basic-type-case (code-point-basic-type cp ver) :surrogate)
           (surrogate-p cp))
    :enable (equal-of-code-point-basic-type
             surrogate-p-alt-def
             code-point-in-ranges-p
             code-point-in-range-p)
    :disable ((:e basic-type-surrogate)
              surrogate-p))

  ;; The noncharacters.

  (defrulel noncharacter-ranges-within-ranges-of-the-type
    (ranges-within-ranges-p
     (noncharacter-ranges ver)
     (basic-type-ranges (basic-type-noncharacter) ver))
    :enable (basic-type-ranges-in-terms-of-version-case
             noncharacter-ranges))

  (defrulel code-point-basic-type-when-noncharacter-p
    (implies (noncharacter-p cp ver)
             (equal (code-point-basic-type cp ver)
                    (basic-type-noncharacter)))
    :enable (equal-of-code-point-basic-type
             noncharacter-p)
    :disable ((:e basic-type-noncharacter)
              basic-type-ranges)
    :use (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                    (subs (noncharacter-ranges ver))
                    (sups (basic-type-ranges (basic-type-noncharacter)
                                             ver))))

  (defrulel noncharacter-p-when-code-point-basic-type-is-noncharacter
    (implies (equal (code-point-basic-type cp ver)
                    (basic-type-noncharacter))
             (noncharacter-p cp ver))
    :rule-classes nil
    :enable code-point-basic-type)

  (defruled code-point-basic-type-is-noncharacter
    (equal (basic-type-case (code-point-basic-type cp ver) :noncharacter)
           (noncharacter-p cp ver))
    :cases ((noncharacter-p cp ver))
    :use noncharacter-p-when-code-point-basic-type-is-noncharacter)

  ;; The assigned code points.

  (defruled assigned-p-in-terms-of-basic-type
    (equal (assigned-p cp ver)
           (b* ((type (code-point-basic-type cp ver)))
             (not (or (basic-type-case type :noncharacter)
                      (basic-type-case type :reserved)))))
    :enable (assigned-p
             code-point-basic-type))

  ;; The type of a code point in a later version.

  (defruledl basic-type-fix-in-terms-of-basic-type-case
    (equal (basic-type-fix type)
           (basic-type-case type
                            :graphic (basic-type-graphic)
                            :format (basic-type-format)
                            :control (basic-type-control)
                            :private-use (basic-type-private-use)
                            :surrogate (basic-type-surrogate)
                            :noncharacter (basic-type-noncharacter)
                            :reserved (basic-type-reserved)))
    :enable basic-type-fix)

  (defruledl basic-type-ranges-in-terms-of-basic-type-case
    (implies (syntaxp (not (quotep type)))
             (equal (basic-type-ranges type ver)
                    (basic-type-case
                     type
                     :graphic (basic-type-ranges (basic-type-graphic) ver)
                     :format (basic-type-ranges (basic-type-format) ver)
                     :control (basic-type-ranges (basic-type-control) ver)
                     :private-use (basic-type-ranges (basic-type-private-use)
                                                     ver)
                     :surrogate (basic-type-ranges (basic-type-surrogate)
                                                   ver)
                     :noncharacter (basic-type-ranges
                                    (basic-type-noncharacter) ver)
                     :reserved (basic-type-ranges (basic-type-reserved)
                                                  ver))))
    :enable basic-type-fix-in-terms-of-basic-type-case
    :disable basic-type-ranges-of-basic-type-fix-type
    :use basic-type-ranges-of-basic-type-fix-type)

  (defrulel basic-type-ranges-within-ranges-of-later-version
    (implies (and (version<= ver1 ver2)
                  (not (basic-type-case type :reserved)))
             (ranges-within-ranges-p (basic-type-ranges type ver1)
                                     (basic-type-ranges type ver2)))
    :rule-classes nil
    :enable (version<=
             version-rank
             basic-type-ranges-in-terms-of-basic-type-case
             basic-type-ranges-in-terms-of-version-case))

  (defruled code-point-basic-type-of-later-version
    (implies (and (version<= ver1 ver2)
                  (not (basic-type-case (code-point-basic-type cp ver1)
                                        :reserved)))
             (equal (code-point-basic-type cp ver2)
                    (code-point-basic-type cp ver1)))
    :enable equal-of-code-point-basic-type
    :disable basic-type-ranges
    :use ((:instance basic-type-ranges-within-ranges-of-later-version
                     (type (code-point-basic-type cp ver1)))
          (:instance code-point-in-basic-type-ranges
                     (type (code-point-basic-type cp ver1))
                     (ver ver1))
          (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                     (subs (basic-type-ranges (code-point-basic-type cp ver1)
                                              ver1))
                     (sups (basic-type-ranges (code-point-basic-type cp ver1)
                                              ver2))))))
