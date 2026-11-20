; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ versions
  :parents (unicode)
  :short "Versions of the Unicode Standard."
  :long
  (xdoc::topstring
   (xdoc::p
    "The properties of code points change from one version
     of the Unicode Standard to the next:
     each version assigns characters to code points
     that were unassigned before,
     and occasionally changes a property of an assigned one.
     So every function of this library
     whose result depends on the Unicode Character Database
     takes the version as an argument.")
   (xdoc::p
    "The version is always explicit.
     There is no default version,
     and no value of the type means `the latest version':
     the result of a function of this library, for given arguments,
     does not change when support for a new version is added.
     Which version a use of the library needs
     is for that use to say.
     For example, a model of a programming language
     whose identifiers are defined in terms of @('XID_Start')
     has to pick the version of Unicode
     that the implementation being modeled uses,
     which may differ between releases of that implementation.")
   (xdoc::p
    "The supported versions are the ones for which
     the directory @('data') has a subdirectory of generated tables.
     The file @('README.md') in this directory
     says how to add a version;
     doing so adds a case to the type defined here
     and to the functions that select the tables,
     and changes nothing else.")
   (xdoc::h3 "From a version to a later one")
   (xdoc::p
    "The Unicode Standard promises
     that some things do not change in later versions:
     these are its stability policies, cited as [Stability]
     (see @(see unicode) for the reference).
     For the supported versions, in the order of @(tsee version<=),
     the following are theorems of this library.
     They are proved by evaluation on the tables,
     for each pair of versions,
     so adding a version checks them for that version.")
   (xdoc::ul
    (xdoc::li
     "A code point that is assigned stays assigned:
      see @(see assigned-across-versions).")
    (xdoc::li
     "A code point that has @('XID_Start') or @('XID_Continue') keeps it,
      and an identifier stays an identifier:
      see @(see xid-across-versions).")
    (xdoc::li
     "The four normalization forms of text
      whose characters are all assigned stay the same,
      and so do the combining classes and the decompositions
      of assigned characters:
      see @(see normalization-across-versions).")
    (xdoc::li
     "The code points of @('Pattern_White_Space'), of @('Pattern_Syntax')
      and the noncharacters are the same in every version,
      as the standard promises [Stability, Property Value Stability].
      In the supported versions the same holds
      for the bidirectional control characters, the join controls,
      the variation selectors, the deprecated characters,
      the default ignorable code points
      and the prepended concatenation marks,
      though the standard does not promise it.
      Each of these properties has a theorem
      whose name ends with @('-same-in-all-versions'),
      in the topic of the property.")
    (xdoc::li
     "The @('General_Category') of an assigned character can change.
      The changes between two versions are computed by
      @(tsee general-category-changes-of-assigned);
      in the supported versions there is one:
      see @(see general-category-stability)."))
   (xdoc::p
    "To compare the code points of any property in two versions,
     use the @(see range-operations):
     for example, the difference of the ranges of @('XID_Start')
     in a version and in an earlier one
     is the list of the code points that got the property."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum version
  :short "Fixtype of the supported versions of the Unicode Standard."
  :long
  (xdoc::topstring
   (xdoc::p
    "A version is identified by its three numbers,
     written as in the standard, with a @('v') in front:
     the constructor for Unicode 16.0.0 is @('(version-v16.0.0)')."))
  (:v16.0.0 ())
  (:v17.0.0 ())
  (:v18.0.0 ())
  :pred versionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-string ((ver versionp))
  :returns (string stringp)
  :short "The usual name of a version of the Unicode Standard."
  (version-case ver
                :v16.0.0 "16.0.0"
                :v17.0.0 "17.0.0"
                :v18.0.0 "18.0.0"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled version-fix-in-terms-of-version-case
  :short "The fixing function of versions, as a choice among the versions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This rule is disabled.
     When it is enabled,
     a term that takes a version as an argument
     is split into one case for each supported version,
     and in each case the version is a constant.
     This is how a statement about every version
     is proved by evaluation, one version at a time."))
  (equal (version-fix ver)
         (version-case ver
                       :v16.0.0 (version-v16.0.0)
                       :v17.0.0 (version-v17.0.0)
                       :v18.0.0 (version-v18.0.0)))
  :enable (version-fix-when-v16.0.0
           version-fix-when-v17.0.0
           version-fix-when-v18.0.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-rank ((ver versionp))
  :returns (rank natp :rule-classes (:rewrite :type-prescription))
  :short "The position of a version among the supported versions,
          in the order in which they were released, starting from 0."
  (version-case ver
                :v16.0.0 0
                :v17.0.0 1
                :v18.0.0 2)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define version<= ((ver1 versionp) (ver2 versionp))
  :returns (yes/no booleanp)
  :short "Check if a version of Unicode is another version
          or was released before it."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the order in which the theorems
     about what stays the same from a version to a later one
     are stated: for example, a code point
     that has the @('XID_Start') property in a version
     has it in every later version.
     The order is reflexive, transitive, antisymmetric and total."))
  (<= (version-rank ver1) (version-rank ver2))
  :hooks (:fix)

  ///

  (defrule version<=-reflexive
    (version<= ver ver))

  (defruled version<=-transitive
    (implies (and (version<= ver1 ver2)
                  (version<= ver2 ver3))
             (version<= ver1 ver3)))

  (defruled version<=-antisymmetric
    (implies (and (version<= ver1 ver2)
                  (version<= ver2 ver1))
             (equal (version-fix ver1)
                    (version-fix ver2)))
    :enable (version-rank
             version-fix-in-terms-of-version-case))

  (defrule version<=-total
    (or (version<= ver1 ver2)
        (version<= ver2 ver1))
    :rule-classes nil))
