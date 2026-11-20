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
     and changes nothing else."))
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
