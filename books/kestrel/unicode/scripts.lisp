; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "versions")
(include-book "script-tables")

(include-book "data/v16.0.0/scripts")
(include-book "data/v17.0.0/scripts")
(include-book "data/v18.0.0/scripts")
(include-book "data/v16.0.0/script-extensions")
(include-book "data/v17.0.0/script-extensions")
(include-book "data/v18.0.0/script-extensions")

(local (include-book "range-operations"))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ scripts
  :parents (unicode)
  :short "The @('Script') and @('Script_Extensions') properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Script') property gives every code point one script,
     and the @('Script_Extensions') property gives it
     the set of the scripts that it is used with [UAX #24];
     see @(see script-tables) for the values.
     Mixing scripts in an identifier is how many spoofs are made,
     so the tests that detect such mixing
     are defined on these two properties,
     and mostly on the second one.")
   (xdoc::p
    "We take the first property from the file @('Scripts.txt')
     and the second from the file @('ScriptExtensions.txt')
     of the Unicode Character Database, for each supported version.
     The second file lists only the code points
     whose set is not just their script;
     the generated tables have the set of every code point.")
   (xdoc::p
    "The function @(tsee code-point-script)
     gives the script of a code point,
     and @(tsee script-ranges) gives the code points of a script,
     as a list of ranges;
     @(tsee code-point-script-extensions)
     gives the set of scripts of a code point, as a list,
     and @(tsee script-extensions-ranges) gives the code points
     whose set contains a script.
     Theorems say that the two views of each property agree.")
   (xdoc::p
    "Neither property is stable:
     each version of Unicode adds scripts,
     and the script extensions of existing characters are revised."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define script-runs ((ver versionp))
  :returns (runs script-run-listp)
  :short "The @('Script') of every code point,
          as a list of runs, in a version of Unicode."
  (version-case ver
                :v16.0.0 *script-v16.0.0*
                :v17.0.0 *script-v17.0.0*
                :v18.0.0 *script-v18.0.0*)
  :hooks (:fix)

  ///

  (defrule script-runs-cover-all-code-points
    (script-run-list-covers-p 0 #x10FFFF (script-runs ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-script ((cp code-point-p) (ver versionp))
  :returns (script script-p)
  :short "The @('Script') of a code point, in a version of Unicode."
  (script-run-list-lookup cp (script-runs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define script-ranges ((script script-p) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points that have a given @('Script'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges are in increasing order and do not overlap.
     They are computed from the list of runs at each call,
     by going through the whole list."))
  (script-run-list-ranges script (script-runs ver))
  :hooks (:fix)

  ///

  (defruled code-point-in-script-ranges
    (equal (code-point-in-ranges-p cp (script-ranges script ver))
           (equal (code-point-script cp ver)
                  (script-fix script)))
    :enable (code-point-script
             code-point-in-script-run-list-ranges))

  (defruled equal-of-code-point-script
    (equal (equal (code-point-script cp ver) script)
           (and (script-p script)
                (code-point-in-ranges-p cp (script-ranges script ver))))
    :enable code-point-in-script-ranges
    :disable script-ranges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define script-extensions-runs ((ver versionp))
  :returns (runs script-extensions-run-listp)
  :short "The @('Script_Extensions') of every code point,
          as a list of runs, in a version of Unicode."
  (version-case ver
                :v16.0.0 *script-extensions-v16.0.0*
                :v17.0.0 *script-extensions-v17.0.0*
                :v18.0.0 *script-extensions-v18.0.0*)
  :hooks (:fix)

  ///

  (defrule script-extensions-runs-cover-all-code-points
    (script-extensions-run-list-covers-p 0 #x10FFFF
                                         (script-extensions-runs ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-script-extensions ((cp code-point-p) (ver versionp))
  :returns (scripts script-listp)
  :short "The @('Script_Extensions') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is a list of scripts without duplicates,
     which stands for a set; it is never empty.
     The scripts are in the order
     of the file @('ScriptExtensions.txt'),
     which is the order of their four-letter codes."))
  (script-extensions-run-list-lookup cp (script-extensions-runs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define script-extensions-ranges ((script script-p) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          whose @('Script_Extensions') contain a given script,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges are in increasing order and do not overlap.
     They are computed from the list of runs at each call,
     by going through the whole list."))
  (script-extensions-run-list-member-ranges script
                                            (script-extensions-runs ver))
  :hooks (:fix)

  ///

  (defruled code-point-in-script-extensions-ranges
    (iff (code-point-in-ranges-p cp (script-extensions-ranges script ver))
         (member-equal (script-fix script)
                       (code-point-script-extensions cp ver)))
    :enable (code-point-script-extensions
             code-point-in-script-extensions-run-list-member-ranges)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection script-theorems
  :short "Theorems about @('Script') and @('Script_Extensions')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The script extensions of a code point contain its script,
     unless the script is @('Common') or @('Inherited'):
     a character that several scripts share, or that takes the script
     of the character before it,
     can have the set of the scripts it is used with,
     and then the set has neither of those two values.
     The script extensions of a code point are never the empty set.")
   (xdoc::p
    "The first theorem is proved by evaluation
     on the lists of ranges of each script, for each version:
     the code points of a script, less the code points
     whose script extensions contain it, are the empty list.
     So adding a version checks it for that version."))

  (local
   (define script-ok ((script script-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (equal (script-fix script) (script-common))
         (equal (script-fix script) (script-inherited))
         (not (consp (ranges-difference
                      (script-ranges script ver)
                      (script-extensions-ranges script ver)))))
     :hooks nil))

  (local
   (std::deflist script-ok-listp (x ver)
     :guard (and (script-listp x)
                 (versionp ver))
     (script-ok x ver)))

  (defrulel script-ok-listp-of-script-values
    (script-ok-listp (script-values) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e script-values))
    :disable script-ok-listp-of-cons)

  (defrulel script-ok-holds
    (script-ok script ver)
    :rule-classes nil
    :enable script-ok
    :use (:instance script-ok-when-member-equal-of-script-ok-listp
                    (acl2::a (script-fix script))
                    (x (script-values))
                    (ver (version-fix ver))))

  (defrule member-equal-of-code-point-script-and-script-extensions
    (implies (and (not (equal (code-point-script cp ver)
                              (script-common)))
                  (not (equal (code-point-script cp ver)
                              (script-inherited))))
             (member-equal (code-point-script cp ver)
                           (code-point-script-extensions cp ver)))
    :enable (script-ok
             code-point-in-script-ranges)
    :disable ((:e script-common)
              (:e script-inherited))
    :use ((:instance script-ok-holds
                     (script (code-point-script cp ver)))
          (:instance code-point-in-ranges-p-when-ranges-difference-is-empty
                     (ranges1 (script-ranges (code-point-script cp ver) ver))
                     (ranges2 (script-extensions-ranges
                               (code-point-script cp ver) ver)))
          (:instance code-point-in-script-extensions-ranges
                     (script (code-point-script cp ver)))))

  ;; The sets are not empty:
  ;; no run of the tables has the empty list as its value.

  (local
   (define runs-nonempty-p ((runs script-extensions-run-listp))
     :returns (yes/no booleanp)
     (or (endp runs)
         (and (consp (script-extensions-run->value (car runs)))
              (runs-nonempty-p (cdr runs))))
     :hooks nil

     ///

     (defrule consp-of-lookup-when-runs-nonempty-p
       (implies (runs-nonempty-p runs)
                (consp (script-extensions-run-list-lookup cp runs)))
       :induct t
       :enable script-extensions-run-list-lookup)))

  (defrulel runs-nonempty-p-of-script-extensions-runs
    (runs-nonempty-p (script-extensions-runs ver))
    :enable script-extensions-runs)

  (defrule consp-of-code-point-script-extensions
    (consp (code-point-script-extensions cp ver))
    :rule-classes :type-prescription
    :enable code-point-script-extensions))
