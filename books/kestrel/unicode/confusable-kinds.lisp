; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "skeleton")
(include-book "mixed-scripts")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ confusable-kinds
  :parents (confusable-detection)
  :short "The three classes of confusable strings:
          single-script, mixed-script and whole-script confusables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode Security Mechanisms [UTS #39, Section 4]
     divides the pairs of confusable strings (see @(tsee confusable-p))
     by the scripts of the two strings,
     that is, by their resolved script sets
     (see @(tsee resolved-script-set)):")
   (xdoc::ul
    (xdoc::li
     "Two strings are single-script confusables
      if they are confusable
      and their resolved script sets have an element in common.
      The example of the specification is
      the word ``ljeto'' written with five letters, and written with four,
      the first of which is U+01C9 LATIN SMALL LETTER LJ.")
    (xdoc::li
     "Two strings are mixed-script confusables
      if they are confusable
      and their resolved script sets have no element in common.
      The example is ``paypal'' written in Latin letters,
      and written with U+0430 CYRILLIC SMALL LETTER A
      in place of each letter a.")
    (xdoc::li
     "Two strings are whole-script confusables
      if they are mixed-script confusables
      and each of them is a single-script string.
      The example is ``scope'' written in Latin letters,
      and written in Cyrillic letters."))
   (xdoc::p
    "So two confusable strings are
     single-script confusables or mixed-script confusables, and not both;
     and whole-script confusables are mixed-script confusables.")
   (xdoc::p
    "The specification also asks
     whether a string has a whole-script confusable at all,
     which is a question about every other string.
     That is not here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define single-script-confusable-p ((cps1 code-point-listp)
                                    (cps2 code-point-listp)
                                    (ver versionp))
  :guard (and (right-to-left-free-p cps1 ver)
              (right-to-left-free-p cps2 ver))
  :returns (yes/no booleanp)
  :short "Check if two lists of code points are single-script confusables,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that they are confusable
     and that their resolved script sets have an element in common
     [UTS #39, Section 4].
     The guard is the one of @(tsee confusable-p)."))
  (and (confusable-p cps1 cps2 ver)
       (script-sets-intersect-p (resolved-script-set cps1 ver)
                                (resolved-script-set cps2 ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define mixed-script-confusable-p ((cps1 code-point-listp)
                                   (cps2 code-point-listp)
                                   (ver versionp))
  :guard (and (right-to-left-free-p cps1 ver)
              (right-to-left-free-p cps2 ver))
  :returns (yes/no booleanp)
  :short "Check if two lists of code points are mixed-script confusables,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that they are confusable
     and that their resolved script sets have no element in common
     [UTS #39, Section 4].
     The guard is the one of @(tsee confusable-p)."))
  (and (confusable-p cps1 cps2 ver)
       (not (script-sets-intersect-p (resolved-script-set cps1 ver)
                                     (resolved-script-set cps2 ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define whole-script-confusable-p ((cps1 code-point-listp)
                                   (cps2 code-point-listp)
                                   (ver versionp))
  :guard (and (right-to-left-free-p cps1 ver)
              (right-to-left-free-p cps2 ver))
  :returns (yes/no booleanp)
  :short "Check if two lists of code points are whole-script confusables,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that they are mixed-script confusables
     and that each of them is single-script
     [UTS #39, Section 4].
     The guard is the one of @(tsee confusable-p)."))
  (and (mixed-script-confusable-p cps1 cps2 ver)
       (single-script-p cps1 ver)
       (single-script-p cps2 ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection confusable-kinds-theorems
  :short "How the three classes of confusable strings
          relate to each other."

  (defruled confusable-p-in-terms-of-kinds
    (equal (confusable-p cps1 cps2 ver)
           (or (single-script-confusable-p cps1 cps2 ver)
               (mixed-script-confusable-p cps1 cps2 ver)))
    :enable (single-script-confusable-p
             mixed-script-confusable-p))

  (defrule not-mixed-script-confusable-p-when-single-script-confusable-p
    (implies (single-script-confusable-p cps1 cps2 ver)
             (not (mixed-script-confusable-p cps1 cps2 ver)))
    :enable (single-script-confusable-p
             mixed-script-confusable-p))

  (defrule mixed-script-confusable-p-when-whole-script-confusable-p
    (implies (whole-script-confusable-p cps1 cps2 ver)
             (mixed-script-confusable-p cps1 cps2 ver))
    :enable whole-script-confusable-p))
