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
(include-book "maps")

(include-book "data/v16.0.0/confusables")
(include-book "data/v17.0.0/confusables")
(include-book "data/v18.0.0/confusables")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ confusables
  :parents (unicode)
  :short "The prototypes of the characters
          that can be confused with other characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Many characters of Unicode look like other characters,
     or like sequences of other characters:
     U+0441 CYRILLIC SMALL LETTER ES looks like
     U+0063 LATIN SMALL LETTER C,
     and U+0153 LATIN SMALL LIGATURE OE looks like
     the letter o followed by the letter e.
     Unicode Security Mechanisms [UTS #39, Section 4]
     has data for telling when two strings look alike.
     The data, in the file @('confusables.txt'),
     gives to each of several thousand characters a prototype:
     a sequence of one or more characters
     that stands for what the character looks like.
     A character that the file does not list is its own prototype.
     Characters that look alike have the same prototype;
     in the examples, the prototype of U+0441 is U+0063,
     and that of U+0153 is U+006F, U+0065.")
   (xdoc::p
    "Here we have the prototypes, for each supported version of Unicode.
     The data is not stable:
     a later version can give a character another prototype.
     What the prototypes are for is the skeleton of a string,
     by which strings that look alike are found:
     see @(see skeleton).")
   (xdoc::p
    "Each line of the file has a third field,
     which is always @('MA') and is obsolete; we do not keep it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prototypes ((ver versionp))
  :returns (map prototype-mapp)
  :short "The map from the code points that the file @('confusables.txt')
          lists to their prototypes, in a version of Unicode."
  (version-case ver
                :v16.0.0 *prototype-v16.0.0*
                :v17.0.0 *prototype-v17.0.0*
                :v18.0.0 *prototype-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define prototype ((cp code-point-p) (ver versionp))
  :returns (cps code-point-listp)
  :short "The prototype of a code point, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the sequence that the file @('confusables.txt')
     gives to the code point if the file lists it,
     and otherwise the code point itself, as a list of one element
     [UTS #39, Section 4]."))
  (b* ((cp (code-point-fix cp)))
    (or (prototype-map-lookup cp (prototypes ver))
        (list cp)))
  :hooks (:fix)

  ///

  (defrule true-listp-of-prototype
    (code-point-listp (prototype cp ver))
    :rule-classes ((:type-prescription
                    :corollary (true-listp (prototype cp ver))))
    :disable prototype)

  (defrule consp-of-prototype
    (consp (prototype cp ver))
    :rule-classes :type-prescription)

  (defrule scalar-value-listp-of-prototype
    (implies (scalar-value-p cp)
             (scalar-value-listp (prototype cp ver)))))

;;;;;;;;;;;;;;;;;;;;

(define own-prototype-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is its own prototype,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check that the file @('confusables.txt')
     does not list the code point."))
  (equal (prototype cp ver)
         (list (code-point-fix cp)))
  :hooks (:fix)

  ///

  (defruled prototype-when-own-prototype-p
    (implies (own-prototype-p cp ver)
             (equal (prototype cp ver)
                    (list (code-point-fix cp))))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist own-prototype-listp (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check if every code point of a list is its own prototype,
          in a version of Unicode."
  (own-prototype-p x ver)

  ///

  (fty::deffixequiv own-prototype-listp
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (own-prototype-listp x ver)
             :in-theory (enable own-prototype-listp)))))

;;;;;;;;;;;;;;;;;;;;

(define replace-by-prototypes ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp :hints (("Goal" :induct t)))
  :short "Replace the code points of a list by their prototypes,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the third step of the skeleton [UTS #39, Section 4]:
     the prototypes of the code points of the list, concatenated."))
  (cond ((endp cps) nil)
        (t (append (prototype (car cps) ver)
                   (replace-by-prototypes (cdr cps) ver))))
  :hooks (:fix)

  ///

  (defrule scalar-value-listp-of-replace-by-prototypes
    (implies (scalar-value-listp cps)
             (scalar-value-listp (replace-by-prototypes cps ver)))
    :induct t)

  (defrule consp-of-replace-by-prototypes
    (equal (consp (replace-by-prototypes cps ver))
           (consp cps))
    :induct t)

  (defrule replace-by-prototypes-of-append
    (equal (replace-by-prototypes (append cps1 cps2) ver)
           (append (replace-by-prototypes cps1 ver)
                   (replace-by-prototypes cps2 ver)))
    :induct (replace-by-prototypes cps1 ver))

  (defrule replace-by-prototypes-when-own-prototype-listp
    (implies (own-prototype-listp cps ver)
             (equal (replace-by-prototypes cps ver)
                    (code-point-list-fix cps)))
    :induct t
    :enable (own-prototype-listp
             prototype-when-own-prototype-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection prototype-theorems
  :short "Each code point of a prototype is its own prototype."
  :long
  (xdoc::topstring
   (xdoc::p
    "So replacing code points by their prototypes a second time
     changes nothing.
     We prove this by checking, for each version,
     that no code point of a prototype in the table is itself in the table;
     so adding a version checks it for that version.")
   (xdoc::p
    "This is not enough for taking the skeleton a second time
     to change nothing, because the skeleton also normalizes the prototypes:
     see @(see skeleton-idempotence)."))

  (local
   (define none-in-map-p ((cps scalar-value-listp) (map prototype-mapp))
     :returns (yes/no booleanp)
     (or (endp cps)
         (and (not (prototype-map-lookup (scalar-value-fix (car cps)) map))
              (none-in-map-p (cdr cps) map)))
     :hooks nil))

  (local
   (define entry-ok ((cp code-point-p) (map prototype-mapp))
     :returns (yes/no booleanp)
     (none-in-map-p (prototype-map-lookup cp map) map)
     :hooks nil))

  (local
   (std::deflist entry-ok-listp (x map)
     :guard (and (code-point-listp x)
                 (prototype-mapp map))
     (entry-ok x map)))

  (defrulel entry-ok-listp-of-all-code-points
    (entry-ok-listp (all-code-points) (prototypes ver))
    :enable (prototypes
             (:e all-code-points))
    :disable entry-ok-listp-of-cons)

  (defrulel own-prototype-listp-when-none-in-map-p
    (implies (and (scalar-value-listp cps)
                  (none-in-map-p cps (prototypes ver)))
             (own-prototype-listp cps ver))
    :induct t
    :enable (none-in-map-p
             own-prototype-listp
             own-prototype-p
             prototype))

  (defrule own-prototype-listp-of-prototype
    (own-prototype-listp (prototype cp ver) ver)
    :enable (prototype
             entry-ok
             own-prototype-listp
             own-prototype-p)
    :use (:instance entry-ok-when-member-equal-of-entry-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (map (prototypes ver))))

  (defrule own-prototype-listp-of-replace-by-prototypes
    (own-prototype-listp (replace-by-prototypes cps ver) ver)
    :induct t
    :enable replace-by-prototypes)

  (defrule replace-by-prototypes-of-replace-by-prototypes
    (equal (replace-by-prototypes (replace-by-prototypes cps ver) ver)
           (replace-by-prototypes cps ver))))
