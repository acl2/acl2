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
(include-book "bidi-left-to-right")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidirectional-skeleton
  :parents (confusable-detection)
  :short "The bidirectional skeleton of a string:
          the skeleton for every string,
          with text from right to left or without."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode Security Mechanisms [UTS #39, Section 4]
     defines the bidirectional skeleton of a string,
     written @('bidiSkeleton') there,
     for a direction of the paragraph:
     from left to right, from right to left,
     or the direction of the first strong character of the string.
     It is the result of four steps:")
   (xdoc::ol
    (xdoc::li
     "Put the code points of the string
      in the order in which they are displayed,
      by the rules of the Unicode Bidirectional Algorithm [UAX #9]
      up to rule L2,
      with the string taken as the whole text
      and the paragraph embedding level set by the direction.")
    (xdoc::li
     "Apply rule L3 of that algorithm:
      move the combining marks after their base characters.")
    (xdoc::li
     "Replace each character that rule L4 of that algorithm
      would draw as its mirror image
      by the value of its @('Bidi_Mirroring_Glyph') property.")
    (xdoc::li
     "Take the internal skeleton of the result
      (see @(tsee internal-skeleton))."))
   (xdoc::p
    "The first three steps are the function @(tsee bidi-display);
     see @(see bidi-displayed-text) for the choices that it makes
     where the two specifications leave room.
     So the bidirectional skeleton is defined here
     for every list of code points: see @(tsee bidi-skeleton).
     Two strings are confusable for a direction
     when they have the same bidirectional skeleton for that direction:
     see @(tsee bidi-confusable-p).")
   (xdoc::p
    "The skeleton of the specification, without qualification,
     is the bidirectional skeleton for a paragraph from left to right,
     and two strings are confusable, without qualification,
     when those skeletons are equal.
     The functions @(tsee skeleton) and @(tsee confusable-p)
     are defined, as the internal skeleton,
     for the lists of code points
     with no character that can make text be displayed from right to left
     (see @(tsee right-to-left-free-p)).
     The theorems here say that they agree with the functions of this book
     on those lists.
     So for a list that may have such characters,
     use the functions of this book
     with the direction from left to right;
     for a list that has none, @(tsee skeleton) is the same and costs less,
     since it does not run the bidirectional algorithm.")
   (xdoc::p
    "The three revisions of [UTS #39]
     that go with the supported versions of Unicode
     define the bidirectional skeleton in the same words."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-skeleton ((cps code-point-listp)
                       (direction paragraph-direction-p)
                       (ver versionp))
  :returns (skeleton code-point-listp)
  :short "The bidirectional skeleton of a list of code points,
          for a direction of the paragraph, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @('bidiSkeleton') of [UTS #39, Section 4]:
     the internal skeleton of the list as it is displayed
     (see @(see bidirectional-skeleton)).
     The skeleton of the specification, written @('skeleton') there,
     is this function for the direction from left to right:
     @('(bidi-skeleton cps (paragraph-direction-left-to-right) ver)').")
   (xdoc::p
    "The result is in Normalization Form D (NFD),
     which is canonical decomposition.
     For a list with no character
     that can make text be displayed from right to left,
     and a direction that is not from right to left,
     the result is the internal skeleton of the list,
     which is what @(tsee skeleton) gives."))
  (internal-skeleton (bidi-display cps direction ver) ver)
  :hooks (:fix)

  ///

  (defrule scalar-value-listp-of-bidi-skeleton
    (implies (scalar-value-listp cps)
             (scalar-value-listp (bidi-skeleton cps direction ver))))

  (defrule nfd-memberp-of-bidi-skeleton
    (nfd-memberp (bidi-skeleton cps direction ver) ver))

  (defrule bidi-skeleton-when-right-to-left-free-p
    (implies (and (right-to-left-free-p cps ver)
                  (not (equal (paragraph-direction-kind direction)
                              :right-to-left)))
             (equal (bidi-skeleton cps direction ver)
                    (skeleton cps ver)))
    :enable skeleton-in-terms-of-internal-skeleton))

;;;;;;;;;;;;;;;;;;;;

(define bidi-confusable-p ((cps1 code-point-listp)
                           (cps2 code-point-listp)
                           (direction paragraph-direction-p)
                           (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if two lists of code points are confusable
          for a direction of the paragraph, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two strings are confusable for a direction if and only if
     they have the same bidirectional skeleton for that direction
     [UTS #39, Section 4].
     Two strings are confusable, without qualification,
     when they are confusable for the direction from left to right.")
   (xdoc::p
    "For each direction, this is an equivalence relation:
     it is reflexive, symmetric and transitive.
     Two lists can be confusable for one direction
     and not for another:
     the specification gives an example,
     which is among the tests of this library.")
   (xdoc::p
    "For two lists with no character
     that can make text be displayed from right to left,
     and a direction that is not from right to left,
     this is @(tsee confusable-p)."))
  (equal (bidi-skeleton cps1 direction ver)
         (bidi-skeleton cps2 direction ver))
  :hooks (:fix)

  ///

  (defrule bidi-confusable-p-reflexive
    (bidi-confusable-p cps cps direction ver))

  (defrule bidi-confusable-p-symmetric
    (equal (bidi-confusable-p cps1 cps2 direction ver)
           (bidi-confusable-p cps2 cps1 direction ver)))

  (defruled bidi-confusable-p-transitive
    (implies (and (bidi-confusable-p cps1 cps2 direction ver)
                  (bidi-confusable-p cps2 cps3 direction ver))
             (bidi-confusable-p cps1 cps3 direction ver)))

  (defrule bidi-confusable-p-when-right-to-left-free-p
    (implies (and (right-to-left-free-p cps1 ver)
                  (right-to-left-free-p cps2 ver)
                  (not (equal (paragraph-direction-kind direction)
                              :right-to-left)))
             (equal (bidi-confusable-p cps1 cps2 direction ver)
                    (confusable-p cps1 cps2 ver)))
    :enable confusable-p))
