; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-controls")
(include-book "bidi-class-tables")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-class-property
  :parents (unicode)
  :short "The @('Bidi_Class') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This property gives every code point
     one of the twenty-three bidirectional classes
     of the Unicode Bidirectional Algorithm [UAX #9, Table 4]:
     see @(tsee bidi-class) for the values.
     The class says whether a character is written
     from left to right or from right to left,
     or how it takes its direction from the characters around it.")
   (xdoc::p
    "We take the property from the file
     @('extracted/DerivedBidiClass.txt')
     of the Unicode Character Database, for each supported version.
     That file gives a class to every code point:
     the code points that are not assigned have default classes,
     which depend on the block they are in,
     so that text of a right-to-left script
     keeps its direction when characters are added to the script.")
   (xdoc::p
    "The function @(tsee code-point-bidi-class)
     gives the class of a code point,
     and @(tsee bidi-class-ranges)
     gives the code points that have a class, as a list of ranges.
     The theorem @('code-point-in-bidi-class-ranges')
     says that the two agree.")
   (xdoc::p
    "The classes of the explicit directional formatting characters
     are also in @(see bidi-controls),
     which has a smaller table of its own;
     a theorem here says that the two tables agree.
     The Bidirectional Algorithm itself is not in this library.")
   (xdoc::p
    "The property is not stable:
     the class of an assigned character is sometimes corrected.
     In the supported versions,
     three Balinese marks, U+1B3A, U+1B3C and U+1B42,
     are @('Nonspacing_Mark') in Unicode 17.0.0
     and @('Left_To_Right') in Unicode 18.0.0."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-class-runs ((ver versionp))
  :returns (runs bidi-class-run-listp)
  :short "The @('Bidi_Class') of every code point,
          as a list of runs, in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-class-v16.0.0*
                :v17.0.0 *bidi-class-v17.0.0*
                :v18.0.0 *bidi-class-v18.0.0*)
  :hooks (:fix)

  ///

  (defrule bidi-class-runs-cover-all-code-points
    (bidi-class-run-list-covers-p 0 #x10FFFF (bidi-class-runs ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-bidi-class ((cp code-point-p) (ver versionp))
  :returns (class bidi-class-p)
  :short "The @('Bidi_Class') of a code point, in a version of Unicode."
  (bidi-class-run-list-lookup cp (bidi-class-runs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-ranges ((class bidi-class-p) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have a given @('Bidi_Class'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges are in increasing order and do not overlap.
     They are computed from the list of runs at each call,
     by going through the whole list."))
  (bidi-class-run-list-ranges class (bidi-class-runs ver))
  :hooks (:fix)

  ///

  (defruled code-point-in-bidi-class-ranges
    (equal (code-point-in-ranges-p cp (bidi-class-ranges class ver))
           (equal (code-point-bidi-class cp ver)
                  (bidi-class-fix class)))
    :enable (code-point-bidi-class
             code-point-in-bidi-class-run-list-ranges))

  (defruled equal-of-code-point-bidi-class
    (equal (equal (code-point-bidi-class cp ver) class)
           (and (bidi-class-p class)
                (code-point-in-ranges-p cp (bidi-class-ranges class ver))))
    :enable code-point-in-bidi-class-ranges
    :disable bidi-class-ranges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-class-formatting-class ((class bidi-class-p))
  :returns (class? bidi-formatting-class-option-p)
  :short "Turn a bidirectional class into a value of the type
          of the classes of the explicit directional formatting characters,
          if it is one of those nine classes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') for the other fourteen classes.
     The type of the nine classes is @(tsee bidi-formatting-class),
     which @(see bidi-controls) uses."))
  (bidi-class-case
   class
   :left-to-right-embedding (bidi-formatting-class-lre)
   :left-to-right-override (bidi-formatting-class-lro)
   :right-to-left-embedding (bidi-formatting-class-rle)
   :right-to-left-override (bidi-formatting-class-rlo)
   :pop-directional-format (bidi-formatting-class-pdf)
   :left-to-right-isolate (bidi-formatting-class-lri)
   :right-to-left-isolate (bidi-formatting-class-rli)
   :first-strong-isolate (bidi-formatting-class-fsi)
   :pop-directional-isolate (bidi-formatting-class-pdi)
   :otherwise nil)
  :hooks (:fix)

  ///

  (defrule bidi-class-formatting-class-under-iff
    (iff (bidi-class-formatting-class class)
         (bidi-class-explicit-formatting-p class))
    :enable bidi-class-explicit-formatting-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-class-theorems
  :short "Theorems about @('Bidi_Class')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each of the nine classes
     of the explicit directional formatting characters
     has one code point.
     So the table of this property agrees with the table of
     @(tsee bidi-explicit-formatting-class),
     and a code point has one of the nine classes
     exactly when @(tsee bidi-explicit-formatting-p) holds.")
   (xdoc::p
    "This is proved by evaluation on the tables, for each version:
     so adding a version checks it for that version.
     Theorems that relate this property to other properties
     are in @(see property-relations)."))

  ;; For each of the nine classes, the ranges of the class are one code point,
  ;; and so a code point has that class exactly when it is that code point.

  (local
   (defmacro def-explicit-class (kind code-point)
     (b* ((constructor (acl2::packn-pos (list 'bidi-class- kind)
                                        'bidi-class))
          (ranges-thm (acl2::packn-pos (list 'ranges-of- kind)
                                       'bidi-class))
          (kind-thm (acl2::packn-pos (list 'kind-is- kind)
                                     'bidi-class))
          (equal-thm (acl2::packn-pos (list 'equal-of-bidi-class- kind)
                                      'bidi-class)))
       `(progn
          (defrulel ,ranges-thm
            (equal (bidi-class-ranges (,constructor) ver)
                   (list (range ,code-point ,code-point)))
            :enable (bidi-class-ranges bidi-class-runs))
          (defrulel ,kind-thm
            (equal (equal (bidi-class-kind (code-point-bidi-class cp ver))
                          ,kind)
                   (equal (code-point-fix cp) ,code-point))
            :enable (equal-of-code-point-bidi-class
                     code-point-in-ranges-p
                     code-point-in-range-p)
            :disable ((:e ,constructor)
                      ,equal-thm)
            :use (:instance ,equal-thm
                            (x (code-point-bidi-class cp ver))))))))

  (local (def-explicit-class :left-to-right-embedding #x202A))
  (local (def-explicit-class :right-to-left-embedding #x202B))
  (local (def-explicit-class :pop-directional-format #x202C))
  (local (def-explicit-class :left-to-right-override #x202D))
  (local (def-explicit-class :right-to-left-override #x202E))
  (local (def-explicit-class :left-to-right-isolate #x2066))
  (local (def-explicit-class :right-to-left-isolate #x2067))
  (local (def-explicit-class :first-strong-isolate #x2068))
  (local (def-explicit-class :pop-directional-isolate #x2069))

  (defruled bidi-explicit-formatting-class-in-terms-of-bidi-class
    (equal (bidi-explicit-formatting-class cp ver)
           (bidi-class-formatting-class (code-point-bidi-class cp ver)))
    :enable (bidi-explicit-formatting-class-alt-def
             bidi-class-formatting-class))

  (defruled bidi-explicit-formatting-p-in-terms-of-bidi-class
    (equal (bidi-explicit-formatting-p cp ver)
           (bidi-class-explicit-formatting-p
            (code-point-bidi-class cp ver)))
    :enable (bidi-explicit-formatting-p
             bidi-explicit-formatting-class-in-terms-of-bidi-class)))
