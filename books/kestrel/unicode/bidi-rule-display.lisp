; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rule")
(include-book "bidi-mirroring")
(include-book "bidi-neutral-types")

(include-book "std/lists/flatten" :dir :system)
(include-book "std/lists/repeat" :dir :system)

(local (include-book "bidi-guarded-brackets"))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-rule-display
  :parents (bidi-rule)
  :short "How a name that satisfies the wide rule is displayed
          in a paragraph from left to right,
          computed without the rules of the algorithm,
          and the way back from the display to the name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee bidi-rule-wide-p) is meant to keep
     two different names from being displayed alike
     in a paragraph from left to right (see @(see bidi-rule)).
     The plan for a proof of that (see @(see bidi-rule-proof-plan))
     is to say how such a name is displayed
     without going through the rules
     of the Unicode Bidirectional Algorithm [UAX #9],
     and to read the name back from that display.
     This book has the two functions:
     @(tsee bidi-name-display) from a name to its display,
     and @(tsee bidi-name-read) from a display to a name.
     It proves that the second undoes the first
     for every name that satisfies the wide rule,
     so that @(tsee bidi-name-display) gives different displays
     to different names
     (see @(see bidi-rule-display-theorems)).
     That the algorithm displays such a name
     as @(tsee bidi-name-display) says
     is proved in other books, which load the whole algorithm
     (see @(see bidi-rule-display-theorem)).
     It is also tested, on every name of the searches
     for the wide rule of up to five characters;
     the tests are in the file @('tests/bidi-rule-display.lisp').")
   (xdoc::h3 "The words")
   (xdoc::p
    "The classes are the values of the @('Bidi_Class') property,
     with the short names of [UAX #9, Table 4].
     In this book a <i>right-to-left letter</i>, or just a letter,
     is a code point of class @('R') (@('Right_To_Left'))
     or @('AL') (@('Arabic_Letter'));
     a <i>digit</i> is one of class @('EN') (@('European_Number'))
     or @('AN') (@('Arabic_Number')),
     a European digit or an Arabic digit;
     a <i>mark</i> is one of class @('NSM') (@('Nonspacing_Mark'));
     a <i>separator</i> is one of class @('ES') (@('European_Separator'))
     or @('CS') (@('Common_Separator'));
     a <i>terminator</i> is one of class @('ET')
     (@('European_Terminator'));
     and a <i>bracket</i> is a paired bracket
     (see @(see bidi-paired-brackets)).
     The other two classes that this book names
     are @('L') (@('Left_To_Right')) and @('ON') (@('Other_Neutral')).
     A <i>cluster</i> is a code point with the marks that follow it
     (see @(tsee bidi-clusters)).
     A <i>number</i> is a run of clusters that are digits,
     with single separators between two digits of the same kind
     (see @(tsee bidi-leading-number)).")
   (xdoc::h3 "The display")
   (xdoc::p
    "A name that has a right-to-left letter has three parts:")
   (xdoc::ul
    (xdoc::li
     "the code points before the first letter;")
    (xdoc::li
     "the middle part, from the first letter to the last cluster
      that starts with a letter, with a digit,
      or with the closing bracket of a bracket pair
      that has a letter or a digit inside;")
    (xdoc::li
     "the code points after the middle part."))
   (xdoc::p
    "The first and the third part are displayed as they are stored.
     The clusters of the middle part are displayed from right to left,
     except that each number is displayed from left to right;
     and the code points of a cluster that is not in a number
     are replaced by their mirroring glyphs
     (see @(tsee bidi-show-clusters)).
     A name without a right-to-left letter
     is displayed as it is stored.")
   (xdoc::p
    "An example:
     the name is @('*'), a Hebrew point, alef, @('1'), @(','), @('2'),
     @('-'), bet, @('-'), @('%').
     The first part is @('*') and the point, which is a mark.
     The middle part goes from alef to bet,
     and has the number @('1,2').
     The name is displayed as
     @('*'), the point, bet, @('-'), @('1'), @(','), @('2'), alef,
     @('-'), @('%').")
   (xdoc::h3 "The way back")
   (xdoc::p
    "In the display, the middle part starts at the first cluster
     that starts with a letter, a digit or a bracket,
     and ends at the last cluster that starts with a letter.
     Its clusters, read from right to left,
     are those of the name with each number reversed;
     the numbers are found and put back in their order,
     and the mirroring glyphs are replaced back
     (see @(tsee bidi-read-clusters)).
     The proof that this gives back the name
     uses two of the conditions of the wide rule:
     that no digit and no bracket comes before the first letter
     (see @(tsee bidi-rule-wide-start-p)),
     and that the name does not have both European and Arabic digits.
     Without the first, the start of the middle part
     cannot be told from the display.
     Without the second, a separator between a European digit
     and an Arabic digit can stand, in the display,
     between two digits of the same kind,
     and the numbers found in the display are not those of the name.")
   (xdoc::p
    "The other conditions of the wide rule are for the algorithm:
     that the name has no letter of class @('L'),
     that no terminator is next to a European digit,
     and that every character is of a class that the rule allows.
     Without one of the first two,
     the algorithm can display a name
     in another way than @(tsee bidi-name-display) says;
     the tests have an example of each,
     and one of a bracket before the first letter.")
   (xdoc::h3 "The theorem about the algorithm")
   (xdoc::p
    "The Unicode Bidirectional Algorithm displays a name
     that satisfies the wide rule as this book says:")
   (xdoc::codeblock
    "(implies (and (bidi-rule-wide-p name ver)"
    "              (equal (paragraph-direction-kind direction)"
    "                     :left-to-right))"
    "         (equal (bidi-display name direction ver)"
    "                (bidi-name-display name ver)))")
   (xdoc::p
    "This is the theorem @('bidi-display-when-bidi-rule-wide-p')
     (see @(see bidi-rule-display-theorem)).
     With it, and with the theorem of this book,
     two names that satisfy the wide rule
     and are displayed alike in a paragraph from left to right
     are the same name.
     The proof has three parts, each in a book of its own:
     the classes that the weak rules give
     (see @(see bidi-rule-display-weak));
     the levels, which are those of @(tsee bidi-name-levels)
     (see @(see bidi-rule-display-levels));
     and the order of display that follows from those levels
     (see @(see bidi-rule-display-order)).
     See also @(see bidi-rule-proof-plan)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-mirror-code-point ((cp code-point-p) (ver versionp))
  :returns (mirror code-point-p)
  :short "The code point that is displayed for a code point
          at a level from right to left, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the mirroring glyph of the code point if it has one
     (see @(see bidi-mirroring)), and the code point itself otherwise
     [UAX #9, rule L4]."))
  (b* ((glyph? (code-point-bidi-mirroring-glyph cp ver)))
    (if glyph?
        (code-point-fix glyph?)
      (code-point-fix cp)))
  :hooks (:fix))

(define bidi-mirror-code-points ((cps code-point-listp) (ver versionp))
  :returns (mirrors code-point-listp)
  :short "The code points that are displayed for the code points of a list
          at a level from right to left, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-mirror-code-point).
     The order of the list is kept."))
  (if (endp cps)
      nil
    (cons (bidi-mirror-code-point (car cps) ver)
          (bidi-mirror-code-points (cdr cps) ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-clusters ((cps code-point-listp) (ver versionp))
  :returns (clusters code-point-list-listp)
  :short "Cut a list of code points into clusters, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A cluster is a code point with the marks that follow it:
     each code point of class @('NSM') (@('Nonspacing_Mark');
     see @(tsee bidi-mark-code-point-p))
     goes into the cluster of the code point before it.
     The first cluster of a list starts with a mark
     if the list does; no other cluster does.
     In the Unicode Bidirectional Algorithm
     a mark takes the class of the character before it [UAX #9, rule W1],
     and it is displayed after that character [UAX #9, rule L3].
     In the displays of this book
     the code points of a cluster stay together, in their order.")
   (xdoc::p
    "The clusters of a list, one after the other, are the list:
     nothing is added or dropped."))
  (b* (((when (endp cps)) nil)
       (cp (code-point-fix (car cps)))
       (rest (bidi-clusters (cdr cps) ver))
       ((when (and (consp (cdr cps))
                   (bidi-mark-code-point-p (cadr cps) ver)))
        (cons (cons cp (code-point-list-fix (car rest)))
              (cdr rest))))
    (cons (list cp) rest))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-cluster-digit-kind ((cluster code-point-listp)
                                 (arabic booleanp)
                                 (ver versionp))
  :returns (kind symbolp)
  :short "The kind of digit that a cluster is, if it is a digit,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A cluster is a digit if its first code point
     is of class @('EN') (@('European_Number'))
     or @('AN') (@('Arabic_Number')).
     The result is @(':european-number') or @(':arabic-number')
     for a digit, and @('nil') for a cluster that is not a digit.
     The second argument says that the last letter before the cluster
     is of class @('AL') (@('Arabic_Letter')):
     a European digit is then an Arabic digit [UAX #9, rule W2]."))
  (b* (((unless (consp cluster)) nil)
       (kind (bidi-class-kind (code-point-bidi-class (car cluster) ver))))
    (case kind
      (:arabic-number :arabic-number)
      (:european-number (if arabic
                            :arabic-number
                          :european-number))
      (otherwise nil)))
  :hooks (:fix))

(define bidi-arabic-after-cluster-p ((cluster code-point-listp)
                                     (arabic booleanp)
                                     (ver versionp))
  :returns (new-arabic booleanp)
  :short "Check if the last letter is of class @('AL')
          (@('Arabic_Letter')) after a cluster,
          given whether it was before the cluster,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the second argument of @(tsee bidi-cluster-digit-kind)
     for the clusters that follow.
     A cluster that starts with a code point of class @('AL') sets it;
     one that starts with a code point of class @('R')
     (@('Right_To_Left')) or @('L') (@('Left_To_Right')) clears it;
     any other cluster leaves it as it is."))
  (b* (((unless (consp cluster)) (and arabic t))
       (kind (bidi-class-kind (code-point-bidi-class (car cluster) ver))))
    (case kind
      (:arabic-letter t)
      (:right-to-left nil)
      (:left-to-right nil)
      (otherwise (and arabic t))))
  :hooks (:fix))

(define bidi-cluster-joins-p ((cluster code-point-listp)
                              (previous code-point-listp)
                              (next code-point-listp)
                              (arabic booleanp)
                              (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a cluster is a separator that joins two digits
          into one number, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second and third arguments are the cluster before it
     and the cluster after it.
     The cluster joins them if it is a single code point,
     the two are digits of the same kind
     (see @(tsee bidi-cluster-digit-kind)),
     and the code point is of class @('CS') (@('Common_Separator')),
     or of class @('ES') (@('European_Separator'))
     between two European digits
     [UAX #9, rule W4].
     A separator with a mark after it is not a single code point,
     and joins nothing."))
  (b* (((unless (and (consp cluster)
                     (endp (cdr cluster))))
        nil)
       (kind (bidi-class-kind (code-point-bidi-class (car cluster) ver)))
       (previous (bidi-cluster-digit-kind previous arabic ver))
       (next (bidi-cluster-digit-kind next arabic ver)))
    (and previous
         (equal previous next)
         (or (equal kind :common-separator)
             (and (equal kind :european-separator)
                  (equal previous :european-number)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-leading-number ((clusters code-point-list-listp)
                             (arabic booleanp)
                             (ver versionp))
  :returns (run code-point-list-listp)
  :short "The number at the start of a list of clusters,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A number is a digit, then any times
     either a digit or a joining separator and a digit
     (see @(tsee bidi-cluster-joins-p)).
     The result is the longest number that the list starts with:
     the empty list if the first cluster is not a digit.
     A number of the middle part of a name
     is displayed from left to right:
     see @(tsee bidi-show-clusters)."))
  (b* (((when (endp clusters)) nil)
       (cluster (code-point-list-fix (car clusters)))
       ((unless (bidi-cluster-digit-kind cluster arabic ver)) nil)
       ((when (and (consp (cdr clusters))
                   (bidi-cluster-joins-p (cadr clusters)
                                         cluster
                                         (caddr clusters)
                                         arabic
                                         ver)))
        (list* cluster
               (code-point-list-fix (cadr clusters))
               (bidi-leading-number (cddr clusters) arabic ver))))
    (cons cluster
          (bidi-leading-number (cdr clusters) arabic ver)))
  :measure (len clusters)
  :hints (("Goal" :in-theory (enable len o-p o-finp o<)))
  :hooks (:fix))

(define bidi-after-leading-number ((clusters code-point-list-listp)
                                   (arabic booleanp)
                                   (ver versionp))
  :returns (rest code-point-list-listp)
  :short "The clusters of a list after the number at its start,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-leading-number):
     the number and this list, one after the other, are the list."))
  (b* (((when (endp clusters)) nil)
       (cluster (code-point-list-fix (car clusters)))
       ((unless (bidi-cluster-digit-kind cluster arabic ver))
        (code-point-list-list-fix clusters))
       ((when (and (consp (cdr clusters))
                   (bidi-cluster-joins-p (cadr clusters)
                                         cluster
                                         (caddr clusters)
                                         arabic
                                         ver)))
        (bidi-after-leading-number (cddr clusters) arabic ver)))
    (bidi-after-leading-number (cdr clusters) arabic ver))
  :measure (len clusters)
  :hints (("Goal" :in-theory (enable len o-p o-finp o<)))
  :hooks (:fix)
  ///
  (defret len-of-bidi-after-leading-number
    (<= (len rest)
        (len clusters))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len))))
  (defret len-of-cdr-of-bidi-after-leading-number
    (implies (consp rest)
             (< (len (cdr rest))
                (len clusters)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (len) (len-of-bidi-after-leading-number))
             :use len-of-bidi-after-leading-number))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-show-clusters ((clusters code-point-list-listp)
                            (arabic booleanp)
                            (ver versionp))
  :returns (shown code-point-list-listp)
  :short "The clusters of the middle part of a name, in the order of display,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list is taken from its start:
     a number (see @(tsee bidi-leading-number)), which can be empty,
     and then one cluster that is not in a number.
     The rest of the list is displayed first, by the same function;
     then that cluster,
     with each code point replaced by the one displayed for it
     (see @(tsee bidi-mirror-code-points));
     then the number, in its own order.
     So the clusters go from right to left,
     except that each number goes from left to right.")
   (xdoc::p
    "The second argument says that the last letter before the list
     is of class @('AL') (@('Arabic_Letter'));
     it is @('nil') for the whole middle part,
     which starts with a letter."))
  (b* ((run (bidi-leading-number clusters arabic ver))
       (rest (bidi-after-leading-number clusters arabic ver))
       ((when (endp rest)) run)
       (cluster (code-point-list-fix (car rest))))
    (append (bidi-show-clusters (cdr rest)
                                (bidi-arabic-after-cluster-p cluster arabic ver)
                                ver)
            (cons (bidi-mirror-code-points cluster ver)
                  run)))
  :measure (len clusters)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :verify-guards :after-returns
  :hooks (:fix))

(define bidi-read-clusters ((clusters code-point-list-listp)
                            (arabic booleanp)
                            (ver versionp))
  :returns (read code-point-list-listp)
  :short "The clusters of the middle part of a name,
          from the clusters of its display taken from right to left,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the display of the middle part
     (see @(tsee bidi-show-clusters)) with its clusters in reverse order.
     Read in that order, the display has the clusters of the name
     in their order, except that each number is reversed;
     so this function takes a number from the start of the list,
     puts it back in its order, takes one more cluster,
     replaces its code points back, and goes on with the rest.")
   (xdoc::p
    "A number reversed is a number,
     and when the digits of the name are all of one class
     the numbers found in the display are those of the name:
     see @(see bidi-rule-display-theorems)."))
  (b* ((run (bidi-leading-number clusters arabic ver))
       (rest (bidi-after-leading-number clusters arabic ver))
       ((when (endp rest)) (rev run))
       (cluster (code-point-list-fix (car rest))))
    (append (rev run)
            (cons (bidi-mirror-code-points cluster ver)
                  (bidi-read-clusters
                   (cdr rest)
                   (bidi-arabic-after-cluster-p cluster arabic ver)
                   ver))))
  :measure (len clusters)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-right-to-left-letter-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a right-to-left letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its class is @('R') (@('Right_To_Left'))
     or @('AL') (@('Arabic_Letter'))."))
  (and (member-eq (bidi-class-kind (code-point-bidi-class cp ver))
                  '(:right-to-left :arabic-letter))
       t)
  :hooks (:fix))

(define bidi-digit-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a digit, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its class is @('EN') (@('European_Number'))
     or @('AN') (@('Arabic_Number'))."))
  (and (member-eq (bidi-class-kind (code-point-bidi-class cp ver))
                  '(:european-number :arabic-number))
       t)
  :hooks (:fix))

(define bidi-name-start ((name code-point-listp) (ver versionp))
  :returns (start natp)
  :short "The number of code points of a name
          before its first right-to-left letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the length of the name if it has no such letter.
     It is the length of the first of the three parts of the name:
     see @(tsee bidi-name-display)."))
  (cond ((endp name) 0)
        ((bidi-right-to-left-letter-p (car name) ver) 0)
        (t (+ 1 (bidi-name-start (cdr name) ver))))
  :hooks (:fix)
  ///
  (defret bidi-name-start-upper-bound
    (<= start (len name))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len)))))

(define bidi-name-to-last-letter-or-digit ((name code-point-listp)
                                           (ver versionp))
  :returns (end natp)
  :short "The number of code points of a name
          up to its last right-to-left letter or digit,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The letter or digit is counted.
     The result is 0 if the name has neither."))
  (b* (((when (endp name)) 0)
       (end (bidi-name-to-last-letter-or-digit (cdr name) ver))
       ((when (> end 0)) (+ 1 end)))
    (if (or (bidi-right-to-left-letter-p (car name) ver)
            (bidi-digit-p (car name) ver))
        1
      0))
  :hooks (:fix)
  ///
  (defret bidi-name-to-last-letter-or-digit-upper-bound
    (<= end (len name))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len)))))

(define bidi-name-strong-inside-p ((name code-point-listp)
                                   (position natp)
                                   (pair bracket-pair-p)
                                   (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a bracket pair of a name
          has a right-to-left letter or a digit inside,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the name, or the rest of it
     from the position that is the second argument;
     the pair has the positions of its two brackets in the name.
     The function looks strictly between the two.
     The Unicode Bidirectional Algorithm gives a direction
     to a bracket pair that has a strong character inside
     [UAX #9, rule N0];
     this is why the closing bracket of such a pair
     is counted in the middle part of a name
     (see @(tsee bidi-name-end)).
     The function follows @(tsee bidi-n0-strong-inside-p),
     which is on the classes that the weak rules have resolved."))
  (b* (((when (endp name)) nil)
       (position (lnfix position))
       ((bracket-pair pair))
       ((when (>= position pair.close)) nil)
       ((when (and (> position pair.open)
                   (or (bidi-right-to-left-letter-p (car name) ver)
                       (bidi-digit-p (car name) ver))))
        t))
    (bidi-name-strong-inside-p (cdr name) (+ 1 position) pair ver))
  :hooks (:fix))

(define bidi-name-pairs-end ((pairs bracket-pair-listp)
                             (name code-point-listp)
                             (ver versionp))
  :returns (end natp)
  :short "The number of code points of a name up to the last closing bracket
          of a bracket pair that has a right-to-left letter
          or a digit inside, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the bracket pairs of the name
     (see @(tsee bidi-bracket-pairs)).
     The bracket is counted.
     The result is 0 if no pair has a letter or a digit inside:
     see @(tsee bidi-name-strong-inside-p)."))
  (b* (((when (endp pairs)) 0)
       (end (bidi-name-pairs-end (cdr pairs) name ver))
       ((unless (bidi-name-strong-inside-p name 0 (car pairs) ver)) end))
    (max (+ 1 (bracket-pair->close (car pairs)))
         end))
  :hooks (:fix))

(define bidi-leading-marks ((name code-point-listp) (ver versionp))
  :returns (count natp)
  :short "The number of marks at the start of a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-mark-code-point-p)."))
  (if (and (consp name)
           (bidi-mark-code-point-p (car name) ver))
      (+ 1 (bidi-leading-marks (cdr name) ver))
    0)
  :hooks (:fix)
  ///
  (defret bidi-leading-marks-upper-bound
    (<= count (len name))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len))))
  (defrule bidi-leading-marks-of-nthcdr-upper-bound
    (implies (and (natp n)
                  (<= n (len name)))
             (<= (+ n (bidi-leading-marks (nthcdr n name) ver))
                 (len name)))
    :rule-classes :linear
    :induct (nthcdr n name)
    :enable (nthcdr len fix)))

; The closing bracket of a bracket pair of a name is a bracket of the name.

(local
 (define closes-ok ((pairs bracket-pair-listp)
                    (name code-point-listp)
                    (ver versionp))
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (< (bracket-pair->close (car pairs)) (len name))
            (code-point-bidi-bracket
             (nth (bracket-pair->close (car pairs)) name)
             ver)
            (closes-ok (cdr pairs) name ver)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-bracket-role-kind-of-nth-of-brackets-of-code-points
  (equal (bidi-bracket-role-kind
          (nth i (bidi-char-list-brackets
                  (code-points-to-bidi-chars name ver))))
         (if (< (nfix i) (len name))
             (bidi-bracket-role-kind
              (code-point-bidi-bracket-role (nth i name) ver))
           :none))
  :induct (nth i name)
  :enable (nth
           len
           bidi-char-list-brackets
           code-points-to-bidi-chars
           code-point-bidi-char
           nfix))

(defrulel code-point-bidi-bracket-when-role-close
  (implies (equal (bidi-bracket-role-kind
                   (code-point-bidi-bracket-role cp ver))
                  :close)
           (code-point-bidi-bracket cp ver))
  :enable code-point-bidi-bracket-role)

(defrulel closes-ok-when-bidi-pairs-sound-p
  (implies (bidi-pairs-sound-p
            pairs
            (bidi-char-list-classes (code-points-to-bidi-chars name ver))
            (bidi-char-list-brackets (code-points-to-bidi-chars name ver)))
           (closes-ok pairs name ver))
  :induct (len pairs)
  :enable (len
           bidi-pairs-sound-p
           bidi-pair-sound-p
           closes-ok
           nfix))

(defrulel bidi-name-pairs-end-upper-bound-when-closes-ok
  (implies (closes-ok pairs name ver)
           (<= (bidi-name-pairs-end pairs name ver)
               (len name)))
  :rule-classes :linear
  :induct (len pairs)
  :enable (len
           closes-ok
           bidi-name-pairs-end
           max))

(define bidi-name-end ((name code-point-listp) (ver versionp))
  :returns (end natp)
  :short "The number of code points of a name
          up to the end of its middle part, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The middle part ends with the last cluster
     (see @(tsee bidi-clusters))
     that starts with a right-to-left letter, with a digit,
     or with the closing bracket of a bracket pair
     that has a letter or a digit inside
     (see @(tsee bidi-name-pairs-end)).
     So this is the position after the last such code point,
     moved past the marks that follow it.
     The bracket pairs are those that the algorithm finds
     [UAX #9, BD16]."))
  (b* ((chars (code-points-to-bidi-chars name ver))
       (pairs (bidi-bracket-pairs (bidi-char-list-classes chars)
                                  (bidi-char-list-brackets chars)))
       (end (max (bidi-name-to-last-letter-or-digit name ver)
                 (bidi-name-pairs-end pairs name ver))))
    (+ end (bidi-leading-marks (nthcdr end name) ver)))
  :guard-hints (("Goal" :in-theory (enable max nfix)))
  :hooks (:fix)
  ///
  (defret bidi-name-end-upper-bound
    (<= end (len name))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable max nfix)))))

(define bidi-name-display ((name code-point-listp) (ver versionp))
  :returns (display code-point-listp
                    :hints (("Goal" :in-theory (enable nfix))))
  :short "The display of a name in a paragraph from left to right,
          computed without the rules of the algorithm,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see bidi-rule-display).
     The name has three parts:
     the code points before the first right-to-left letter
     (see @(tsee bidi-name-start)), the middle part,
     and the code points after the middle part
     (see @(tsee bidi-name-end)).
     The first and the third are displayed as they are stored,
     and the clusters of the middle part
     as @(tsee bidi-show-clusters) says.
     A name with no right-to-left letter has no middle part,
     and the result is the name.")
   (xdoc::p
    "This is the display of the Unicode Bidirectional Algorithm
     (see @(tsee bidi-display))
     for the names that satisfy @(tsee bidi-rule-wide-p):
     that is the theorem of @(see bidi-rule-display-theorem).
     For other names the two can differ."))
  (b* ((name (code-point-list-fix name))
       (start (bidi-name-start name ver))
       (end (bidi-name-end name ver))
       ((unless (< start end)) name))
    (append (take start name)
            (acl2::flatten
             (bidi-show-clusters
              (bidi-clusters (nthcdr start (take end name)) ver)
              nil
              ver))
            (nthcdr end name)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defrulel nat-listp-of-repeat
  (implies (natp x)
           (nat-listp (acl2::repeat n x)))
  :induct (acl2::repeat n x)
  :enable acl2::repeat)

(define bidi-middle-levels ((clusters code-point-list-listp)
                            (arabic booleanp)
                            (ver versionp))
  :returns (levels nat-listp)
  :short "The levels of the code points of the middle part of a name,
          computed without the rules of the algorithm,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list is taken from its start,
     as @(tsee bidi-show-clusters) takes it:
     the code points of a number (see @(tsee bidi-leading-number))
     have level 2,
     and those of a cluster that is not in a number have level 1.
     These are the levels for which rule L2 of the algorithm
     reverses the middle part and then puts each number back
     in its own order.
     The second argument says that the last letter before the list
     is of class @('AL') (@('Arabic_Letter'))."))
  (b* ((number (bidi-leading-number clusters arabic ver))
       (rest (bidi-after-leading-number clusters arabic ver))
       (twos (acl2::repeat (len (acl2::flatten number)) 2))
       ((when (endp rest)) twos)
       (cluster (code-point-list-fix (car rest))))
    (append twos
            (acl2::repeat (len cluster) 1)
            (bidi-middle-levels
             (cdr rest)
             (bidi-arabic-after-cluster-p cluster arabic ver)
             ver)))
  :measure (len clusters)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :verify-guards :after-returns
  :hooks (:fix))

(define bidi-name-levels ((name code-point-listp) (ver versionp))
  :returns (levels nat-listp)
  :short "The levels of the code points of a name
          in a paragraph from left to right,
          computed without the rules of the algorithm,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code points before the first right-to-left letter
     (see @(tsee bidi-name-start)) and those after the middle part
     (see @(tsee bidi-name-end)) have level 0,
     and those of the middle part have the levels
     that @(tsee bidi-middle-levels) gives.
     Every code point of a name with no right-to-left letter
     has level 0.")
   (xdoc::p
    "For a name that satisfies @(tsee bidi-rule-wide-p),
     these are the levels that the Unicode Bidirectional Algorithm
     gives in a paragraph from left to right
     (see @(tsee bidi-paragraph-all-levels)):
     that is the theorem of @(see bidi-rule-display-levels)."))
  (b* ((name (code-point-list-fix name))
       (start (bidi-name-start name ver))
       (end (bidi-name-end name ver))
       ((unless (< start end)) (acl2::repeat (len name) 0)))
    (append (acl2::repeat start 0)
            (bidi-middle-levels
             (bidi-clusters (nthcdr start (take end name)) ver)
             nil
             ver)
            (acl2::repeat (- (len name) end) 0)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-cluster-letter-p ((cluster code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a cluster starts with a right-to-left letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-right-to-left-letter-p)."))
  (and (consp cluster)
       (bidi-right-to-left-letter-p (car cluster) ver))
  :hooks (:fix))

(define bidi-cluster-landmark-p ((cluster code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a cluster starts with a right-to-left letter,
          a digit or a paired bracket, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the display of a name that satisfies the wide rule,
     the first cluster of this kind is where the middle part starts:
     see @(tsee bidi-name-read)."))
  (and (consp cluster)
       (or (bidi-right-to-left-letter-p (car cluster) ver)
           (bidi-digit-p (car cluster) ver)
           (and (code-point-bidi-bracket (car cluster) ver) t)))
  :hooks (:fix))

(define bidi-clusters-before-landmark ((clusters code-point-list-listp)
                                       (ver versionp))
  :returns (count natp)
  :short "The number of clusters of a list before the first
          that starts with a right-to-left letter, a digit
          or a paired bracket, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-cluster-landmark-p).
     This is the length of the list if it has no such cluster."))
  (cond ((endp clusters) 0)
        ((bidi-cluster-landmark-p (car clusters) ver) 0)
        (t (+ 1 (bidi-clusters-before-landmark (cdr clusters) ver))))
  :hooks (:fix)
  ///
  (defret bidi-clusters-before-landmark-upper-bound
    (<= count (len clusters))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len)))))

(define bidi-clusters-to-last-letter ((clusters code-point-list-listp)
                                      (ver versionp))
  :returns (count natp)
  :short "The number of clusters of a list up to the last
          that starts with a right-to-left letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That cluster is counted.
     The result is 0 if the list has no such cluster."))
  (b* (((when (endp clusters)) 0)
       (count (bidi-clusters-to-last-letter (cdr clusters) ver))
       ((when (> count 0)) (+ 1 count)))
    (if (bidi-cluster-letter-p (car clusters) ver)
        1
      0))
  :hooks (:fix)
  ///
  (defret bidi-clusters-to-last-letter-upper-bound
    (<= count (len clusters))
    :rule-classes :linear
    :hints (("Goal" :induct t :in-theory (enable len)))))

(define bidi-name-read ((display code-point-listp) (ver versionp))
  :returns (name code-point-listp
                 :hints (("Goal" :in-theory (enable nfix))))
  :short "The name that a display is the display of,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the way back from @(tsee bidi-name-display).
     The display is cut into clusters.
     The middle part goes from the first cluster
     that starts with a right-to-left letter, a digit or a paired bracket
     to the last cluster that starts with a right-to-left letter;
     its clusters are read from right to left
     (see @(tsee bidi-read-clusters)),
     and the clusters before it and after it are kept.
     A display with no right-to-left letter is the name.")
   (xdoc::p
    "For a name that satisfies @(tsee bidi-rule-wide-p),
     this gives the name back from what @(tsee bidi-name-display) gives:
     see @(see bidi-rule-display-theorems).
     The middle part of the name starts with its first letter,
     which is displayed last, so the last letter of the display
     ends the middle part there.
     The middle part of the name ends with a letter, a digit
     or a closing bracket, which is displayed first, or,
     for a digit, in the number that is displayed first;
     and the rule allows no digit and no paired bracket
     before the first letter of the name."))
  (b* ((clusters (bidi-clusters display ver))
       (start (bidi-clusters-before-landmark clusters ver))
       (end (bidi-clusters-to-last-letter clusters ver))
       ((unless (< start end)) (code-point-list-fix display)))
    (acl2::flatten
     (append (take start clusters)
             (bidi-read-clusters (rev (nthcdr start (take end clusters)))
                                 nil
                                 ver)
             (nthcdr end clusters))))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-mirrored-class
  :short "A code point that has a mirroring glyph has the class @('ON')
          (Other Neutral), and so does its mirroring glyph."
  :long
  (xdoc::topstring
   (xdoc::p
    "So replacing a code point by its mirroring glyph
     (see @(tsee bidi-mirror-code-point))
     keeps its class, and doing it twice gives the code point back;
     a paired bracket becomes a paired bracket,
     and a code point that is not one does not become one.
     We prove the first theorem by checking it on every code point,
     for each version;
     so adding a version checks it for that version.
     The others follow from it and from the theorems
     about the mirroring glyphs (see @(see bidi-mirroring-theorems))
     and about the paired brackets (see @(see bidi-bracket-partners))."))

  (local
   (define mirrored-class-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (not (code-point-bidi-mirroring-glyph cp ver))
         (equal (bidi-class-kind (code-point-bidi-class cp ver))
                :other-neutral))
     :hooks nil))

  (local
   (std::deflist mirrored-class-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (mirrored-class-ok x ver)))

  (defrulel mirrored-class-ok-listp-of-all-code-points
    (mirrored-class-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable mirrored-class-ok-listp-of-cons)

  (defrulel mirrored-class-ok-holds
    (mirrored-class-ok cp ver)
    :rule-classes nil
    :use (:instance
          mirrored-class-ok-when-member-equal-of-mirrored-class-ok-listp
          (acl2::a (code-point-fix cp))
          (x (all-code-points))
          (ver (version-fix ver)))
    :enable mirrored-class-ok)

  (defrule code-point-bidi-class-when-code-point-bidi-mirroring-glyph
    (implies (code-point-bidi-mirroring-glyph cp ver)
             (equal (bidi-class-kind (code-point-bidi-class cp ver))
                    :other-neutral))
    :enable mirrored-class-ok
    :use mirrored-class-ok-holds)

  (defrule bidi-class-kind-of-bidi-mirror-code-point
    (equal (bidi-class-kind
            (code-point-bidi-class (bidi-mirror-code-point cp ver) ver))
           (bidi-class-kind (code-point-bidi-class cp ver)))
    :enable bidi-mirror-code-point)

  (defrule bidi-mirror-code-point-of-bidi-mirror-code-point
    (equal (bidi-mirror-code-point (bidi-mirror-code-point cp ver) ver)
           (code-point-fix cp))
    :enable bidi-mirror-code-point)

  (defrulel code-point-bidi-bracket-of-bidi-mirror-code-point-when-bracket
    (implies (code-point-bidi-bracket cp ver)
             (code-point-bidi-bracket (bidi-mirror-code-point cp ver) ver))
    :enable bidi-mirror-code-point)

  (defrule code-point-bidi-bracket-of-bidi-mirror-code-point
    (iff (code-point-bidi-bracket (bidi-mirror-code-point cp ver) ver)
         (code-point-bidi-bracket cp ver))
    :use (:instance
          code-point-bidi-bracket-of-bidi-mirror-code-point-when-bracket
          (cp (bidi-mirror-code-point cp ver)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rest of the book is the proof that BIDI-NAME-READ undoes
; BIDI-NAME-DISPLAY for a name that satisfies the wide rule;
; the two theorems are at the end.  The proof has three layers:
;
; - On lists of clusters whose digits are of one class,
;   BIDI-READ-CLUSTERS undoes BIDI-SHOW-CLUSTERS
;   (theorem BIDI-READ-CLUSTERS-OF-REV-OF-BIDI-SHOW-CLUSTERS).
;
; - On a list of code points in three parts, BIDI-NAME-READ finds
;   the middle part (theorem BIDI-NAME-READ-OF-THREE-PARTS).
;
; - The three parts of a name that satisfies the wide rule
;   have what the second layer asks for.
;
; The lemmas are local.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Mirroring a cluster.

(defrulel consp-of-bidi-mirror-code-points
  (equal (consp (bidi-mirror-code-points cps ver))
         (consp cps))
  :expand (bidi-mirror-code-points cps ver))

(defrulel car-of-bidi-mirror-code-points
  (implies (consp cps)
           (equal (car (bidi-mirror-code-points cps ver))
                  (bidi-mirror-code-point (car cps) ver)))
  :expand (bidi-mirror-code-points cps ver))

(defrulel cdr-of-bidi-mirror-code-points
  (implies (consp cps)
           (equal (cdr (bidi-mirror-code-points cps ver))
                  (bidi-mirror-code-points (cdr cps) ver)))
  :expand (bidi-mirror-code-points cps ver))

(defrulel consp-of-cdr-of-bidi-mirror-code-points
  (equal (consp (cdr (bidi-mirror-code-points cps ver)))
         (consp (cdr cps)))
  :expand ((bidi-mirror-code-points cps ver)
           (bidi-mirror-code-points (cdr cps) ver)))

(defrulel bidi-mirror-code-points-of-bidi-mirror-code-points
  (equal (bidi-mirror-code-points (bidi-mirror-code-points cps ver) ver)
         (code-point-list-fix cps))
  :induct t
  :enable (bidi-mirror-code-points code-point-list-fix))

(defrulel bidi-cluster-digit-kind-of-bidi-mirror-code-points
  (equal (bidi-cluster-digit-kind (bidi-mirror-code-points cluster ver)
                                  arabic
                                  ver)
         (bidi-cluster-digit-kind cluster arabic ver))
  :enable bidi-cluster-digit-kind)

(defrulel bidi-arabic-after-cluster-p-of-bidi-mirror-code-points
  (equal (bidi-arabic-after-cluster-p (bidi-mirror-code-points cluster ver)
                                      arabic
                                      ver)
         (bidi-arabic-after-cluster-p cluster arabic ver))
  :enable bidi-arabic-after-cluster-p)

(defrulel bidi-cluster-joins-p-of-bidi-mirror-code-points
  (equal (bidi-cluster-joins-p (bidi-mirror-code-points cluster ver)
                               previous
                               next
                               arabic
                               ver)
         (bidi-cluster-joins-p cluster previous next arabic ver))
  :enable bidi-cluster-joins-p)

(defrulel bidi-cluster-letter-p-of-bidi-mirror-code-points
  (equal (bidi-cluster-letter-p (bidi-mirror-code-points cluster ver) ver)
         (bidi-cluster-letter-p cluster ver))
  :enable (bidi-cluster-letter-p bidi-right-to-left-letter-p))

(defrulel bidi-cluster-landmark-p-of-bidi-mirror-code-points
  (equal (bidi-cluster-landmark-p (bidi-mirror-code-points cluster ver) ver)
         (bidi-cluster-landmark-p cluster ver))
  :enable (bidi-cluster-landmark-p bidi-right-to-left-letter-p bidi-digit-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Digits and separators.

(defrulel not-bidi-cluster-digit-kind-when-bidi-cluster-joins-p
  (implies (bidi-cluster-joins-p cluster previous next arabic ver)
           (not (bidi-cluster-digit-kind cluster arabic2 ver)))
  :enable (bidi-cluster-joins-p bidi-cluster-digit-kind))

(defrulel bidi-cluster-digit-kind-of-next-when-bidi-cluster-joins-p
  (implies (bidi-cluster-joins-p cluster previous next arabic ver)
           (bidi-cluster-digit-kind next arabic ver))
  :enable bidi-cluster-joins-p)

(defrulel consp-of-next-when-bidi-cluster-joins-p
  (implies (bidi-cluster-joins-p cluster previous next arabic ver)
           (consp next))
  :rule-classes :forward-chaining
  :enable (bidi-cluster-joins-p bidi-cluster-digit-kind))

(defrulel consp-when-bidi-cluster-digit-kind
  (implies (bidi-cluster-digit-kind cluster arabic ver)
           (consp cluster))
  :rule-classes :forward-chaining
  :enable bidi-cluster-digit-kind)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The number at the start of a list of clusters, and the rest.

(defrulel append-of-bidi-leading-number-and-bidi-after-leading-number
  (equal (append (bidi-leading-number clusters arabic ver)
                 (bidi-after-leading-number clusters arabic ver))
         (code-point-list-list-fix clusters))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number bidi-after-leading-number))

(defrulel consp-of-bidi-leading-number
  (equal (consp (bidi-leading-number clusters arabic ver))
         (and (bidi-cluster-digit-kind (car clusters) arabic ver)
              t))
  :expand (bidi-leading-number clusters arabic ver)
  :enable bidi-cluster-digit-kind)

(defrulel car-of-bidi-leading-number
  (implies (bidi-cluster-digit-kind (car clusters) arabic ver)
           (equal (car (bidi-leading-number clusters arabic ver))
                  (code-point-list-fix (car clusters))))
  :expand (bidi-leading-number clusters arabic ver))

(defrulel bidi-leading-number-when-not-digit
  (implies (not (bidi-cluster-digit-kind (car clusters) arabic ver))
           (equal (bidi-leading-number clusters arabic ver)
                  nil))
  :expand (bidi-leading-number clusters arabic ver))

(defrulel bidi-after-leading-number-when-not-digit
  (implies (not (bidi-cluster-digit-kind (car clusters) arabic ver))
           (equal (bidi-after-leading-number clusters arabic ver)
                  (code-point-list-list-fix clusters)))
  :expand (bidi-after-leading-number clusters arabic ver))

(defrulel not-bidi-cluster-digit-kind-of-car-of-bidi-after-leading-number
  (not (bidi-cluster-digit-kind
        (car (bidi-after-leading-number clusters arabic ver))
        arabic
        ver))
  :induct (bidi-after-leading-number clusters arabic ver)
  :enable bidi-after-leading-number)

; A list of clusters is a number
; if the number at its start is the whole list.
; The number at the start of a list is a number;
; a number followed by more clusters is taken up to its last cluster,
; and what comes after that cluster depends on that cluster only.

(defrulel bidi-leading-number-of-bidi-leading-number
  (equal (bidi-leading-number (bidi-leading-number clusters arabic ver)
                              arabic
                              ver)
         (bidi-leading-number clusters arabic ver))
  :induct (bidi-leading-number clusters arabic ver)
  :enable bidi-leading-number)

(defrulel bidi-leading-number-of-append-when-closed
  (implies (and (code-point-list-listp x)
                (consp x)
                (equal (bidi-leading-number x arabic ver) x))
           (equal (bidi-leading-number (append x y) arabic ver)
                  (append (rev (cdr (rev x)))
                          (bidi-leading-number (cons (car (rev x)) y)
                                               arabic
                                               ver))))
  :induct (bidi-leading-number x arabic ver)
  :enable (bidi-leading-number rev))

(defrulel bidi-after-leading-number-of-append-when-closed
  (implies (and (code-point-list-listp x)
                (consp x)
                (equal (bidi-leading-number x arabic ver) x))
           (equal (bidi-after-leading-number (append x y) arabic ver)
                  (bidi-after-leading-number (cons (car (rev x)) y)
                                             arabic
                                             ver)))
  :induct (bidi-leading-number x arabic ver)
  :enable (bidi-leading-number bidi-after-leading-number rev))

(defrulel bidi-after-leading-number-when-closed
  (implies (and (code-point-list-listp x)
                (equal (bidi-leading-number x arabic ver) x))
           (equal (bidi-after-leading-number x arabic ver)
                  nil))
  :induct (bidi-leading-number x arabic ver)
  :enable (bidi-leading-number bidi-after-leading-number))

; A number reversed is a number.
; First: a number with one more digit, or with a separator
; that joins its last cluster to one more digit, is a number.

(defrulel append-of-rev-of-cdr-of-rev
  (implies (consp x)
           (equal (append (rev (cdr (rev x)))
                          (cons (car (rev x)) y))
                  (append x y)))
  :induct (len x)
  :enable (rev len))

(defrulel not-bidi-cluster-joins-p-when-bidi-cluster-digit-kind
  (implies (bidi-cluster-digit-kind cluster arabic2 ver)
           (not (bidi-cluster-joins-p cluster previous next arabic ver)))
  :enable (bidi-cluster-joins-p bidi-cluster-digit-kind))

(defrulel bidi-cluster-joins-p-commutes
  (implies (bidi-cluster-joins-p cluster previous next arabic ver)
           (bidi-cluster-joins-p cluster next previous arabic ver))
  :enable bidi-cluster-joins-p)

(defrulel bidi-cluster-digit-kind-of-car-of-rev-when-closed
  (implies (and (code-point-list-listp x)
                (consp x)
                (equal (bidi-leading-number x arabic ver) x))
           (bidi-cluster-digit-kind (car (rev x)) arabic ver))
  :induct (bidi-leading-number x arabic ver)
  :enable (bidi-leading-number rev))

(defrulel bidi-leading-number-of-append-of-digit
  (implies (and (code-point-list-listp x)
                (equal (bidi-leading-number x arabic ver) x)
                (bidi-cluster-digit-kind d arabic ver))
           (equal (bidi-leading-number (append x (list d)) arabic ver)
                  (append x (list (code-point-list-fix d)))))
  :cases ((consp x))
  :enable bidi-leading-number)

(defrulel bidi-leading-number-of-append-of-separator-and-digit
  (implies (and (code-point-list-listp x)
                (consp x)
                (equal (bidi-leading-number x arabic ver) x)
                (bidi-cluster-joins-p s (car (rev x)) d arabic ver))
           (equal (bidi-leading-number (append x (list s d)) arabic ver)
                  (append x
                          (list (code-point-list-fix s)
                                (code-point-list-fix d)))))
  :enable bidi-leading-number)

(defrulel bidi-leading-number-of-rev-of-bidi-leading-number
  (equal (bidi-leading-number (rev (bidi-leading-number clusters arabic ver))
                              arabic
                              ver)
         (rev (bidi-leading-number clusters arabic ver)))
  :induct (bidi-leading-number clusters arabic ver)
  :enable bidi-leading-number)

(defrulel bidi-leading-number-when-not-consp-of-bidi-after-leading-number
  (implies (not (consp (bidi-after-leading-number clusters arabic ver)))
           (equal (equal (bidi-leading-number clusters arabic ver)
                         (code-point-list-list-fix clusters))
                  t))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number bidi-after-leading-number))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Clusters whose digits are of one class.

(local
 (define digit-cluster-p ((cluster code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (and (bidi-cluster-digit-kind cluster nil ver) t)
   :hooks nil))

(local
 (define arabic-free-cluster-p ((cluster code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (not (and (consp cluster)
             (equal (bidi-class-kind (code-point-bidi-class (car cluster) ver))
                    :arabic-number)))
   :hooks nil))

(local
 (define european-free-cluster-p ((cluster code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (not (and (consp cluster)
             (equal (bidi-class-kind (code-point-bidi-class (car cluster) ver))
                    :european-number)))
   :hooks nil))

(local
 (std::deflist arabic-free-clusters-p (x ver)
   :guard (and (code-point-list-listp x)
               (versionp ver))
   (arabic-free-cluster-p x ver)))

(local
 (std::deflist european-free-clusters-p (x ver)
   :guard (and (code-point-list-listp x)
               (versionp ver))
   (european-free-cluster-p x ver)))

(local
 (define uniform-clusters-p ((clusters code-point-list-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (arabic-free-clusters-p clusters ver)
       (european-free-clusters-p clusters ver))
   :hooks nil))

(defrulel digit-cluster-p-when-bidi-cluster-digit-kind
  (implies (bidi-cluster-digit-kind cluster arabic ver)
           (digit-cluster-p cluster ver))
  :enable (digit-cluster-p bidi-cluster-digit-kind))

(defruledl bidi-cluster-digit-kind-when-arabic-free-cluster-p
  (implies (arabic-free-cluster-p cluster ver)
           (equal (bidi-cluster-digit-kind cluster arabic ver)
                  (and (digit-cluster-p cluster ver)
                       (if arabic :arabic-number :european-number))))
  :enable (bidi-cluster-digit-kind digit-cluster-p arabic-free-cluster-p))

(defruledl bidi-cluster-digit-kind-when-european-free-cluster-p
  (implies (european-free-cluster-p cluster ver)
           (equal (bidi-cluster-digit-kind cluster arabic ver)
                  (and (digit-cluster-p cluster ver)
                       :arabic-number)))
  :enable (bidi-cluster-digit-kind digit-cluster-p european-free-cluster-p))

(defrulel digit-cluster-p-of-code-point-list-fix
  (equal (digit-cluster-p (code-point-list-fix cluster) ver)
         (digit-cluster-p cluster ver))
  :enable digit-cluster-p)

(defrulel arabic-free-cluster-p-of-code-point-list-fix
  (equal (arabic-free-cluster-p (code-point-list-fix cluster) ver)
         (arabic-free-cluster-p cluster ver))
  :enable arabic-free-cluster-p)

(defrulel european-free-cluster-p-of-code-point-list-fix
  (equal (european-free-cluster-p (code-point-list-fix cluster) ver)
         (european-free-cluster-p cluster ver))
  :enable european-free-cluster-p)

(defrulel arabic-free-clusters-p-of-bidi-leading-number
  (implies (arabic-free-clusters-p clusters ver)
           (arabic-free-clusters-p (bidi-leading-number clusters arabic ver)
                                   ver))
  :induct (bidi-leading-number clusters arabic ver)
  :enable bidi-leading-number)

(defrulel european-free-clusters-p-of-bidi-leading-number
  (implies (european-free-clusters-p clusters ver)
           (european-free-clusters-p (bidi-leading-number clusters arabic ver)
                                     ver))
  :induct (bidi-leading-number clusters arabic ver)
  :enable bidi-leading-number)

(defrulel arabic-free-clusters-p-of-code-point-list-list-fix
  (implies (arabic-free-clusters-p clusters ver)
           (arabic-free-clusters-p (code-point-list-list-fix clusters) ver))
  :induct (len clusters)
  :enable (code-point-list-list-fix len))

(defrulel european-free-clusters-p-of-code-point-list-list-fix
  (implies (european-free-clusters-p clusters ver)
           (european-free-clusters-p (code-point-list-list-fix clusters) ver))
  :induct (len clusters)
  :enable (code-point-list-list-fix len))

(defrulel arabic-free-clusters-p-of-bidi-after-leading-number
  (implies (arabic-free-clusters-p clusters ver)
           (arabic-free-clusters-p
            (bidi-after-leading-number clusters arabic ver)
            ver))
  :induct (bidi-after-leading-number clusters arabic ver)
  :enable bidi-after-leading-number)

(defrulel european-free-clusters-p-of-bidi-after-leading-number
  (implies (european-free-clusters-p clusters ver)
           (european-free-clusters-p
            (bidi-after-leading-number clusters arabic ver)
            ver))
  :induct (bidi-after-leading-number clusters arabic ver)
  :enable bidi-after-leading-number)

; When the digits are of one class, the cluster after a number
; does not join the first digit of the number to the cluster after it:
; it does not join the last digit to that cluster,
; and the two digits are of the same kind.

(defrulel bidi-cluster-digit-kind-when-not-consp
  (implies (not (consp cluster))
           (equal (bidi-cluster-digit-kind cluster arabic ver)
                  nil))
  :enable bidi-cluster-digit-kind)

(defrulel not-bidi-cluster-joins-p-after-bidi-leading-number-when-arabic-free
  (implies (and (arabic-free-clusters-p clusters ver)
                (bidi-cluster-digit-kind (car clusters) arabic ver))
           (not (bidi-cluster-joins-p
                 (car (bidi-after-leading-number clusters arabic ver))
                 (car clusters)
                 (cadr (bidi-after-leading-number clusters arabic ver))
                 arabic
                 ver)))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number
           bidi-after-leading-number
           bidi-cluster-joins-p
           bidi-cluster-digit-kind-when-arabic-free-cluster-p))

(defrulel not-bidi-cluster-joins-p-after-bidi-leading-number-when-european-free
  (implies (and (european-free-clusters-p clusters ver)
                (bidi-cluster-digit-kind (car clusters) arabic ver))
           (not (bidi-cluster-joins-p
                 (car (bidi-after-leading-number clusters arabic ver))
                 (car clusters)
                 (cadr (bidi-after-leading-number clusters arabic ver))
                 arabic
                 ver)))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number
           bidi-after-leading-number
           bidi-cluster-joins-p
           bidi-cluster-digit-kind-when-european-free-cluster-p))

(defrulel not-bidi-cluster-joins-p-after-bidi-leading-number
  (implies (and (uniform-clusters-p clusters ver)
                (bidi-cluster-digit-kind (car clusters) arabic ver))
           (not (bidi-cluster-joins-p
                 (car (bidi-after-leading-number clusters arabic ver))
                 (car clusters)
                 (cadr (bidi-after-leading-number clusters arabic ver))
                 arabic
                 ver)))
  :enable uniform-clusters-p)

(defrulel digit-cluster-p-of-car-of-rev-of-bidi-leading-number
  (implies (bidi-cluster-digit-kind (car clusters) arabic ver)
           (digit-cluster-p
            (car (rev (bidi-leading-number clusters arabic ver)))
            ver))
  :induct (bidi-leading-number clusters arabic ver)
  :enable bidi-leading-number)

(defrulel bidi-cluster-digit-kind-when-digit-cluster-p
  (implies (digit-cluster-p cluster ver)
           (bidi-cluster-digit-kind cluster arabic ver))
  :enable (digit-cluster-p bidi-cluster-digit-kind))

(defrulel not-digit-cluster-p-of-car-of-bidi-after-leading-number
  (not (digit-cluster-p (car (bidi-after-leading-number clusters arabic ver))
                        ver))
  :use not-bidi-cluster-digit-kind-of-car-of-bidi-after-leading-number
  :disable not-bidi-cluster-digit-kind-of-car-of-bidi-after-leading-number)

(defrulel digit-cluster-p-of-bidi-mirror-code-points
  (equal (digit-cluster-p (bidi-mirror-code-points cluster ver) ver)
         (digit-cluster-p cluster ver))
  :enable digit-cluster-p)

(defrulel arabic-free-cluster-p-of-bidi-mirror-code-points
  (equal (arabic-free-cluster-p (bidi-mirror-code-points cluster ver) ver)
         (arabic-free-cluster-p cluster ver))
  :enable arabic-free-cluster-p)

(defrulel european-free-cluster-p-of-bidi-mirror-code-points
  (equal (european-free-cluster-p (bidi-mirror-code-points cluster ver) ver)
         (european-free-cluster-p cluster ver))
  :enable european-free-cluster-p)

(defrulel bidi-show-clusters-when-not-consp
  (implies (not (consp clusters))
           (equal (bidi-show-clusters clusters arabic ver)
                  nil))
  :expand ((bidi-show-clusters clusters arabic ver)
           (bidi-leading-number clusters arabic ver)
           (bidi-after-leading-number clusters arabic ver)))

; The last cluster of the display of a list of clusters
; is a digit of the kind of the first cluster of the list,
; or it is not a digit and the first cluster of the list is not a digit.

(defrulel digit-kind-of-last-of-bidi-show-clusters-when-arabic-free
  (implies (arabic-free-clusters-p clusters ver)
           (equal (bidi-cluster-digit-kind
                   (car (rev (bidi-show-clusters clusters arabic2 ver)))
                   arabic
                   ver)
                  (bidi-cluster-digit-kind (car clusters) arabic ver)))
  :cases ((not (consp clusters))
          (bidi-cluster-digit-kind (car clusters) arabic2 ver))
  :expand (bidi-show-clusters clusters arabic2 ver)
  :enable bidi-cluster-digit-kind-when-arabic-free-cluster-p)

(defrulel digit-kind-of-last-of-bidi-show-clusters-when-european-free
  (implies (european-free-clusters-p clusters ver)
           (equal (bidi-cluster-digit-kind
                   (car (rev (bidi-show-clusters clusters arabic2 ver)))
                   arabic
                   ver)
                  (bidi-cluster-digit-kind (car clusters) arabic ver)))
  :cases ((not (consp clusters))
          (bidi-cluster-digit-kind (car clusters) arabic2 ver))
  :expand (bidi-show-clusters clusters arabic2 ver)
  :enable bidi-cluster-digit-kind-when-european-free-cluster-p)

; The cluster after a number does not join the number
; to what the display has on the other side of it.

(defrulel not-bidi-cluster-joins-p-in-display-when-arabic-free
  (implies (and (arabic-free-clusters-p clusters ver)
                (bidi-cluster-digit-kind (car clusters) arabic ver))
           (not (bidi-cluster-joins-p
                 (car (bidi-after-leading-number clusters arabic ver))
                 (car clusters)
                 (car (rev (bidi-show-clusters
                            (cdr (bidi-after-leading-number clusters
                                                            arabic
                                                            ver))
                            arabic2
                            ver)))
                 arabic
                 ver)))
  :use not-bidi-cluster-joins-p-after-bidi-leading-number-when-arabic-free
  :disable not-bidi-cluster-joins-p-after-bidi-leading-number-when-arabic-free
  :enable (bidi-cluster-joins-p
           bidi-cluster-digit-kind-when-arabic-free-cluster-p))

(defrulel not-bidi-cluster-joins-p-in-display-when-european-free
  (implies (and (european-free-clusters-p clusters ver)
                (bidi-cluster-digit-kind (car clusters) arabic ver))
           (not (bidi-cluster-joins-p
                 (car (bidi-after-leading-number clusters arabic ver))
                 (car clusters)
                 (car (rev (bidi-show-clusters
                            (cdr (bidi-after-leading-number clusters
                                                            arabic
                                                            ver))
                            arabic2
                            ver)))
                 arabic
                 ver)))
  :use not-bidi-cluster-joins-p-after-bidi-leading-number-when-european-free
  :disable not-bidi-cluster-joins-p-after-bidi-leading-number-when-european-free
  :enable (bidi-cluster-joins-p
           bidi-cluster-digit-kind-when-european-free-cluster-p))

(defrulel not-bidi-cluster-joins-p-in-display
  (implies (and (uniform-clusters-p clusters ver)
                (bidi-cluster-digit-kind (car clusters) arabic ver))
           (not (bidi-cluster-joins-p
                 (car (bidi-after-leading-number clusters arabic ver))
                 (car clusters)
                 (car (rev (bidi-show-clusters
                            (cdr (bidi-after-leading-number clusters
                                                            arabic
                                                            ver))
                            arabic2
                            ver)))
                 arabic
                 ver)))
  :enable uniform-clusters-p)

; So the reversed display starts with the reversed number,
; and after it comes the cluster that followed the number in the name.

(defrulel append-of-rev-of-cdr-of-bidi-leading-number
  (implies (bidi-cluster-digit-kind (car clusters) arabic ver)
           (equal (append (rev (cdr (bidi-leading-number clusters arabic ver)))
                          (cons (code-point-list-fix (car clusters)) y))
                  (append (rev (bidi-leading-number clusters arabic ver)) y)))
  :expand (rev (bidi-leading-number clusters arabic ver)))

(defrulel bidi-leading-number-of-rev-of-display
  (implies (and (uniform-clusters-p clusters ver)
                (consp (bidi-after-leading-number clusters arabic ver)))
           (equal (bidi-leading-number
                   (append
                    (rev (bidi-leading-number clusters arabic ver))
                    (cons (bidi-mirror-code-points
                           (car (bidi-after-leading-number clusters arabic ver))
                           ver)
                          (rev (bidi-show-clusters
                                (cdr (bidi-after-leading-number clusters
                                                                arabic
                                                                ver))
                                arabic2
                                ver))))
                   arabic
                   ver)
                  (rev (bidi-leading-number clusters arabic ver))))
  :cases ((bidi-cluster-digit-kind (car clusters) arabic ver))
  :expand (:free (x y) (bidi-leading-number (cons x y) arabic ver)))

(defrulel bidi-after-leading-number-of-rev-of-display
  (implies (and (uniform-clusters-p clusters ver)
                (consp (bidi-after-leading-number clusters arabic ver)))
           (equal (bidi-after-leading-number
                   (append
                    (rev (bidi-leading-number clusters arabic ver))
                    (cons (bidi-mirror-code-points
                           (car (bidi-after-leading-number clusters arabic ver))
                           ver)
                          (rev (bidi-show-clusters
                                (cdr (bidi-after-leading-number clusters
                                                                arabic
                                                                ver))
                                arabic2
                                ver))))
                   arabic
                   ver)
                  (cons (bidi-mirror-code-points
                         (car (bidi-after-leading-number clusters arabic ver))
                         ver)
                        (rev (bidi-show-clusters
                              (cdr (bidi-after-leading-number clusters
                                                              arabic
                                                              ver))
                              arabic2
                              ver)))))
  :cases ((bidi-cluster-digit-kind (car clusters) arabic ver))
  :expand ((:free (x y) (bidi-after-leading-number (cons x y) arabic ver))))

; The first layer.

(defrulel uniform-clusters-p-of-cdr-of-bidi-after-leading-number
  (implies (uniform-clusters-p clusters ver)
           (uniform-clusters-p
            (cdr (bidi-after-leading-number clusters arabic ver))
            ver))
  :enable uniform-clusters-p)

(defrulel append-of-bidi-leading-number-and-cons-of-bidi-after-leading-number
  (implies (consp (bidi-after-leading-number clusters arabic ver))
           (equal (append (bidi-leading-number clusters arabic ver)
                          (cons (car (bidi-after-leading-number clusters
                                                                arabic
                                                                ver))
                                (cdr (bidi-after-leading-number clusters
                                                                arabic
                                                                ver))))
                  (code-point-list-list-fix clusters))))

(defrulel bidi-read-clusters-of-rev-of-bidi-show-clusters
  (implies (uniform-clusters-p clusters ver)
           (equal (bidi-read-clusters
                   (rev (bidi-show-clusters clusters arabic ver))
                   arabic
                   ver)
                  (code-point-list-list-fix clusters)))
  :induct (bidi-show-clusters clusters arabic ver)
  :enable bidi-show-clusters
  :expand (:free (x) (bidi-read-clusters x arabic ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Clusters and lists of code points.

(defrulel consp-of-bidi-clusters
  (equal (consp (bidi-clusters cps ver))
         (consp cps))
  :expand (bidi-clusters cps ver))

(defrulel bidi-clusters-when-not-consp
  (implies (not (consp cps))
           (equal (bidi-clusters cps ver)
                  nil))
  :expand (bidi-clusters cps ver))

(defrulel flatten-of-bidi-clusters
  (equal (acl2::flatten (bidi-clusters cps ver))
         (code-point-list-fix cps))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           acl2::flatten
           code-point-list-fix)
  :expand (acl2::flatten (bidi-clusters (cdr cps) ver)))

(defrulel bidi-clusters-of-append
  (implies (not (and (consp y)
                     (bidi-mark-code-point-p (car y) ver)))
           (equal (bidi-clusters (append x y) ver)
                  (append (bidi-clusters x ver)
                          (bidi-clusters y ver))))
  :induct (bidi-clusters x ver)
  :enable bidi-clusters
  :expand (:free (a b) (bidi-clusters (cons a b) ver)))

(defrulel bidi-clusters-when-cluster
  (implies (and (consp cluster)
                (bidi-marks-p (cdr cluster) ver))
           (equal (bidi-clusters cluster ver)
                  (list (code-point-list-fix cluster))))
  :induct (len cluster)
  :enable (len
           bidi-clusters
           code-point-list-fix))

; A cluster that starts with a code point that is not a mark,
; and lists of such clusters.

(local
 (define proper-cluster-p ((cluster code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (and (consp cluster)
        (not (bidi-mark-code-point-p (car cluster) ver))
        (bidi-marks-p (cdr cluster) ver))
   :hooks nil))

(local
 (std::deflist proper-clusters-p (x ver)
   :guard (and (code-point-list-listp x)
               (versionp ver))
   (proper-cluster-p x ver)))

(defrulel not-bidi-mark-code-point-p-of-car-of-flatten-when-proper
  (implies (and (proper-clusters-p clusters ver)
                (consp (acl2::flatten clusters)))
           (not (bidi-mark-code-point-p (car (acl2::flatten clusters)) ver)))
  :expand (acl2::flatten clusters)
  :enable proper-cluster-p)

(defrulel consp-of-flatten-when-proper
  (implies (and (proper-clusters-p clusters ver)
                (consp clusters))
           (consp (acl2::flatten clusters)))
  :expand (acl2::flatten clusters)
  :enable proper-cluster-p)

(defrulel bidi-clusters-of-flatten-when-proper
  (implies (and (code-point-list-listp clusters)
                (proper-clusters-p clusters ver))
           (equal (bidi-clusters (acl2::flatten clusters) ver)
                  clusters))
  :induct (len clusters)
  :enable (len
           acl2::flatten
           proper-cluster-p))

(defrulel bidi-clusters-shape
  (and (proper-clusters-p (cdr (bidi-clusters cps ver)) ver)
       (implies (consp cps)
                (and (consp (car (bidi-clusters cps ver)))
                     (equal (car (car (bidi-clusters cps ver)))
                            (code-point-fix (car cps)))
                     (bidi-marks-p (cdr (car (bidi-clusters cps ver))) ver))))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           proper-cluster-p))

(defrulel proper-clusters-p-of-bidi-clusters
  (implies (not (and (consp cps)
                     (bidi-mark-code-point-p (car cps) ver)))
           (proper-clusters-p (bidi-clusters cps ver) ver))
  :cases ((consp cps))
  :expand (proper-clusters-p (bidi-clusters cps ver) ver)
  :enable proper-cluster-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The display of a list of proper clusters is a list of proper clusters.

(defrulel bidi-mark-code-point-p-of-bidi-mirror-code-point
  (equal (bidi-mark-code-point-p (bidi-mirror-code-point cp ver) ver)
         (bidi-mark-code-point-p cp ver))
  :enable bidi-mark-code-point-p)

(defrulel bidi-marks-p-of-bidi-mirror-code-points
  (equal (bidi-marks-p (bidi-mirror-code-points cps ver) ver)
         (bidi-marks-p cps ver))
  :induct (len cps)
  :enable (len bidi-mirror-code-points))

(defrulel bidi-marks-p-of-code-point-list-fix
  (equal (bidi-marks-p (code-point-list-fix cps) ver)
         (bidi-marks-p cps ver))
  :induct (len cps)
  :enable (len code-point-list-fix))

(defrulel proper-cluster-p-of-bidi-mirror-code-points
  (equal (proper-cluster-p (bidi-mirror-code-points cluster ver) ver)
         (proper-cluster-p cluster ver))
  :enable proper-cluster-p)

(defrulel proper-cluster-p-of-code-point-list-fix
  (equal (proper-cluster-p (code-point-list-fix cluster) ver)
         (proper-cluster-p cluster ver))
  :enable proper-cluster-p)

(defrulel proper-clusters-p-of-code-point-list-list-fix
  (implies (proper-clusters-p clusters ver)
           (proper-clusters-p (code-point-list-list-fix clusters) ver))
  :induct (len clusters)
  :enable (code-point-list-list-fix len))

(defrulel proper-clusters-p-of-bidi-leading-number
  (implies (proper-clusters-p clusters ver)
           (proper-clusters-p (bidi-leading-number clusters arabic ver) ver))
  :induct (bidi-leading-number clusters arabic ver)
  :enable bidi-leading-number)

(defrulel proper-clusters-p-of-bidi-after-leading-number
  (implies (proper-clusters-p clusters ver)
           (proper-clusters-p (bidi-after-leading-number clusters arabic ver)
                              ver))
  :induct (bidi-after-leading-number clusters arabic ver)
  :enable bidi-after-leading-number)

(defrulel proper-clusters-p-of-bidi-show-clusters
  (implies (proper-clusters-p clusters ver)
           (proper-clusters-p (bidi-show-clusters clusters arabic ver) ver))
  :induct (bidi-show-clusters clusters arabic ver)
  :enable bidi-show-clusters)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first and the last cluster of the display of a list of clusters.

(defrulel consp-of-bidi-show-clusters
  (equal (consp (bidi-show-clusters clusters arabic ver))
         (consp clusters))
  :cases ((bidi-cluster-digit-kind (car clusters) arabic ver))
  :expand (bidi-show-clusters clusters arabic ver))

(defrulel car-of-rev-of-bidi-show-clusters-when-not-digit
  (implies (and (consp clusters)
                (not (bidi-cluster-digit-kind (car clusters) arabic ver)))
           (equal (car (rev (bidi-show-clusters clusters arabic ver)))
                  (bidi-mirror-code-points (car clusters) ver)))
  :expand (bidi-show-clusters clusters arabic ver))

(defrulel consp-when-consp-of-bidi-after-leading-number
  (implies (consp (bidi-after-leading-number clusters arabic ver))
           (consp clusters))
  :rule-classes :forward-chaining
  :expand (bidi-after-leading-number clusters arabic ver))

(defrulel car-of-rev-of-cdr
  (implies (consp (cdr x))
           (equal (car (rev (cdr x)))
                  (car (rev x))))
  :expand (rev x))

(defrulel car-of-rev-of-code-point-list-list-fix
  (equal (car (rev (code-point-list-list-fix x)))
         (code-point-list-fix (car (rev x))))
  :induct (len x)
  :enable (len rev code-point-list-list-fix))

(defrulel car-of-rev-of-bidi-after-leading-number
  (implies (consp (bidi-after-leading-number clusters arabic ver))
           (equal (car (rev (bidi-after-leading-number clusters arabic ver)))
                  (code-point-list-fix (car (rev clusters)))))
  :induct (bidi-after-leading-number clusters arabic ver)
  :enable bidi-after-leading-number)

(defrulel car-of-bidi-after-leading-number-when-last
  (implies (and (consp (bidi-after-leading-number clusters arabic ver))
                (not (consp (cdr (bidi-after-leading-number clusters
                                                            arabic
                                                            ver)))))
           (equal (car (bidi-after-leading-number clusters arabic ver))
                  (code-point-list-fix (car (rev clusters)))))
  :use car-of-rev-of-bidi-after-leading-number
  :disable car-of-rev-of-bidi-after-leading-number
  :expand ((rev (bidi-after-leading-number clusters arabic ver))
           (rev (cdr (bidi-after-leading-number clusters arabic ver)))))

(defrulel bidi-cluster-landmark-p-when-bidi-cluster-digit-kind
  (implies (bidi-cluster-digit-kind cluster arabic ver)
           (bidi-cluster-landmark-p cluster ver))
  :enable (bidi-cluster-digit-kind
           bidi-cluster-landmark-p
           bidi-digit-p))

(defrulel bidi-cluster-landmark-p-of-car-of-bidi-leading-number
  (implies (and (consp clusters)
                (not (consp (bidi-after-leading-number clusters arabic ver))))
           (bidi-cluster-landmark-p
            (car (bidi-leading-number clusters arabic ver))
            ver))
  :cases ((bidi-cluster-digit-kind (car clusters) arabic ver)))

(defrulel bidi-cluster-landmark-p-of-car-of-bidi-show-clusters
  (implies (and (consp clusters)
                (bidi-cluster-landmark-p (car (rev clusters)) ver))
           (bidi-cluster-landmark-p
            (car (bidi-show-clusters clusters arabic ver))
            ver))
  :induct (bidi-show-clusters clusters arabic ver)
  :enable bidi-show-clusters)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The way back finds the middle part of a display.

(defrulel bidi-clusters-before-landmark-of-append
  (implies (equal (bidi-clusters-before-landmark x ver)
                  (len x))
           (equal (bidi-clusters-before-landmark (append x y) ver)
                  (+ (len x)
                     (bidi-clusters-before-landmark y ver))))
  :induct (len x)
  :enable (len fix bidi-clusters-before-landmark))

(defrulel bidi-clusters-before-landmark-when-landmark
  (implies (bidi-cluster-landmark-p (car clusters) ver)
           (equal (bidi-clusters-before-landmark clusters ver)
                  0))
  :expand (bidi-clusters-before-landmark clusters ver))

(defrulel bidi-clusters-to-last-letter-of-append-when-no-letter
  (implies (equal (bidi-clusters-to-last-letter y ver) 0)
           (equal (bidi-clusters-to-last-letter (append x y) ver)
                  (bidi-clusters-to-last-letter x ver)))
  :induct (len x)
  :enable (len fix bidi-clusters-to-last-letter))

(defrulel bidi-clusters-to-last-letter-of-append-when-letter
  (implies (< 0 (bidi-clusters-to-last-letter y ver))
           (equal (bidi-clusters-to-last-letter (append x y) ver)
                  (+ (len x)
                     (bidi-clusters-to-last-letter y ver))))
  :induct (len x)
  :enable (len fix bidi-clusters-to-last-letter))

(defrulel bidi-clusters-to-last-letter-when-last-is-letter
  (implies (bidi-cluster-letter-p (car (rev x)) ver)
           (equal (bidi-clusters-to-last-letter x ver)
                  (len x)))
  :induct (len x)
  :enable (len fix rev bidi-clusters-to-last-letter))

; The second layer.

(local (in-theory (enable fix)))

(defrulel len-positive-when-consp
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear
  :enable len)

(defrulel nthcdr-of-len-of-append
  (equal (nthcdr (len x) (append x y))
         y)
  :induct (len x)
  :enable (len nthcdr append))

(defrulel nthcdr-of-len-plus-of-append
  (implies (natp n)
           (and (equal (nthcdr (+ (len x) n) (append x y))
                       (nthcdr n y))
                (equal (nthcdr (+ n (len x)) (append x y))
                       (nthcdr n y))))
  :induct (len x)
  :enable (len nthcdr append))

(defrulel take-of-len-of-append
  (equal (take (len x) (append x y))
         (acl2::list-fix x))
  :induct (len x)
  :enable (len take append acl2::list-fix))

(defrulel take-of-len-plus-of-append
  (implies (natp n)
           (and (equal (take (+ (len x) n) (append x y))
                       (append x (take n y)))
                (equal (take (+ n (len x)) (append x y))
                       (append x (take n y)))))
  :induct (len x)
  :enable (len take append))

(defrulel nthcdr-of-len-when-true-listp
  (implies (true-listp x)
           (equal (nthcdr (len x) x)
                  nil))
  :induct (len x)
  :enable (len nthcdr))

(defrulel bidi-name-read-of-three-parts
  (implies (and (code-point-listp before)
                (code-point-list-listp shown)
                (code-point-listp after)
                (proper-clusters-p shown ver)
                (consp shown)
                (equal (bidi-clusters-before-landmark
                        (bidi-clusters before ver)
                        ver)
                       (len (bidi-clusters before ver)))
                (bidi-cluster-landmark-p (car shown) ver)
                (bidi-cluster-letter-p (car (rev shown)) ver)
                (equal (bidi-clusters-to-last-letter
                        (bidi-clusters after ver)
                        ver)
                       0)
                (not (and (consp after)
                          (bidi-mark-code-point-p (car after) ver))))
           (equal (bidi-name-read
                   (append before (acl2::flatten shown) after)
                   ver)
                  (append before
                          (acl2::flatten
                           (bidi-read-clusters (rev shown) nil ver))
                          after)))
  :enable (bidi-name-read fix nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The three parts of a name.

(local
 (define split-induction (start end x)
   (if (zp start)
       (list end x)
     (split-induction (- start 1) (- end 1) (cdr x)))
   :verify-guards nil
   :hooks nil))

(defrulel append-of-take-and-nthcdr-of-take
  (implies (and (natp start)
                (natp end)
                (<= start end))
           (equal (append (take start x)
                          (append (nthcdr start (take end x)) y))
                  (append (take end x) y)))
  :induct (split-induction start end x)
  :enable (split-induction take nthcdr))

(defrulel append-of-take-and-nthcdr-when-true-listp
  (implies (and (true-listp x)
                (natp end)
                (<= end (len x)))
           (equal (append (take end x) (nthcdr end x))
                  x))
  :induct (nthcdr end x)
  :enable (take nthcdr len))

; The part before the first letter has no letter, digit or bracket.

(local
 (define landmark-code-point-p ((cp code-point-p) (ver versionp))
   :returns (yes/no booleanp)
   (or (bidi-right-to-left-letter-p cp ver)
       (bidi-digit-p cp ver)
       (and (code-point-bidi-bracket cp ver) t))
   :hooks nil))

(local
 (define plain-code-point-p ((cp code-point-p) (ver versionp))
   :returns (yes/no booleanp)
   (not (landmark-code-point-p cp ver))
   :hooks nil))

(local
 (std::deflist plain-code-points-p (x ver)
   :guard (and (code-point-listp x)
               (versionp ver))
   (plain-code-point-p x ver)))

(defrulel plain-code-points-p-of-take-of-bidi-name-start
  (implies (bidi-rule-wide-start-p name ver)
           (plain-code-points-p (take (bidi-name-start name ver) name) ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           bidi-rule-wide-start-p
           plain-code-point-p
           landmark-code-point-p
           bidi-right-to-left-letter-p
           bidi-digit-p
           take))

(defrulel bidi-clusters-before-landmark-of-cdr-when-all
  (implies (equal (bidi-clusters-before-landmark x ver)
                  (len x))
           (equal (bidi-clusters-before-landmark (cdr x) ver)
                  (len (cdr x))))
  :expand (bidi-clusters-before-landmark x ver)
  :enable len)

(defrulel bidi-clusters-before-landmark-of-bidi-clusters-when-plain
  (implies (plain-code-points-p cps ver)
           (equal (bidi-clusters-before-landmark (bidi-clusters cps ver) ver)
                  (len (bidi-clusters cps ver))))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-clusters-before-landmark
           bidi-cluster-landmark-p
           plain-code-point-p
           landmark-code-point-p
           len))

; The middle part starts with a letter.

(defrulel bidi-right-to-left-letter-p-of-nth-of-bidi-name-start
  (implies (< (bidi-name-start name ver) (len name))
           (bidi-right-to-left-letter-p (nth (bidi-name-start name ver) name)
                                        ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start nth len))

(defrulel not-bidi-mark-code-point-p-when-bidi-right-to-left-letter-p
  (implies (bidi-right-to-left-letter-p cp ver)
           (not (bidi-mark-code-point-p cp ver)))
  :enable (bidi-right-to-left-letter-p bidi-mark-code-point-p))

(defrulel bidi-cluster-letter-p-of-car-of-bidi-clusters
  (implies (consp cps)
           (equal (bidi-cluster-letter-p (car (bidi-clusters cps ver)) ver)
                  (bidi-right-to-left-letter-p (car cps) ver)))
  :enable bidi-cluster-letter-p)

(defrulel not-bidi-cluster-digit-kind-when-bidi-cluster-letter-p
  (implies (bidi-cluster-letter-p cluster ver)
           (not (bidi-cluster-digit-kind cluster arabic ver)))
  :enable (bidi-cluster-letter-p
           bidi-right-to-left-letter-p
           bidi-cluster-digit-kind))

; The middle part ends with a cluster
; that starts with a letter, a digit or a bracket.

(defrulel bidi-name-start-below-bidi-name-to-last-letter-or-digit
  (implies (< (bidi-name-start name ver) (len name))
           (< (bidi-name-start name ver)
              (bidi-name-to-last-letter-or-digit name ver)))
  :rule-classes :linear
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           bidi-name-to-last-letter-or-digit
           len))

(local
 (define take-induction (a x)
   (if (or (zp a)
           (equal a 1))
       x
     (take-induction (- a 1) (cdr x)))
   :verify-guards nil
   :hooks nil))

(defruledl take-of-+
  (implies (and (posp a)
                (natp k))
           (equal (take (+ a k) x)
                  (append (take (- a 1) x)
                          (cons (nth (- a 1) x)
                                (take k (nthcdr a x))))))
  :induct (take-induction a x)
  :enable (take-induction take nthcdr nth))

(defrulel take-of-+-of-bidi-leading-marks
  (implies (posp a)
           (equal (take (+ a (bidi-leading-marks (nthcdr a x) ver)) x)
                  (append (take (- a 1) x)
                          (cons (nth (- a 1) x)
                                (take (bidi-leading-marks (nthcdr a x) ver)
                                      (nthcdr a x))))))
  :enable take-of-+)

(defrulel bidi-marks-p-of-take-of-bidi-leading-marks
  (bidi-marks-p (take (bidi-leading-marks x ver) x) ver)
  :induct (bidi-leading-marks x ver)
  :enable (bidi-leading-marks take))

(defrulel landmark-code-point-p-of-nth-of-bidi-name-to-last-letter-or-digit
  (implies (< 0 (bidi-name-to-last-letter-or-digit name ver))
           (landmark-code-point-p
            (nth (+ -1 (bidi-name-to-last-letter-or-digit name ver)) name)
            ver))
  :induct (bidi-name-to-last-letter-or-digit name ver)
  :enable (bidi-name-to-last-letter-or-digit
           landmark-code-point-p
           nth))

(defrulel landmark-code-point-p-of-nth-of-bidi-name-pairs-end
  (implies (and (closes-ok pairs name ver)
                (< 0 (bidi-name-pairs-end pairs name ver)))
           (landmark-code-point-p
            (nth (+ -1 (bidi-name-pairs-end pairs name ver)) name)
            ver))
  :induct (len pairs)
  :enable (len
           closes-ok
           bidi-name-pairs-end
           max
           landmark-code-point-p))

(defrulel not-bidi-mark-code-point-p-when-landmark-code-point-p
  (implies (landmark-code-point-p cp ver)
           (not (bidi-mark-code-point-p cp ver)))
  :enable (landmark-code-point-p
           bidi-right-to-left-letter-p
           bidi-digit-p
           bidi-mark-code-point-p))

(defrulel bidi-cluster-landmark-p-of-cons
  (equal (bidi-cluster-landmark-p (cons cp cps) ver)
         (landmark-code-point-p cp ver))
  :enable (bidi-cluster-landmark-p landmark-code-point-p))

(defrulel landmark-code-point-p-of-code-point-fix
  (equal (landmark-code-point-p (code-point-fix cp) ver)
         (landmark-code-point-p cp ver))
  :enable landmark-code-point-p)

(defrulel nthcdr-of-append-when-within
  (implies (<= (nfix n) (len x))
           (equal (nthcdr n (append x y))
                  (append (nthcdr n x) y)))
  :induct (nthcdr n x)
  :enable (nthcdr append len nfix))

(defrulel bidi-cluster-landmark-p-of-last-cluster-before-marks
  (implies (and (posp a)
                (natp start)
                (< start a)
                (landmark-code-point-p (nth (+ -1 a) x) ver))
           (bidi-cluster-landmark-p
            (car (rev (bidi-clusters
                       (nthcdr start
                               (take (+ a
                                        (bidi-leading-marks (nthcdr a x)
                                                            ver))
                                     x))
                       ver)))
            ver))
  :enable nfix)

(defrulel bidi-cluster-landmark-p-of-last-of-middle
  (implies (< (bidi-name-start name ver)
              (len name))
           (bidi-cluster-landmark-p
            (car (rev (bidi-clusters
                       (nthcdr (bidi-name-start name ver)
                               (take (bidi-name-end name ver) name))
                       ver)))
            ver))
  :enable (bidi-name-end max)
  :disable take-of-+-of-bidi-leading-marks)

; The part after the middle part has no letter
; and does not start with a mark.

(local
 (define letter-free-code-point-p ((cp code-point-p) (ver versionp))
   :returns (yes/no booleanp)
   (not (bidi-right-to-left-letter-p cp ver))
   :hooks nil))

(local
 (std::deflist letter-free-code-points-p (x ver)
   :guard (and (code-point-listp x)
               (versionp ver))
   (letter-free-code-point-p x ver)))

(defrulel letter-free-code-points-p-when-no-letter-or-digit
  (implies (equal (bidi-name-to-last-letter-or-digit name ver) 0)
           (letter-free-code-points-p name ver))
  :induct (bidi-name-to-last-letter-or-digit name ver)
  :enable (bidi-name-to-last-letter-or-digit
           letter-free-code-point-p))

(defrulel letter-free-code-points-p-of-nthcdr-when-after-last
  (implies (<= (bidi-name-to-last-letter-or-digit name ver) (nfix n))
           (letter-free-code-points-p (nthcdr n name) ver))
  :induct (nthcdr n name)
  :enable (nthcdr
           bidi-name-to-last-letter-or-digit
           letter-free-code-point-p
           nfix))

(defrulel letter-free-code-points-p-when-no-letter
  (implies (<= (len name) (bidi-name-start name ver))
           (letter-free-code-points-p name ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           letter-free-code-point-p
           len))

(defrulel bidi-clusters-to-last-letter-of-cdr-when-no-letter
  (implies (equal (bidi-clusters-to-last-letter x ver) 0)
           (equal (bidi-clusters-to-last-letter (cdr x) ver)
                  0))
  :expand (bidi-clusters-to-last-letter x ver))

(defrulel bidi-clusters-to-last-letter-of-bidi-clusters-when-letter-free
  (implies (letter-free-code-points-p cps ver)
           (equal (bidi-clusters-to-last-letter (bidi-clusters cps ver) ver)
                  0))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-clusters-to-last-letter
           bidi-cluster-letter-p
           letter-free-code-point-p))

(defrulel bidi-name-to-last-letter-or-digit-below-bidi-name-end
  (<= (bidi-name-to-last-letter-or-digit name ver)
      (bidi-name-end name ver))
  :rule-classes :linear
  :enable (bidi-name-end max))

(defrulel not-bidi-mark-code-point-p-of-nth-of-bidi-leading-marks
  (implies (< (bidi-leading-marks x ver) (len x))
           (not (bidi-mark-code-point-p (nth (bidi-leading-marks x ver) x)
                                        ver)))
  :induct (bidi-leading-marks x ver)
  :enable (bidi-leading-marks nth len))

(defrulel not-bidi-mark-code-point-p-of-nth-after-marks
  (implies (and (natp a)
                (< (+ a (bidi-leading-marks (nthcdr a x) ver))
                   (len x)))
           (not (bidi-mark-code-point-p
                 (nth (+ a (bidi-leading-marks (nthcdr a x) ver)) x)
                 ver)))
  :induct (nthcdr a x)
  :enable (nthcdr nth len))

(defrulel not-bidi-mark-code-point-p-of-nth-of-bidi-name-end
  (implies (< (bidi-name-end name ver) (len name))
           (not (bidi-mark-code-point-p (nth (bidi-name-end name ver) name)
                                        ver)))
  :enable (bidi-name-end max))

(defrulel not-bidi-mark-code-point-p-of-nth-of-bidi-name-end-when-consp
  (implies (consp (nthcdr (bidi-name-end name ver) name))
           (not (bidi-mark-code-point-p (nth (bidi-name-end name ver) name)
                                        ver)))
  :enable nfix)

; The digits of the middle part are of one class.

(defrulel not-bidi-class-kind-present-p-of-nthcdr
  (implies (not (bidi-class-kind-present-p kind x ver))
           (not (bidi-class-kind-present-p kind (nthcdr n x) ver)))
  :induct (nthcdr n x)
  :enable (nthcdr bidi-class-kind-present-p))

(defrulel not-bidi-class-kind-present-p-of-take
  (implies (and (not (bidi-class-kind-present-p kind x ver))
                (<= (nfix n) (len x)))
           (not (bidi-class-kind-present-p kind (take n x) ver)))
  :induct (take n x)
  :enable (take bidi-class-kind-present-p len nfix))

(defrulel arabic-free-clusters-p-of-bidi-clusters
  (implies (not (bidi-class-kind-present-p :arabic-number cps ver))
           (arabic-free-clusters-p (bidi-clusters cps ver) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-class-kind-present-p
           arabic-free-cluster-p))

(defrulel european-free-clusters-p-of-bidi-clusters
  (implies (not (bidi-class-kind-present-p :european-number cps ver))
           (european-free-clusters-p (bidi-clusters cps ver) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-class-kind-present-p
           european-free-cluster-p))

; A name with a letter is a right-to-left label.

(defrulel bidi-right-to-left-label-p-when-letter
  (implies (< (bidi-name-start name ver) (len name))
           (bidi-right-to-left-label-p name ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start
           bidi-right-to-left-letter-p
           bidi-right-to-left-label-p
           bidi-class-kind-present-p
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel bidi-name-read-of-bidi-name-display-when-no-letter
  (implies (and (code-point-listp name)
                (<= (len name) (bidi-name-start name ver)))
           (equal (bidi-name-read (bidi-name-display name ver) ver)
                  name))
  :enable (bidi-name-display
           bidi-name-read))

(defrulel bidi-name-read-of-bidi-name-display-when-letter
  (implies (and (code-point-listp name)
                (< (bidi-name-start name ver) (len name))
                (bidi-rule-wide-p name ver))
           (equal (bidi-name-read (bidi-name-display name ver) ver)
                  name))
  :enable (bidi-name-display
           bidi-rule-wide-p
           uniform-clusters-p
           nfix))

(defrulel bidi-name-read-of-bidi-name-display-when-code-point-listp
  (implies (and (code-point-listp name)
                (bidi-rule-wide-p name ver))
           (equal (bidi-name-read (bidi-name-display name ver) ver)
                  name))
  :cases ((< (bidi-name-start name ver) (len name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-display-theorems
  :short "The way back undoes the display
          that @(tsee bidi-name-display) computes,
          for a name that satisfies the wide rule;
          so that display is different for different names."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see bidi-rule-display).
     The first theorem is that @(tsee bidi-name-read)
     gives back a name that satisfies @(tsee bidi-rule-wide-p)
     from what @(tsee bidi-name-display) gives for it.
     The second follows:
     two names that satisfy the rule and for which
     @(tsee bidi-name-display) gives the same list of code points
     are the same name.
     The theorems are about @(tsee bidi-name-display),
     not about the Unicode Bidirectional Algorithm:
     that the algorithm displays these names so
     is the theorem of @(see bidi-rule-display-theorem).")
   (xdoc::p
    "The proof is in three layers.
     On lists of clusters whose digits are all of one class,
     @(tsee bidi-read-clusters) applied to the reverse
     of what @(tsee bidi-show-clusters) gives is the list:
     a number reversed is a number,
     and the cluster after a number does not join it to the digit
     that the display puts on its other side.
     On a list of code points in three parts,
     @(tsee bidi-name-read) finds the middle part
     if the first part has no letter, digit or bracket,
     the displayed middle part starts with one of them
     and ends with a letter,
     and the third part has no letter and does not start with a mark.
     Last, the three parts of a name that satisfies the rule
     are such parts."))

  (defrule bidi-name-read-of-bidi-name-display
    (implies (bidi-rule-wide-p name ver)
             (equal (bidi-name-read (bidi-name-display name ver) ver)
                    (code-point-list-fix name)))
    :use (:instance
          bidi-name-read-of-bidi-name-display-when-code-point-listp
          (name (code-point-list-fix name))))

  (defrule bidi-name-display-is-one-to-one
    (implies (and (bidi-rule-wide-p name1 ver)
                  (bidi-rule-wide-p name2 ver)
                  (equal (bidi-name-display name1 ver)
                         (bidi-name-display name2 ver)))
             (equal (code-point-list-fix name1)
                    (code-point-list-fix name2)))
    :rule-classes nil
    :use ((:instance bidi-name-read-of-bidi-name-display (name name1))
          (:instance bidi-name-read-of-bidi-name-display (name name2)))
    :disable bidi-name-read-of-bidi-name-display))
