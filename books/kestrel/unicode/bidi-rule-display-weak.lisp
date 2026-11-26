; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rule-display")
(include-book "bidi-weak-types")

(local (include-book "std/lists/top" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable fix nfix)))

; The classes are kept as they are written,
; and an equality with a list of repeated classes is not split.

(local (in-theory (disable bidi-class-fix-when-left-to-right
                           bidi-class-fix-when-right-to-left
                           bidi-class-fix-when-arabic-letter
                           bidi-class-fix-when-european-number
                           bidi-class-fix-when-european-separator
                           bidi-class-fix-when-european-terminator
                           bidi-class-fix-when-arabic-number
                           bidi-class-fix-when-common-separator
                           bidi-class-fix-when-nonspacing-mark
                           bidi-class-fix-when-boundary-neutral
                           bidi-class-fix-when-paragraph-separator
                           bidi-class-fix-when-segment-separator
                           bidi-class-fix-when-white-space
                           bidi-class-fix-when-other-neutral
                           bidi-class-fix-when-left-to-right-embedding
                           bidi-class-fix-when-left-to-right-override
                           bidi-class-fix-when-right-to-left-embedding
                           bidi-class-fix-when-right-to-left-override
                           bidi-class-fix-when-pop-directional-format
                           bidi-class-fix-when-left-to-right-isolate
                           bidi-class-fix-when-right-to-left-isolate
                           bidi-class-fix-when-first-strong-isolate
                           bidi-class-fix-when-pop-directional-isolate
                           acl2::equal-of-append-repeat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-rule-display-weak
  :parents (bidi-rule-display)
  :short "The classes that the weak rules give to the characters of a name
          that satisfies the wide rule, computed without those rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a step of the proof that the Unicode Bidirectional Algorithm
     displays a name that satisfies @(tsee bidi-rule-wide-p)
     as @(tsee bidi-name-display) says
     (see @(see bidi-rule-display-theorem)).
     The weak rules are the rules W1 to W7 of [UAX #9],
     the function @(tsee bidi-resolve-weak-types).
     The classes are the values of the @('Bidi_Class') property;
     see @(see bidi-rule-display) for the words used here.")
   (xdoc::p
    "Take a name that satisfies the wide rule
     and has a letter of class @('R') (@('Right_To_Left'))
     or @('AL') (@('Arabic_Letter'))
     or a digit of class @('AN') (@('Arabic_Number')),
     in a paragraph from left to right.
     The weak rules give every code point of a cluster the same class,
     and that class is:")
   (xdoc::ul
    (xdoc::li
     "@('R') for a cluster that starts with a right-to-left letter;")
    (xdoc::li
     "@('AN') for a cluster that starts with an Arabic digit,
      or with a European digit when the last right-to-left letter
      before it is of class @('AL');")
    (xdoc::li
     "@('EN') (@('European_Number'))
      for a cluster that starts with any other European digit;")
    (xdoc::li
     "the class of the two digits
      for a separator that is alone in its cluster
      and stands between two clusters that start with digits
      and get the same class,
      except that a separator of class @('ES')
      (@('European_Separator')) does this
      between European digits only;")
    (xdoc::li
     "@('L') (@('Left_To_Right')), the direction of the paragraph,
      for marks at the start of the name;")
    (xdoc::li
     "@('ON') (@('Other_Neutral')) for every other cluster."))
   (xdoc::p
    "The function @(tsee bidi-clusters-weak-classes)
     computes these classes,
     and the theorem of this book says that the weak rules give them
     (see @(see bidi-rule-display-weak-theorem)).
     The proof uses three of the conditions of the wide rule.
     The name has no letter of class @('L'),
     and no digit comes before its first right-to-left letter:
     otherwise a European digit could take the class @('L')
     [UAX #9, rule W7].
     And no terminator is next to a European digit:
     otherwise the terminator would take the class of the digit
     [UAX #9, rule W5]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-cluster-weak-class ((cluster code-point-listp)
                                 (previous code-point-listp)
                                 (next code-point-listp)
                                 (arabic booleanp)
                                 (ver versionp))
  :returns (class bidi-class-p)
  :short "The class that the weak rules give to the code points of a cluster
          of a name, in a paragraph from left to right,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the cluster, the cluster before it
     and the cluster after it, each an empty list if there is none,
     and @('arabic'), which says that the last right-to-left letter
     before the cluster is of class @('AL') (@('Arabic_Letter');
     see @(tsee bidi-arabic-after-cluster-p)).")
   (xdoc::p
    "A cluster that starts with a digit
     gets the class of the digit (see @(tsee bidi-cluster-digit-kind)).
     A separator that joins two digits
     (see @(tsee bidi-cluster-joins-p)) gets the class of those digits.
     A cluster that starts with a right-to-left letter
     gets the class @('R') (@('Right_To_Left')).
     A cluster that starts with a mark, which only the first cluster
     of a name can do, or with a letter of class @('L')
     (@('Left_To_Right')), gets the class @('L').
     Any other cluster gets the class @('ON') (@('Other_Neutral')).")
   (xdoc::p
    "This is what the weak rules give for a name
     that satisfies the wide rule and has a right-to-left letter
     or an Arabic digit (see @(see bidi-rule-display-weak)).
     For a cluster that starts with a code point
     that the wide rule does not allow,
     the function gives @('ON'),
     which need not be what the weak rules give."))
  (b* ((kind (bidi-cluster-digit-kind cluster arabic ver))
       ((when (equal kind :arabic-number)) (bidi-class-arabic-number))
       ((when kind) (bidi-class-european-number))
       ((when (bidi-cluster-joins-p cluster previous next arabic ver))
        (if (equal (bidi-cluster-digit-kind previous arabic ver)
                   :arabic-number)
            (bidi-class-arabic-number)
          (bidi-class-european-number)))
       ((unless (consp cluster)) (bidi-class-other-neutral))
       (class (code-point-bidi-class (car cluster) ver)))
    (bidi-class-case class
                     :right-to-left (bidi-class-right-to-left)
                     :arabic-letter (bidi-class-right-to-left)
                     :left-to-right (bidi-class-left-to-right)
                     :nonspacing-mark (bidi-class-left-to-right)
                     :otherwise (bidi-class-other-neutral)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-clusters-weak-classes ((clusters code-point-list-listp)
                                    (previous code-point-listp)
                                    (arabic booleanp)
                                    (ver versionp))
  :returns (classes bidi-class-listp)
  :short "The classes that the weak rules give to the code points
          of the clusters of a name, in a paragraph from left to right,
          computed without those rules, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list has one class for each code point,
     in the order of the code points:
     the class of each cluster (see @(tsee bidi-cluster-weak-class)),
     once for each code point of the cluster.
     The argument @('previous') is the cluster before the first cluster
     of the list, an empty list if there is none,
     and @('arabic') says that the last right-to-left letter
     before the first cluster is of class @('AL') (@('Arabic_Letter')).
     For a whole name, @('previous') is empty and @('arabic') is false."))
  (b* (((when (endp clusters)) nil)
       (cluster (code-point-list-fix (car clusters))))
    (append (acl2::repeat (len cluster)
                          (bidi-cluster-weak-class cluster
                                                   previous
                                                   (cadr clusters)
                                                   arabic
                                                   ver))
            (bidi-clusters-weak-classes
             (cdr clusters)
             cluster
             (bidi-arabic-after-cluster-p cluster arabic ver)
             ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here on, the events are local, except the theorem at the end.
;
; The proof.  Rule W1 gives every mark the class of the code point before it,
; so after it the classes are those of the first code points of the clusters,
; each repeated as many times as its cluster has code points (SPREAD).
; Rules W2, W3, W5, W6 and W7 go through such repetitions:
; a rule on the repeated classes gives the repetitions of what the rule
; gives on the classes themselves.  Rule W4 does not, because a separator
; that is repeated is next to another separator; W4R is rule W4
; with the numbers of the repetitions.  So the weak rules on a name
; are the weak rules, with W4R, on the classes of the first code points
; of its clusters; and those are followed rule by rule
; (G3 after W2 and W3, G4 after W4, WEAK-HEADS at the end),
; with the conditions of the wide rule where rules W5 and W7 need them.

; A list of classes in which each class is repeated a number of times.

(local
 (define spread ((ns nat-listp) (cs bidi-class-listp))
   :returns (classes bidi-class-listp)
   (if (or (endp ns)
           (endp cs))
       nil
     (append (acl2::repeat (nfix (car ns)) (bidi-class-fix (car cs)))
             (spread (cdr ns) (cdr cs))))
   :hooks nil))

(local
 (define all-pos (ns)
   :returns (yes/no booleanp)
   (or (atom ns)
       (and (posp (car ns))
            (all-pos (cdr ns))))
   :hooks nil))

(local
 (define run-induction (n)
   (if (or (zp n)
           (equal n 1))
       nil
     (run-induction (- n 1)))
   :verify-guards nil
   :hooks nil))

(defrulel repeat-of-1
  (equal (acl2::repeat 1 x)
         (list x))
  :expand (acl2::repeat 1 x))

(defruledl repeat-when-more
  (implies (and (posp n)
                (not (equal n 1)))
           (equal (acl2::repeat n x)
                  (cons x (acl2::repeat (- n 1) x))))
  :expand (acl2::repeat n x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W2.

(local
 (define w2-run-induction (n c strong)
   (if (or (zp n)
           (equal n 1))
       nil
     (w2-run-induction (- n 1)
                       c
                       (if (bidi-class-strong-p c)
                           (bidi-class-fix c)
                         (bidi-class-fix strong))))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w2-of-append-of-repeat
  (implies (posp n)
           (equal (bidi-w2 (append (acl2::repeat n c) x) strong)
                  (append (acl2::repeat n (car (bidi-w2 (list c) strong)))
                          (cdr (bidi-w2 (cons c x) strong)))))
  :induct (w2-run-induction n c strong)
  :enable (w2-run-induction
           repeat-when-more)
  :expand ((:free (a b s) (bidi-w2 (cons a b) s))
           (:free (s) (bidi-w2 nil s))))

(local
 (define w2-spread-induction (ns cs strong)
   (if (or (atom ns)
           (atom cs))
       nil
     (w2-spread-induction (cdr ns)
                          (cdr cs)
                          (if (bidi-class-strong-p (car cs))
                              (bidi-class-fix (car cs))
                            (bidi-class-fix strong))))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w2-of-spread
  (implies (all-pos ns)
           (equal (bidi-w2 (spread ns cs) strong)
                  (spread ns (bidi-w2 cs strong))))
  :induct (w2-spread-induction ns cs strong)
  :enable (w2-spread-induction
           spread
           all-pos)
  :expand ((:free (a b s) (bidi-w2 (cons a b) s))
           (:free (s) (bidi-w2 nil s))
           (bidi-w2 cs strong)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules W3 and W6.

(defrulel bidi-w3-of-append-of-repeat
  (implies (posp n)
           (equal (bidi-w3 (append (acl2::repeat n c) x))
                  (append (acl2::repeat n (car (bidi-w3 (list c))))
                          (bidi-w3 x))))
  :induct (run-induction n)
  :enable (run-induction
           repeat-when-more)
  :expand ((:free (a b) (bidi-w3 (cons a b)))
           (bidi-w3 nil)))

(defrulel bidi-w3-of-spread
  (implies (all-pos ns)
           (equal (bidi-w3 (spread ns cs))
                  (spread ns (bidi-w3 cs))))
  :induct (spread ns cs)
  :enable (spread
           all-pos)
  :expand ((:free (a b) (bidi-w3 (cons a b)))
           (bidi-w3 nil)
           (bidi-w3 cs)))

(defrulel bidi-w6-of-append-of-repeat
  (implies (posp n)
           (equal (bidi-w6 (append (acl2::repeat n c) x))
                  (append (acl2::repeat n (car (bidi-w6 (list c))))
                          (bidi-w6 x))))
  :induct (run-induction n)
  :enable (run-induction
           repeat-when-more)
  :expand ((:free (a b) (bidi-w6 (cons a b)))
           (bidi-w6 nil)))

(defrulel bidi-w6-of-spread
  (implies (all-pos ns)
           (equal (bidi-w6 (spread ns cs))
                  (spread ns (bidi-w6 cs))))
  :induct (spread ns cs)
  :enable (spread
           all-pos)
  :expand ((:free (a b) (bidi-w6 (cons a b)))
           (bidi-w6 nil)
           (bidi-w6 cs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W7.

(local
 (define w7-run-induction (n c strong)
   (if (or (zp n)
           (equal n 1))
       nil
     (w7-run-induction (- n 1)
                       c
                       (if (member-eq (bidi-class-kind c)
                                      '(:left-to-right :right-to-left))
                           (bidi-class-fix c)
                         (bidi-class-fix strong))))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w7-of-append-of-repeat
  (implies (posp n)
           (equal (bidi-w7 (append (acl2::repeat n c) x) strong)
                  (append (acl2::repeat n (car (bidi-w7 (list c) strong)))
                          (cdr (bidi-w7 (cons c x) strong)))))
  :induct (w7-run-induction n c strong)
  :enable (w7-run-induction
           repeat-when-more)
  :expand ((:free (a b s) (bidi-w7 (cons a b) s))
           (:free (s) (bidi-w7 nil s))))

(local
 (define w7-spread-induction (ns cs strong)
   (if (or (atom ns)
           (atom cs))
       nil
     (w7-spread-induction (cdr ns)
                          (cdr cs)
                          (if (member-eq (bidi-class-kind (car cs))
                                         '(:left-to-right :right-to-left))
                              (bidi-class-fix (car cs))
                            (bidi-class-fix strong))))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w7-of-spread
  (implies (all-pos ns)
           (equal (bidi-w7 (spread ns cs) strong)
                  (spread ns (bidi-w7 cs strong))))
  :induct (w7-spread-induction ns cs strong)
  :enable (w7-spread-induction
           spread
           all-pos)
  :expand ((:free (a b s) (bidi-w7 (cons a b) s))
           (:free (s) (bidi-w7 nil s))
           (bidi-w7 cs strong)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W5.

(local
 (define w5-run-induction (n c after)
   (if (or (zp n)
           (equal n 1))
       nil
     (w5-run-induction (- n 1)
                       c
                       (or (equal (bidi-class-kind c) :european-number)
                           (and after
                                (equal (bidi-class-kind c)
                                       :european-terminator)))))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w5-forward-of-append-of-repeat
  (implies (posp n)
           (equal (bidi-w5-forward (append (acl2::repeat n c) x) after)
                  (append (acl2::repeat n
                                        (car (bidi-w5-forward (list c) after)))
                          (cdr (bidi-w5-forward (cons c x) after)))))
  :induct (w5-run-induction n c after)
  :enable (w5-run-induction
           repeat-when-more)
  :expand ((:free (a b s) (bidi-w5-forward (cons a b) s))
           (:free (s) (bidi-w5-forward nil s))))

(local
 (define w5-spread-induction (ns cs after)
   (if (or (atom ns)
           (atom cs))
       nil
     (w5-spread-induction (cdr ns)
                          (cdr cs)
                          (or (equal (bidi-class-kind (car cs))
                                     :european-number)
                              (and after
                                   (equal (bidi-class-kind (car cs))
                                          :european-terminator)))))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w5-forward-of-spread
  (implies (all-pos ns)
           (equal (bidi-w5-forward (spread ns cs) after)
                  (spread ns (bidi-w5-forward cs after))))
  :induct (w5-spread-induction ns cs after)
  :enable (w5-spread-induction
           spread
           all-pos)
  :expand ((:free (a b s) (bidi-w5-forward (cons a b) s))
           (:free (s) (bidi-w5-forward nil s))
           (bidi-w5-forward cs after)))

(defrulel spread-of-append
  (implies (equal (len ns1) (len cs1))
           (equal (spread (append ns1 ns2) (append cs1 cs2))
                  (append (spread ns1 cs1)
                          (spread ns2 cs2))))
  :induct (spread ns1 cs1)
  :enable (spread len))

(defrulel all-pos-of-append
  (equal (all-pos (append x y))
         (and (all-pos x)
              (all-pos y)))
  :induct (len x)
  :enable (all-pos len))

(defrulel all-pos-of-rev
  (equal (all-pos (rev x))
         (all-pos x))
  :induct (len x)
  :enable (all-pos len rev))

(defrulel rev-of-spread
  (implies (equal (len ns) (len cs))
           (equal (rev (spread ns cs))
                  (spread (rev ns) (rev cs))))
  :induct (spread ns cs)
  :enable (spread len rev))

(defrulel bidi-w5-of-spread
  (implies (and (all-pos ns)
                (true-listp ns)
                (equal (len ns) (len cs)))
           (equal (bidi-w5 (spread ns cs))
                  (spread ns (bidi-w5 cs))))
  :enable bidi-w5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W4 does not go through the repetitions as the other rules do:
; a separator that is repeated is next to another separator.
; W4R is rule W4 with the numbers of the repetitions.

(local
 (define w4r (ns (cs bidi-class-listp) (previous bidi-class-p))
   :returns (new-cs bidi-class-listp)
   (b* (((when (or (atom ns)
                   (endp cs)))
         nil)
        (class (bidi-class-fix (car cs)))
        (previous (bidi-class-fix previous))
        (next? (and (consp (cdr cs))
                    (bidi-class-fix (cadr cs))))
        (new-class
         (cond ((not (equal (car ns) 1)) class)
               ((and (equal (bidi-class-kind class) :european-separator)
                     (equal (bidi-class-kind previous) :european-number)
                     next?
                     (equal (bidi-class-kind next?) :european-number))
                (bidi-class-european-number))
               ((and (equal (bidi-class-kind class) :common-separator)
                     (or (equal (bidi-class-kind previous) :european-number)
                         (equal (bidi-class-kind previous) :arabic-number))
                     (equal next? previous))
                previous)
               (t class))))
     (cons new-class
           (w4r (cdr ns) (cdr cs) class)))
   :verify-guards nil
   :hooks nil))

(local
 (define w4-run-induction (n c previous)
   (declare (ignorable previous))
   (if (or (zp n)
           (<= n 2))
       nil
     (w4-run-induction (- n 1) c c))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w4-of-append-of-repeat
  (implies (and (natp n)
                (<= 2 n))
           (equal (bidi-w4 (append (acl2::repeat n c) x) previous)
                  (append (acl2::repeat n (bidi-class-fix c))
                          (bidi-w4 x c))))
  :induct (w4-run-induction n c previous)
  :enable (w4-run-induction
           repeat-when-more)
  :expand ((:free (a b s) (bidi-w4 (cons a b) s))
           (:free (s) (bidi-w4 nil s))))

(defrulel bidi-w4-of-append-of-repeat-with-split
  (implies (and (posp n)
                (case-split (not (equal n 1))))
           (equal (bidi-w4 (append (acl2::repeat n c) x) previous)
                  (append (acl2::repeat n (bidi-class-fix c))
                          (bidi-w4 x c)))))

(defrulel bidi-w4-of-repeat
  (equal (bidi-w4 (acl2::repeat n c) previous)
         (acl2::repeat n (bidi-class-fix c)))
  :cases ((zp n)
          (equal n 1))
  :use (:instance bidi-w4-of-append-of-repeat (x nil))
  :disable bidi-w4-of-append-of-repeat
  :expand ((:free (a b s) (bidi-w4 (cons a b) s))
           (:free (s) (bidi-w4 nil s))
           (:free (x) (acl2::repeat n x))))

(defrulel consp-of-spread
  (implies (and (all-pos ns)
                (equal (len ns) (len cs)))
           (equal (consp (spread ns cs))
                  (consp cs)))
  :expand ((spread ns cs)
           (all-pos ns)
           (acl2::repeat (car ns) (bidi-class-fix (car cs))))
  :enable len)

(defrulel car-of-spread
  (implies (and (all-pos ns)
                (equal (len ns) (len cs))
                (consp cs))
           (equal (car (spread ns cs))
                  (bidi-class-fix (car cs))))
  :expand ((spread ns cs)
           (all-pos ns)
           (acl2::repeat (car ns) (bidi-class-fix (car cs))))
  :enable len)

(defrulel bidi-w4-of-spread
  (implies (and (all-pos ns)
                (equal (len ns) (len cs)))
           (equal (bidi-w4 (spread ns cs) previous)
                  (spread ns (w4r ns cs previous))))
  :induct (w4r ns cs previous)
  :enable (w4r
           spread
           all-pos
           len)
  :expand ((:free (a b s) (bidi-w4 (cons a b) s))
           (:free (s) (bidi-w4 nil s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The classes of a list of code points.

(local
 (define classes-of ((cps code-point-listp) (ver versionp))
   :returns (classes bidi-class-listp)
   (if (endp cps)
       nil
     (cons (code-point-bidi-class (car cps) ver)
           (classes-of (cdr cps) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-char-list-classes-of-code-points-to-bidi-chars
  (equal (bidi-char-list-classes (code-points-to-bidi-chars cps ver))
         (classes-of cps ver))
  :induct (len cps)
  :enable (len
           classes-of
           bidi-char-list-classes
           code-points-to-bidi-chars
           code-point-bidi-char))

(defrulel classes-of-of-append
  (equal (classes-of (append x y) ver)
         (append (classes-of x ver)
                 (classes-of y ver)))
  :induct (len x)
  :enable (len classes-of))

(defrulel classes-of-of-code-point-list-fix
  (equal (classes-of (code-point-list-fix cps) ver)
         (classes-of cps ver))
  :induct (len cps)
  :enable (len classes-of code-point-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The clusters of a name that the wide rule allows
; and that has a letter of class R or AL or a digit of class AN:
; each has a code point followed by marks only,
; and its first code point has no class but the nine that are left.
; In a proper cluster the first code point is not a mark.

(local
 (define cluster-ok ((cluster code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (and (consp cluster)
        (bidi-marks-p (cdr cluster) ver)
        (member-eq (bidi-class-kind (code-point-bidi-class (car cluster) ver))
                   '(:right-to-left
                     :arabic-letter
                     :arabic-number
                     :european-number
                     :european-separator
                     :common-separator
                     :european-terminator
                     :other-neutral
                     :nonspacing-mark))
        t)
   :verify-guards nil
   :hooks nil))

(local
 (define proper-ok ((clusters code-point-list-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (endp clusters)
       (and (cluster-ok (car clusters) ver)
            (not (bidi-mark-code-point-p (car (car clusters)) ver))
            (proper-ok (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

; Only the first cluster of a name can start with a mark,
; and no letter comes before it.

(local
 (define fit ((clusters code-point-list-listp) arabic (ver versionp))
   :returns (yes/no booleanp)
   (or (endp clusters)
       (and (cluster-ok (car clusters) ver)
            (or (not arabic)
                (not (bidi-mark-code-point-p (car (car clusters)) ver)))
            (proper-ok (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel fit-when-proper-ok
  (implies (proper-ok clusters ver)
           (fit clusters arabic ver))
  :enable (fit proper-ok))

(defrulel proper-ok-of-cdr-when-fit
  (implies (fit clusters arabic ver)
           (proper-ok (cdr clusters) ver))
  :enable (fit proper-ok))

(defrulel fit-of-cdr
  (implies (fit clusters arabic ver)
           (fit (cdr clusters) arabic2 ver)))

; The lengths of the clusters, and the classes of their first code points
; after rule W1 in a paragraph from left to right.

(local
 (define lens (clusters)
   :returns (ns true-listp)
   (if (atom clusters)
       nil
     (cons (len (car clusters))
           (lens (cdr clusters))))
   :verify-guards nil
   :hooks nil))

(local
 (define h1class ((cluster code-point-listp) (ver versionp))
   :returns (class bidi-class-p)
   (if (and (consp cluster)
            (not (bidi-mark-code-point-p (car cluster) ver)))
       (code-point-bidi-class (car cluster) ver)
     (bidi-class-left-to-right))
   :verify-guards nil
   :hooks nil))

(local
 (define h1 ((clusters code-point-list-listp) (ver versionp))
   :returns (cs bidi-class-listp)
   (if (endp clusters)
       nil
     (cons (h1class (car clusters) ver)
           (h1 (cdr clusters) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel len-of-lens
  (equal (len (lens clusters))
         (len clusters))
  :induct (len clusters)
  :enable (len lens))

(defrulel len-of-h1
  (equal (len (h1 clusters ver))
         (len clusters))
  :induct (len clusters)
  :enable (len h1))

(defrulel all-pos-of-lens-when-fit
  (implies (fit clusters arabic ver)
           (all-pos (lens clusters)))
  :enable (fit all-pos lens cluster-ok len)
  :prep-lemmas
  ((defrule all-pos-of-lens-when-proper-ok
     (implies (proper-ok clusters ver)
              (all-pos (lens clusters)))
     :induct (len clusters)
     :enable (proper-ok all-pos lens cluster-ok len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W1: every mark of a cluster gets the class of the first code point.

(defrulel bidi-w1-of-append-of-classes-of-marks
  (implies (and (bidi-marks-p marks ver)
                (not (bidi-class-isolate-formatting-p previous)))
           (equal (bidi-w1 (append (classes-of marks ver) x) previous)
                  (append (acl2::repeat (len marks) (bidi-class-fix previous))
                          (bidi-w1 x previous))))
  :induct (len marks)
  :enable (len
           classes-of
           bidi-mark-code-point-p
           acl2::repeat)
  :expand ((:free (a b s) (bidi-w1 (cons a b) s))))

(defrulel bidi-w1-of-append-of-classes-of-cluster
  (implies (and (cluster-ok cluster ver)
                (not (bidi-class-isolate-formatting-p previous)))
           (equal (bidi-w1 (append (classes-of cluster ver) x) previous)
                  (append (acl2::repeat
                           (len cluster)
                           (if (bidi-mark-code-point-p (car cluster) ver)
                               (bidi-class-fix previous)
                             (code-point-bidi-class (car cluster) ver)))
                          (bidi-w1 x
                                   (if (bidi-mark-code-point-p (car cluster)
                                                               ver)
                                       previous
                                     (code-point-bidi-class (car cluster)
                                                            ver))))))
  :enable (cluster-ok
           len
           bidi-mark-code-point-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           acl2::repeat)
  :expand ((classes-of cluster ver)
           (:free (a b s) (bidi-w1 (cons a b) s))))

(local
 (define w1-induction (clusters previous ver)
   (declare (ignorable previous))
   (if (atom clusters)
       nil
     (w1-induction (cdr clusters)
                   (code-point-bidi-class (car (car clusters)) ver)
                   ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w1-of-classes-of-flatten-when-proper-ok
  (implies (and (proper-ok clusters ver)
                (not (bidi-class-isolate-formatting-p previous)))
           (equal (bidi-w1 (classes-of (acl2::flatten clusters) ver) previous)
                  (spread (lens clusters) (h1 clusters ver))))
  :induct (w1-induction clusters previous ver)
  :enable (w1-induction
           proper-ok
           cluster-ok
           acl2::flatten
           lens
           h1
           h1class
           spread
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p)
  :expand ((:free (s) (bidi-w1 nil s))
           (classes-of nil ver)))

(defrulel bidi-w1-of-classes-of-flatten-when-fit
  (implies (and (fit clusters arabic ver)
                (equal previous (bidi-class-left-to-right)))
           (equal (bidi-w1 (classes-of (acl2::flatten clusters) ver) previous)
                  (spread (lens clusters) (h1 clusters ver))))
  :enable (fit
           cluster-ok
           acl2::flatten
           lens
           h1
           h1class
           spread
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p)
  :expand ((:free (s) (bidi-w1 nil s))
           (classes-of nil ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A class of a code point is one constant when its kind is known.

(defruledl code-point-bidi-class-when-european-number
  (implies (equal (bidi-class-kind (code-point-bidi-class cp ver))
                  :european-number)
           (equal (code-point-bidi-class cp ver)
                  (bidi-class-european-number)))
  :use (:instance bidi-class-fix-when-european-number
                  (x (code-point-bidi-class cp ver))))

(defruledl code-point-bidi-class-when-arabic-number
  (implies (equal (bidi-class-kind (code-point-bidi-class cp ver))
                  :arabic-number)
           (equal (code-point-bidi-class cp ver)
                  (bidi-class-arabic-number)))
  :use (:instance bidi-class-fix-when-arabic-number
                  (x (code-point-bidi-class cp ver))))

(defruledl code-point-bidi-class-when-right-to-left
  (implies (equal (bidi-class-kind (code-point-bidi-class cp ver))
                  :right-to-left)
           (equal (code-point-bidi-class cp ver)
                  (bidi-class-right-to-left)))
  :use (:instance bidi-class-fix-when-right-to-left
                  (x (code-point-bidi-class cp ver))))

(defruledl code-point-bidi-class-when-other-neutral
  (implies (equal (bidi-class-kind (code-point-bidi-class cp ver))
                  :other-neutral)
           (equal (code-point-bidi-class cp ver)
                  (bidi-class-other-neutral)))
  :use (:instance bidi-class-fix-when-other-neutral
                  (x (code-point-bidi-class cp ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules W2 and W3 on the classes of the first code points.

(local
 (define g3class ((cluster code-point-listp) arabic (ver versionp))
   :returns (class bidi-class-p)
   (b* ((class (h1class cluster ver))
        (kind (bidi-class-kind class)))
     (cond ((and arabic
                 (equal kind :european-number))
            (bidi-class-arabic-number))
           ((equal kind :arabic-letter) (bidi-class-right-to-left))
           (t class)))
   :verify-guards nil
   :hooks nil))

(local
 (define g3 ((clusters code-point-list-listp) arabic (ver versionp))
   :returns (cs bidi-class-listp)
   (if (endp clusters)
       nil
     (cons (g3class (car clusters) arabic ver)
           (g3 (cdr clusters)
               (bidi-arabic-after-cluster-p (car clusters) arabic ver)
               ver)))
   :verify-guards nil
   :hooks nil))

(defrulel len-of-g3
  (equal (len (g3 clusters arabic ver))
         (len clusters))
  :induct (g3 clusters arabic ver)
  :enable (len g3))

(local
 (define s23-induction (clusters arabic strong ver)
   (declare (ignorable arabic strong))
   (if (atom clusters)
       nil
     (s23-induction (cdr clusters)
                    (bidi-arabic-after-cluster-p (car clusters) arabic ver)
                    (if (bidi-class-strong-p (h1class (car clusters) ver))
                        (h1class (car clusters) ver)
                      (bidi-class-fix strong))
                    ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w3-of-bidi-w2-of-h1
  (implies (and (fit clusters arabic ver)
                (iff arabic
                     (equal (bidi-class-kind strong) :arabic-letter)))
           (equal (bidi-w3 (bidi-w2 (h1 clusters ver) strong))
                  (g3 clusters arabic ver)))
  :induct (s23-induction clusters arabic strong ver)
  :enable (s23-induction
           h1
           h1class
           g3
           g3class
           fit
           cluster-ok
           bidi-arabic-after-cluster-p
           bidi-class-strong-p
           bidi-mark-code-point-p)
  :expand ((:free (a b s) (bidi-w2 (cons a b) s))
           (:free (s) (bidi-w2 nil s))
           (:free (a b) (bidi-w3 (cons a b)))
           (bidi-w3 nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W4 on the classes of the first code points.

(local
 (define g4class ((cluster code-point-listp)
                  (previous code-point-listp)
                  (next code-point-listp)
                  arabic
                  (ver versionp))
   :returns (class bidi-class-p)
   (b* ((class (g3class cluster arabic ver))
        ((unless (bidi-cluster-joins-p cluster previous next arabic ver))
         class))
     (if (equal (bidi-class-kind class) :european-separator)
         (bidi-class-european-number)
       (g3class previous arabic ver)))
   :verify-guards nil
   :hooks nil))

(local
 (define g4 ((clusters code-point-list-listp)
             (previous code-point-listp)
             arabic
             (ver versionp))
   :returns (cs bidi-class-listp)
   (if (endp clusters)
       nil
     (cons (g4class (car clusters) previous (cadr clusters) arabic ver)
           (g4 (cdr clusters)
               (car clusters)
               (bidi-arabic-after-cluster-p (car clusters) arabic ver)
               ver)))
   :verify-guards nil
   :hooks nil))

(defrulel len-of-g4
  (equal (len (g4 clusters previous arabic ver))
         (len clusters))
  :induct (g4 clusters previous arabic ver)
  :enable (len g4))

(defrulel equal-of-len-and-1
  (equal (equal (len x) 1)
         (and (consp x)
              (not (consp (cdr x)))))
  :enable len)

(defrulel g3class-of-bidi-arabic-after-cluster-p
  (equal (g3class cluster
                  (bidi-arabic-after-cluster-p cluster arabic ver)
                  ver)
         (g3class cluster arabic ver))
  :enable (g3class
           h1class
           bidi-arabic-after-cluster-p))

(defrulel bidi-cluster-digit-kind-in-terms-of-g3class
  (implies (or (not (consp cluster))
               (cluster-ok cluster ver))
           (equal (bidi-cluster-digit-kind cluster arabic ver)
                  (and (member-eq (bidi-class-kind (g3class cluster arabic ver))
                                  '(:european-number :arabic-number))
                       (bidi-class-kind (g3class cluster arabic ver)))))
  :enable (g3class
           h1class
           cluster-ok
           bidi-cluster-digit-kind
           bidi-mark-code-point-p))

(defrulel consp-of-g3
  (equal (consp (g3 clusters arabic ver))
         (consp clusters))
  :expand (g3 clusters arabic ver))

(defrulel car-of-g3
  (implies (consp clusters)
           (equal (car (g3 clusters arabic ver))
                  (g3class (car clusters) arabic ver)))
  :expand (g3 clusters arabic ver))

(defrulel cdr-of-g3
  (equal (cdr (g3 clusters arabic ver))
         (g3 (cdr clusters)
             (bidi-arabic-after-cluster-p (car clusters) arabic ver)
             ver))
  :expand ((g3 clusters arabic ver)
           (:free (a) (g3 (cdr clusters) a ver))))

(defrulel consp-when-cluster-ok
  (implies (cluster-ok cluster ver)
           (consp cluster))
  :rule-classes :forward-chaining
  :enable cluster-ok)

(defrulel g3class-when-not-consp
  (implies (not (consp cluster))
           (equal (g3class cluster arabic ver)
                  (bidi-class-left-to-right)))
  :enable (g3class h1class))

(defrulel cluster-ok-of-car-when-proper-ok
  (implies (and (proper-ok clusters ver)
                (consp clusters))
           (and (cluster-ok (car clusters) ver)
                (not (bidi-mark-code-point-p (car (car clusters)) ver))))
  :expand (proper-ok clusters ver))

(defrulel bidi-arabic-after-cluster-p-when-separator
  (implies (member-eq (bidi-class-kind (g3class cluster arabic ver))
                      '(:european-separator :common-separator))
           (equal (bidi-arabic-after-cluster-p cluster arabic ver)
                  (and arabic t)))
  :enable (bidi-arabic-after-cluster-p
           g3class
           h1class
           bidi-mark-code-point-p))

(defrulel separator-kind-of-g3class
  (and (equal (equal (bidi-class-kind (g3class cluster arabic ver))
                     :common-separator)
              (and (consp cluster)
                   (equal (bidi-class-kind
                           (code-point-bidi-class (car cluster) ver))
                          :common-separator)))
       (equal (equal (bidi-class-kind (g3class cluster arabic ver))
                     :european-separator)
              (and (consp cluster)
                   (equal (bidi-class-kind
                           (code-point-bidi-class (car cluster) ver))
                          :european-separator))))
  :enable (g3class
           h1class
           bidi-mark-code-point-p))

(defrulel g3class-when-number
  (and (implies (equal (bidi-class-kind (g3class cluster arabic ver))
                       :european-number)
                (equal (g3class cluster arabic ver)
                       (bidi-class-european-number)))
       (implies (equal (bidi-class-kind (g3class cluster arabic ver))
                       :arabic-number)
                (equal (g3class cluster arabic ver)
                       (bidi-class-arabic-number))))
  :use ((:instance bidi-class-fix-when-european-number
                   (x (g3class cluster arabic ver)))
        (:instance bidi-class-fix-when-arabic-number
                   (x (g3class cluster arabic ver)))))

(local
 (define s4-induction (clusters previous arabic ver)
   (declare (ignorable previous arabic))
   (if (atom clusters)
       nil
     (s4-induction (cdr clusters)
                   (car clusters)
                   (bidi-arabic-after-cluster-p (car clusters) arabic ver)
                   ver))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel w4r-of-lens-and-g3
  (implies (and (fit clusters arabic ver)
                (booleanp arabic)
                (or (not (consp previous))
                    (cluster-ok previous ver)))
           (equal (w4r (lens clusters)
                       (g3 clusters arabic ver)
                       (g3class previous arabic ver))
                  (g4 clusters previous arabic ver)))
  :induct (s4-induction clusters previous arabic ver)
  :enable (s4-induction
           g4
           g4class
           w4r
           lens
           fit
           proper-ok
           bidi-cluster-joins-p))

(defrulel w4r-of-lens-and-g3-at-the-start
  (implies (and (fit clusters nil ver)
                (equal prevclass (bidi-class-left-to-right)))
           (equal (w4r (lens clusters) (g3 clusters nil ver) prevclass)
                  (g4 clusters nil nil ver)))
  :use (:instance w4r-of-lens-and-g3 (previous nil) (arabic nil))
  :disable w4r-of-lens-and-g3)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W5 changes nothing in a list of classes
; in which no ET is next to an EN.

(local
 (define et-en-p ((x bidi-class-listp))
   :returns (yes/no booleanp)
   (and (consp x)
        (consp (cdr x))
        (or (and (equal (bidi-class-kind (car x)) :european-terminator)
                 (equal (bidi-class-kind (cadr x)) :european-number))
            (and (equal (bidi-class-kind (car x)) :european-number)
                 (equal (bidi-class-kind (cadr x)) :european-terminator))
            (et-en-p (cdr x))))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w5-forward-when-not-et-en-p
  (implies (and (not (et-en-p x))
                (bidi-class-listp x)
                (or (not after)
                    (not (consp x))
                    (not (equal (bidi-class-kind (car x))
                                :european-terminator))))
           (equal (bidi-w5-forward x after)
                  x))
  :induct (bidi-w5-forward x after)
  :enable (bidi-w5-forward et-en-p))

(defrulel et-en-p-of-append-of-list
  (equal (et-en-p (append x (list a)))
         (or (et-en-p x)
             (and (consp x)
                  (or (and (equal (bidi-class-kind (car (rev x)))
                                  :european-terminator)
                           (equal (bidi-class-kind a) :european-number))
                      (and (equal (bidi-class-kind (car (rev x)))
                                  :european-number)
                           (equal (bidi-class-kind a)
                                  :european-terminator))))))
  :induct (len x)
  :enable (len et-en-p rev))

(defrulel et-en-p-of-rev
  (equal (et-en-p (rev x))
         (et-en-p x))
  :induct (len x)
  :enable (len et-en-p rev))

(defrulel bidi-w5-when-not-et-en-p
  (implies (and (not (et-en-p x))
                (bidi-class-listp x))
           (equal (bidi-w5 x)
                  x))
  :enable bidi-w5)

; No ET is next to an EN after rule W4
; if none is in the list of the first code points of the clusters.

(local
 (define heads-et-en ((clusters code-point-list-listp) (ver versionp))
   :returns (yes/no booleanp)
   (and (consp clusters)
        (consp (cdr clusters))
        (b* ((kind1 (bidi-class-kind
                     (code-point-bidi-class (car (car clusters)) ver)))
             (kind2 (bidi-class-kind
                     (code-point-bidi-class (car (cadr clusters)) ver))))
          (or (and (equal kind1 :european-terminator)
                   (equal kind2 :european-number))
              (and (equal kind1 :european-number)
                   (equal kind2 :european-terminator))
              (heads-et-en (cdr clusters) ver))))
   :verify-guards nil
   :hooks nil))

(defrulel consp-of-g4
  (equal (consp (g4 clusters previous arabic ver))
         (consp clusters))
  :expand (g4 clusters previous arabic ver))

(defrulel car-of-g4
  (implies (consp clusters)
           (equal (car (g4 clusters previous arabic ver))
                  (g4class (car clusters)
                           previous
                           (cadr clusters)
                           arabic
                           ver)))
  :expand (g4 clusters previous arabic ver))

(defrulel not-et-en-p-of-g4
  (implies (and (fit clusters arabic ver)
                (not (heads-et-en clusters ver)))
           (not (et-en-p (g4 clusters previous arabic ver))))
  :induct (g4 clusters previous arabic ver)
  :enable (g4
           g4class
           g3class
           h1class
           et-en-p
           heads-et-en
           fit
           cluster-ok
           bidi-cluster-joins-p
           bidi-cluster-digit-kind
           bidi-mark-code-point-p)
  :disable (bidi-cluster-digit-kind-in-terms-of-g3class
            separator-kind-of-g3class
            g3class-when-number))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W6 gives the classes of the closed form.

(local
 (define weak-heads ((clusters code-point-list-listp)
                     (previous code-point-listp)
                     arabic
                     (ver versionp))
   :returns (cs bidi-class-listp)
   (if (endp clusters)
       nil
     (cons (bidi-cluster-weak-class (car clusters)
                                    previous
                                    (cadr clusters)
                                    arabic
                                    ver)
           (weak-heads (cdr clusters)
                       (car clusters)
                       (bidi-arabic-after-cluster-p (car clusters) arabic ver)
                       ver)))
   :verify-guards nil
   :hooks nil))

(defrulel len-of-weak-heads
  (equal (len (weak-heads clusters previous arabic ver))
         (len clusters))
  :induct (weak-heads clusters previous arabic ver)
  :enable (len weak-heads))

(local
 (define w6class ((class bidi-class-p))
   :returns (new-class bidi-class-p)
   (bidi-class-case class
                    :european-separator (bidi-class-other-neutral)
                    :european-terminator (bidi-class-other-neutral)
                    :common-separator (bidi-class-other-neutral)
                    :otherwise (bidi-class-fix class))
   :hooks nil))

(defruledl bidi-w6-of-cons
  (equal (bidi-w6 (cons class classes))
         (cons (w6class class)
               (bidi-w6 classes)))
  :enable w6class
  :expand (bidi-w6 (cons class classes)))

(defrulel w6class-of-g4class
  (implies (and (cluster-ok cluster ver)
                (or (not (consp previous))
                    (cluster-ok previous ver)))
           (equal (w6class (g4class cluster previous next arabic ver))
                  (bidi-cluster-weak-class cluster previous next arabic ver)))
  :enable (w6class
           g4class
           g3class
           h1class
           cluster-ok
           bidi-cluster-weak-class
           bidi-cluster-joins-p
           bidi-cluster-digit-kind
           bidi-mark-code-point-p
           code-point-bidi-class-when-european-number
           code-point-bidi-class-when-arabic-number
           code-point-bidi-class-when-right-to-left
           code-point-bidi-class-when-other-neutral)
  :disable (bidi-cluster-digit-kind-in-terms-of-g3class
            separator-kind-of-g3class
            g3class-when-number))

(defrulel bidi-w6-of-g4
  (implies (and (fit clusters arabic ver)
                (or (not (consp previous))
                    (cluster-ok previous ver)))
           (equal (bidi-w6 (g4 clusters previous arabic ver))
                  (weak-heads clusters previous arabic ver)))
  :induct (g4 clusters previous arabic ver)
  :enable (g4
           weak-heads
           fit
           bidi-w6-of-cons)
  :expand (bidi-w6 nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W7 changes nothing in a list of classes
; in which no EN comes before the first R and no L comes after it.

(local
 (define no-l ((x bidi-class-listp))
   :returns (yes/no booleanp)
   (or (endp x)
       (and (not (equal (bidi-class-kind (car x)) :left-to-right))
            (no-l (cdr x))))
   :hooks nil))

(local
 (define w7-ok ((x bidi-class-listp))
   :returns (yes/no booleanp)
   (cond ((endp x) t)
         ((equal (bidi-class-kind (car x)) :right-to-left) (no-l (cdr x)))
         ((equal (bidi-class-kind (car x)) :european-number) nil)
         (t (w7-ok (cdr x))))
   :hooks nil))

(defrulel bidi-w7-when-no-l
  (implies (and (no-l x)
                (bidi-class-listp x)
                (not (equal (bidi-class-kind strong) :left-to-right)))
           (equal (bidi-w7 x strong)
                  x))
  :induct (bidi-w7 x strong)
  :enable (bidi-w7 no-l))

(defrulel bidi-w7-when-w7-ok
  (implies (and (w7-ok x)
                (bidi-class-listp x))
           (equal (bidi-w7 x strong)
                  x))
  :induct (bidi-w7 x strong)
  :enable (bidi-w7 w7-ok))

; The classes of the closed form are such a list
; if no digit comes before the first letter.

(local
 (define start-ok ((clusters code-point-list-listp) (ver versionp))
   :returns (yes/no booleanp)
   (b* (((when (endp clusters)) t)
        (kind (bidi-class-kind
               (code-point-bidi-class (car (car clusters)) ver))))
     (cond ((member-eq kind '(:right-to-left :arabic-letter)) t)
           ((member-eq kind '(:european-number :arabic-number)) nil)
           (t (start-ok (cdr clusters) ver))))
   :verify-guards nil
   :hooks nil))

(defrulel no-l-of-weak-heads-when-proper-ok
  (implies (proper-ok clusters ver)
           (no-l (weak-heads clusters previous arabic ver)))
  :induct (weak-heads clusters previous arabic ver)
  :enable (weak-heads
           no-l
           proper-ok
           cluster-ok
           bidi-cluster-weak-class
           bidi-mark-code-point-p))

(defrulel w7-ok-of-weak-heads
  (implies (and (fit clusters arabic ver)
                (start-ok clusters ver)
                (not (bidi-cluster-digit-kind previous arabic ver)))
           (w7-ok (weak-heads clusters previous arabic ver)))
  :induct (weak-heads clusters previous arabic ver)
  :enable (weak-heads
           w7-ok
           start-ok
           fit
           cluster-ok
           bidi-cluster-weak-class
           bidi-cluster-joins-p
           bidi-cluster-digit-kind)
  :disable bidi-cluster-digit-kind-in-terms-of-g3class)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The weak rules on the clusters.

(defrulel bidi-clusters-weak-classes-in-terms-of-weak-heads
  (equal (bidi-clusters-weak-classes clusters previous arabic ver)
         (spread (lens clusters)
                 (weak-heads clusters previous arabic ver)))
  :induct (weak-heads clusters previous arabic ver)
  :enable (weak-heads
           bidi-clusters-weak-classes
           spread
           lens))

(defrulel bidi-resolve-weak-types-of-classes-of-flatten
  (implies (and (fit clusters nil ver)
                (start-ok clusters ver)
                (not (heads-et-en clusters ver)))
           (equal (bidi-resolve-weak-types
                   (classes-of (acl2::flatten clusters) ver)
                   (bidi-class-left-to-right))
                  (bidi-clusters-weak-classes clusters nil nil ver)))
  :enable bidi-resolve-weak-types)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The clusters of a name that the wide rule allows
; and that has a letter of class R or AL or a digit of class AN.

(defrulel flatten-of-bidi-clusters
  (equal (acl2::flatten (bidi-clusters cps ver))
         (code-point-list-fix cps))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           acl2::flatten
           code-point-list-fix)
  :expand (acl2::flatten (bidi-clusters (cdr cps) ver)))

(defrulel consp-of-bidi-clusters
  (equal (consp (bidi-clusters cps ver))
         (consp cps))
  :expand (bidi-clusters cps ver))

(defrulel bidi-clusters-when-not-consp
  (implies (not (consp cps))
           (equal (bidi-clusters cps ver)
                  nil))
  :expand (bidi-clusters cps ver))

(defrulel car-of-car-of-bidi-clusters
  (implies (consp cps)
           (equal (car (car (bidi-clusters cps ver)))
                  (code-point-fix (car cps))))
  :expand (bidi-clusters cps ver))

; The code points of such a name.

(local
 (define cps-ok ((cps code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (endp cps)
       (and (member-eq (bidi-class-kind (code-point-bidi-class (car cps) ver))
                       '(:right-to-left
                         :arabic-letter
                         :arabic-number
                         :european-number
                         :european-separator
                         :common-separator
                         :european-terminator
                         :other-neutral
                         :nonspacing-mark))
            (cps-ok (cdr cps) ver)))
   :hooks nil))

(defrulel cps-ok-when-wide-and-not-left-to-right
  (implies (and (bidi-rule-wide-code-points-p cps ver)
                (not (bidi-class-kind-present-p :left-to-right cps ver)))
           (cps-ok cps ver))
  :induct (len cps)
  :enable (len
           cps-ok
           bidi-rule-wide-code-point-p
           bidi-class-kind-present-p))

(defrulel shape-of-bidi-clusters-when-cps-ok
  (implies (cps-ok cps ver)
           (and (proper-ok (cdr (bidi-clusters cps ver)) ver)
                (implies (consp cps)
                         (cluster-ok (car (bidi-clusters cps ver)) ver))))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           cps-ok
           proper-ok
           cluster-ok
           bidi-mark-code-point-p))

(defrulel fit-of-bidi-clusters-when-cps-ok
  (implies (cps-ok cps ver)
           (fit (bidi-clusters cps ver) nil ver))
  :enable fit
  :cases ((consp cps)))

; No digit comes before the first letter.

(defrulel start-ok-of-bidi-clusters
  (implies (bidi-rule-wide-start-p cps ver)
           (start-ok (bidi-clusters cps ver) ver))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-rule-wide-start-p
           start-ok
           bidi-mark-code-point-p)
  :expand ((start-ok (bidi-clusters (cdr cps) ver) ver)))

; No ET is next to an EN in the list of the first code points.

(local
 (define heads ((clusters code-point-list-listp))
   :returns (cps code-point-listp)
   (if (endp clusters)
       nil
     (cons (code-point-fix (car (car clusters)))
           (heads (cdr clusters))))
   :verify-guards nil
   :hooks nil))

(defrulel heads-of-bidi-clusters
  (implies (consp cps)
           (equal (heads (bidi-clusters cps ver))
                  (cons (code-point-fix (car cps))
                        (bidi-drop-marks (cdr cps) ver))))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           heads
           bidi-drop-marks)
  :expand ((heads (bidi-clusters (cdr cps) ver))))

(defrulel heads-et-en-in-terms-of-heads
  (equal (heads-et-en clusters ver)
         (bidi-terminator-next-to-digit-p (heads clusters) ver))
  :induct (len clusters)
  :enable (len
           heads-et-en
           heads
           bidi-terminator-next-to-digit-p))

(defrulel not-heads-et-en-of-bidi-clusters
  (implies (not (bidi-terminator-next-to-digit-p (bidi-drop-marks cps ver)
                                                 ver))
           (not (heads-et-en (bidi-clusters cps ver) ver)))
  :cases ((consp cps))
  :enable bidi-mark-code-point-p
  :expand ((bidi-drop-marks cps ver)
           (:free (a b) (bidi-terminator-next-to-digit-p (cons a b) ver))
           (bidi-terminator-next-to-digit-p nil ver)
           (heads nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-display-weak-theorem
  :short "Theorem that the weak rules give the classes
          of @(tsee bidi-clusters-weak-classes)
          to a name that satisfies the wide rule
          and has a right-to-left letter or an Arabic digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classes of the name are those of the list
     that @(tsee code-points-to-bidi-chars) gives,
     and @('sos') is the direction at the start of the sequence,
     which is @('L') (@('Left_To_Right'))
     in a paragraph from left to right.
     The rule is disabled by default."))

  (defruled bidi-resolve-weak-types-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name ver)
                  (bidi-right-to-left-label-p name ver)
                  (equal (bidi-class-kind sos) :left-to-right))
             (equal (bidi-resolve-weak-types
                     (bidi-char-list-classes
                      (code-points-to-bidi-chars name ver))
                     sos)
                    (bidi-clusters-weak-classes (bidi-clusters name ver)
                                                nil
                                                nil
                                                ver)))
    :enable (bidi-rule-wide-p
             bidi-class-fix-when-left-to-right)
    :use ((:instance bidi-resolve-weak-types-of-classes-of-flatten
                     (clusters (bidi-clusters name ver)))
          (:instance bidi-resolve-weak-types-of-bidi-class-fix-sos
                     (classes (classes-of name ver))))
    :disable (bidi-resolve-weak-types-of-classes-of-flatten
              bidi-resolve-weak-types-of-bidi-class-fix-sos
              bidi-class-fix-under-bidi-class-equiv
              bidi-clusters-weak-classes-in-terms-of-weak-heads
              heads-et-en-in-terms-of-heads)))
