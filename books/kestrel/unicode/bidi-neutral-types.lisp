; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-characters")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp))) ; for the types with fields of naturals

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-neutral-types
  :parents (bidirectional-algorithm)
  :short "Resolving the neutral and isolate formatting types:
          bracket pairs and rules N0 to N2
          of the Unicode Bidirectional Algorithm."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules [UAX #9, Section 3.3.5] work on
     one isolating run sequence at a time,
     after the rules for the weak types (see @(see bidi-weak-types)).
     They give a direction, @('L') or @('R'),
     to the characters that have none of their own:
     the neutral characters and the isolate formatting characters,
     which the specification calls NI together
     (see @(tsee bidi-class-neutral-or-isolate-p)).
     Such a character takes the direction of the text around it
     if the text on both sides has the same direction,
     and the direction of the embedding level otherwise.
     In these rules a number, @('EN') or @('AN'),
     counts as a character of direction @('R')
     (see @(tsee bidi-class-direction)).")
   (xdoc::p
    "Rule N0 comes first and treats brackets:
     the two brackets of a bracket pair get the same direction,
     which depends on what is between them and on what comes before.
     The bracket pairs of a sequence are found as [UAX #9, BD16] says,
     with a stack of at most 63 opening brackets.")
   (xdoc::p
    "A position in an isolating run sequence
     is the number of characters of the sequence before it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bracket-pair
  :short "Fixtype of bracket pairs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A bracket pair is given by the positions,
     in an isolating run sequence,
     of its opening bracket and of its closing bracket
     [UAX #9, BD16]."))
  ((open nat)
   (close nat))
  :pred bracket-pair-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bracket-pair-list
  :short "Fixtype of lists of bracket pairs."
  :elt-type bracket-pair
  :true-listp t
  :elementp-of-nil nil
  :pred bracket-pair-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod open-bracket
  :short "Fixtype of elements of the stack that finds the bracket pairs."
  :long
  (xdoc::topstring
   (xdoc::p
    "An element is for an opening bracket
     whose closing bracket has not been found yet:
     the identifier of the bracket (see @(tsee bidi-bracket-role))
     and its position [UAX #9, BD16]."))
  ((id code-point)
   (position nat))
  :pred open-bracket-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist open-bracket-list
  :short "Fixtype of stacks of opening brackets."
  :elt-type open-bracket
  :true-listp t
  :elementp-of-nil nil
  :pred open-bracket-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define open-bracket-stack-find ((stack open-bracket-listp)
                                 (id code-point-p))
  :returns (mv (found booleanp)
               (position natp :rule-classes (:rewrite :type-prescription))
               (rest open-bracket-listp))
  :short "Find the opening bracket that a closing bracket goes with."
  :long
  (xdoc::topstring
   (xdoc::p
    "The stack is searched from the top
     for an opening bracket with the identifier of the closing bracket
     [UAX #9, BD16].
     If there is one, the results are @('t'),
     the position of the first one found,
     and the stack under that element:
     the elements above it are for opening brackets
     that now cannot be paired.
     If there is none, the first result is @('nil')."))
  (b* (((when (endp stack)) (mv nil 0 nil))
       ((open-bracket top) (car stack))
       ((when (equal top.id (code-point-fix id)))
        (mv t top.position (open-bracket-list-fix (cdr stack)))))
    (open-bracket-stack-find (cdr stack) id))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-current-bracket-roles ((classes bidi-class-listp)
                                    (roles bidi-bracket-role-listp))
  :returns (new-roles bidi-bracket-role-listp)
  :short "The roles in bracket pairs that the characters of
          an isolating run sequence have for rule N0."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the classes of the characters of the sequence,
     as they are after rules W1 to W7,
     and the roles that their properties give them.
     A character is an opening or a closing paired bracket
     for the algorithm only if its class is, at this point,
     @('ON') (Other Neutral) [UAX #9, BD14 and BD15]:
     an override may have changed it.
     So a character whose class is not @('ON') gets the role @(':none')."))
  (b* (((when (or (endp classes)
                  (endp roles)))
        nil))
    (cons (if (equal (bidi-class-kind (car classes)) :other-neutral)
              (bidi-bracket-role-fix (car roles))
            (bidi-bracket-role-none))
          (bidi-current-bracket-roles (cdr classes) (cdr roles))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-bracket-pairs-from ((roles bidi-bracket-role-listp)
                                 (position natp)
                                 (stack open-bracket-listp))
  :returns (mv (overflow booleanp)
               (pairs bracket-pair-listp))
  :short "Find the bracket pairs of the rest of an isolating run sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the roles in bracket pairs
     of the characters from a position on
     (see @(tsee bidi-current-bracket-roles)),
     that position, and the stack.")
   (xdoc::p
    "An opening bracket is pushed on the stack.
     If the stack already has 63 elements,
     the search stops and the first result is @('t'):
     the sequence then has no bracket pairs at all.
     A closing bracket is paired with the nearest opening bracket
     on the stack that has its identifier, if there is one
     (see @(tsee open-bracket-stack-find)).
     The pairs are in the order of their closing brackets."))
  (b* (((when (endp roles)) (mv nil nil))
       (position (lnfix position))
       (role (bidi-bracket-role-fix (car roles))))
    (bidi-bracket-role-case
     role
     :none (bidi-bracket-pairs-from (cdr roles) (+ 1 position) stack)
     :open (if (>= (len stack) 63)
               (mv t nil)
             (bidi-bracket-pairs-from
              (cdr roles)
              (+ 1 position)
              (cons (make-open-bracket :id role.id :position position)
                    (open-bracket-list-fix stack))))
     :close (b* (((mv found open rest)
                  (open-bracket-stack-find stack role.id))
                 ((unless found)
                  (bidi-bracket-pairs-from (cdr roles) (+ 1 position) stack))
                 ((mv overflow pairs)
                  (bidi-bracket-pairs-from (cdr roles) (+ 1 position) rest)))
              (mv overflow
                  (cons (make-bracket-pair :open open :close position)
                        pairs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bracket-pair-insert ((pair bracket-pair-p)
                             (pairs bracket-pair-listp))
  :returns (new-pairs bracket-pair-listp)
  :short "Insert a bracket pair into a list of bracket pairs
          that is in the order of the opening brackets."
  (b* (((when (endp pairs)) (list (bracket-pair-fix pair)))
       ((when (<= (bracket-pair->open pair)
                  (bracket-pair->open (car pairs))))
        (cons (bracket-pair-fix pair)
              (bracket-pair-list-fix pairs))))
    (cons (bracket-pair-fix (car pairs))
          (bracket-pair-insert pair (cdr pairs))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bracket-pairs-sort ((pairs bracket-pair-listp))
  :returns (new-pairs bracket-pair-listp)
  :short "Put a list of bracket pairs in the order of the opening brackets."
  (if (endp pairs)
      nil
    (bracket-pair-insert (car pairs)
                         (bracket-pairs-sort (cdr pairs))))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-bracket-pairs ((classes bidi-class-listp)
                            (roles bidi-bracket-role-listp))
  :returns (pairs bracket-pair-listp)
  :short "The bracket pairs of an isolating run sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the classes of the characters of the sequence,
     as they are after rules W1 to W7,
     and their roles in bracket pairs.
     The result is the list of the bracket pairs,
     in the order of the positions of their opening brackets
     [UAX #9, BD16].
     It is empty if the sequence has more than 63 opening brackets
     waiting for their closing brackets at some point."))
  (b* (((mv overflow pairs)
        (bidi-bracket-pairs-from (bidi-current-bracket-roles classes roles)
                                 0
                                 nil)))
    (if overflow
        nil
      (bracket-pairs-sort pairs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-n0-strong-inside-p ((classes bidi-class-listp)
                                 (position natp)
                                 (pair bracket-pair-p)
                                 (direction bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a character of a given direction
          is inside a bracket pair."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first two arguments are the classes of the characters
     from a position on, and that position: 0 at first.
     The characters inside the pair are those
     after the opening bracket and before the closing bracket.
     Numbers count as @('R') (see @(tsee bidi-class-direction))."))
  (b* (((when (endp classes)) nil)
       (position (lnfix position))
       ((bracket-pair pair))
       ((when (>= position pair.close)) nil)
       ((when (and (> position pair.open)
                   (equal (bidi-class-direction (car classes))
                          (bidi-class-fix direction))))
        t))
    (bidi-n0-strong-inside-p (cdr classes) (+ 1 position) pair direction))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-n0-context ((classes bidi-class-listp)
                         (count natp)
                         (direction bidi-class-p))
  :returns (context bidi-class-p)
  :short "The direction of the last character with a direction
          before an opening bracket."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first two arguments are the classes of the characters
     from some position on,
     and the number of them that are before the opening bracket.
     The third is the direction found so far:
     @('sos') at first, which is the result
     if no character before the bracket has a direction
     [UAX #9, rule N0].
     Numbers count as @('R')."))
  (b* ((count (lnfix count))
       ((when (or (equal count 0)
                  (endp classes)))
        (bidi-class-fix direction)))
    (bidi-n0-context (cdr classes)
                     (- count 1)
                     (or (bidi-class-direction (car classes))
                         direction)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-starts-with-mark-p ((classes bidi-class-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of bidirectional classes
          starts with the class of the nonspacing marks."
  (and (consp classes)
       (equal (bidi-class-kind (car classes)) :nonspacing-mark))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-n0-set-pair ((classes bidi-class-listp)
                          (originals bidi-class-listp)
                          (position natp)
                          (pair bracket-pair-p)
                          (direction bidi-class-p)
                          (after-bracket booleanp))
  :returns (new-classes bidi-class-listp)
  :short "Give a direction to the two brackets of a bracket pair,
          and to the nonspacing marks that follow each of them."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first three arguments are the classes of the characters
     from a position on,
     the classes that the same characters had before rule W1,
     and that position: 0 at first.
     The two brackets of the pair get the direction.
     So does every character that was a nonspacing mark before rule W1
     and that comes right after one of the two brackets,
     or after such a mark [UAX #9, rule N0].
     The last argument says whether the character before the list
     is one of the brackets or such a mark."))
  (b* (((when (endp classes)) nil)
       (position (lnfix position))
       (originals (bidi-class-list-fix originals))
       ((bracket-pair pair))
       (bracket (or (equal position pair.open)
                    (equal position pair.close)))
       (mark (and after-bracket
                  (bidi-starts-with-mark-p originals))))
    (cons (if (or bracket mark)
              (bidi-class-fix direction)
            (bidi-class-fix (car classes)))
          (bidi-n0-set-pair (cdr classes)
                            (cdr originals)
                            (+ 1 position)
                            pair
                            direction
                            (or bracket mark))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-n0-set-pair
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len))))

  ;; This is the theorem that the fixing of the position needs;
  ;; it follows from the definition without induction.

  (defrule bidi-n0-set-pair-of-nfix-position-by-definition
    (equal (bidi-n0-set-pair classes
                             originals
                             (nfix position)
                             pair
                             direction
                             after-bracket)
           (bidi-n0-set-pair classes
                             originals
                             position
                             pair
                             direction
                             after-bracket))
    :expand ((bidi-n0-set-pair classes
                               originals
                               (nfix position)
                               pair
                               direction
                               after-bracket)
             (bidi-n0-set-pair classes
                               originals
                               position
                               pair
                               direction
                               after-bracket))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-n0-pair ((classes bidi-class-listp)
                      (originals bidi-class-listp)
                      (pair bracket-pair-p)
                      (sos bidi-class-p)
                      (embedding bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule N0 for one bracket pair."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last argument is the embedding direction:
     the direction of the level of the sequence, @('L') or @('R').")
   (xdoc::ul
    (xdoc::li
     "If a character inside the pair has the embedding direction,
      the two brackets get the embedding direction.")
    (xdoc::li
     "Otherwise, if a character inside the pair
      has the opposite direction,
      the last character with a direction before the opening bracket
      decides, or @('sos') if there is none:
      if it has the opposite direction too,
      the two brackets get the opposite direction,
      and otherwise the embedding direction.")
    (xdoc::li
     "Otherwise no character inside the pair has a direction,
      and the brackets are left for rules N1 and N2."))
   (xdoc::p
    "This is [UAX #9, rule N0].
     The classes are those that the characters have at this point:
     an earlier bracket pair may have given a direction
     to a bracket that is inside this one."))
  (b* ((embedding (bidi-class-fix embedding))
       (opposite (if (equal (bidi-class-kind embedding) :left-to-right)
                     (bidi-class-right-to-left)
                   (bidi-class-left-to-right)))
       ((when (bidi-n0-strong-inside-p classes 0 pair embedding))
        (bidi-n0-set-pair classes originals 0 pair embedding nil))
       ((unless (bidi-n0-strong-inside-p classes 0 pair opposite))
        (bidi-class-list-fix classes))
       (context (bidi-n0-context classes (bracket-pair->open pair) sos)))
    (bidi-n0-set-pair classes
                      originals
                      0
                      pair
                      (if (equal context opposite)
                          opposite
                        embedding)
                      nil))
  :hooks (:fix)

  ///

  (defret len-of-bidi-n0-pair
    (equal (len new-classes)
           (len classes))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-n0-pairs ((classes bidi-class-listp)
                       (originals bidi-class-listp)
                       (pairs bracket-pair-listp)
                       (sos bidi-class-p)
                       (embedding bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule N0 for a list of bracket pairs, one after the other."
  (if (endp pairs)
      (bidi-class-list-fix classes)
    (bidi-n0-pairs (bidi-n0-pair classes originals (car pairs) sos embedding)
                   originals
                   (cdr pairs)
                   sos
                   embedding))
  :hooks (:fix)

  ///

  (defret len-of-bidi-n0-pairs
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-n0 ((classes bidi-class-listp)
                 (originals bidi-class-listp)
                 (roles bidi-bracket-role-listp)
                 (sos bidi-class-p)
                 (embedding bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule N0: the bracket pairs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The bracket pairs of the sequence (see @(tsee bidi-bracket-pairs))
     are treated in the order of their opening brackets
     (see @(tsee bidi-n0-pair)) [UAX #9, rule N0].
     The arguments are the classes of the characters of the sequence
     after rules W1 to W7, their classes before rule W1,
     their roles in bracket pairs, @('sos'),
     and the embedding direction."))
  (bidi-n0-pairs classes
                 originals
                 (bidi-bracket-pairs classes roles)
                 sos
                 embedding)
  :hooks (:fix)

  ///

  (defret len-of-bidi-n0
    (equal (len new-classes)
           (len classes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-neutral-run-end ((classes bidi-class-listp)
                              (eos bidi-class-p))
  :returns (direction? bidi-class-option-p)
  :short "The direction of the first character after
          the neutral and isolate formatting characters
          at the front of a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the list has only such characters,
     the result is @('eos'), for end of sequence,
     which is @('L') or @('R') [UAX #9, rule X10].
     Numbers count as @('R')."))
  (b* (((when (endp classes)) (bidi-class-fix eos))
       ((when (bidi-class-neutral-or-isolate-p (car classes)))
        (bidi-neutral-run-end (cdr classes) eos)))
    (bidi-class-direction (car classes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-n1-n2 ((classes bidi-class-listp)
                    (previous? bidi-class-option-p)
                    (eos bidi-class-p)
                    (embedding bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rules N1 and N2: the neutral and isolate formatting characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "A sequence of neutral and isolate formatting characters
     takes the direction of the characters on its two sides
     if they have the same direction [UAX #9, rule N1],
     and the embedding direction otherwise [UAX #9, rule N2].
     Numbers count as @('R').
     At the start of the isolating run sequence,
     the direction on the left is @('sos'),
     and at its end the direction on the right is @('eos').")
   (xdoc::p
    "The second argument is the direction
     of the character before the list
     that is not neutral or isolate formatting,
     or @('sos') if there is none;
     at first it is @('sos')."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (previous? (bidi-class-option-fix previous?))
       ((unless (bidi-class-neutral-or-isolate-p class))
        (cons class
              (bidi-n1-n2 (cdr classes)
                          (bidi-class-direction class)
                          eos
                          embedding)))
       (next? (bidi-neutral-run-end classes eos)))
    (cons (if (and previous?
                   (equal previous? next?))
              previous?
            (bidi-class-fix embedding))
          (bidi-n1-n2 (cdr classes) previous? eos embedding)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-n1-n2
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-resolve-neutral-types ((classes bidi-class-listp)
                                    (originals bidi-class-listp)
                                    (roles bidi-bracket-role-listp)
                                    (sos bidi-class-p)
                                    (eos bidi-class-p)
                                    (embedding bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rules N0 to N2, in that order, on one isolating run sequence."
  (bidi-n1-n2 (bidi-n0 classes originals roles sos embedding)
              (bidi-class-fix sos)
              eos
              embedding)
  :hooks (:fix)

  ///

  (defret len-of-bidi-resolve-neutral-types
    (equal (len new-classes)
           (len classes))))
