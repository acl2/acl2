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
(include-book "bidi-resolved-levels")
(include-book "bidi-display")

(local (include-book "bidi-guarded-plain"))
(local (include-book "bidi-guarded-brackets"))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable fix nfix)))

; The classes are kept as they are written.

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
                           bidi-class-fix-when-pop-directional-isolate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book proves that the Unicode Bidirectional Algorithm [UAX #9]
; gives level 2 to every character of a left-to-right label
; that satisfies the strict rule (BIDI-RULE-STRICT-P),
; in a paragraph from right to left.  The theorem is at the end;
; every other event is local.
;
; The outline of the proof.  Such a label is plain text
; (theorem BIDI-PARAGRAPH-ALL-LEVELS-WHEN-PLAIN-AT-LEVEL): it is one sequence
; at level 1, with the direction R at its two ends.
;
; 1. The classes of the label are L, EN, ES, CS, ON and NSM (C0-P);
;    the first is L, and the last that is not NSM is L or EN (END-P).
;    Rule W1 gives each NSM the class before it, so the classes
;    are then L, EN, ES, CS and ON (C1-P) and the last is L or EN.
;    Rules W2, W3 and W5 change nothing: there is no AL and no ET.
;    Rule W4 changes some ES and CS to EN, and rule W6 the others to ON.
;    Rule W7 changes every EN to L, because the first class is L
;    and there is no R.  So the classes are L and ON (C7-P),
;    and the first and the last are L (LL-P).
; 2. Rule N0 changes some ON to L and nothing else:
;    no class R, AN or EN is inside a pair, and the strong class
;    before a pair is L, because the pair opens after the first class.
; 3. Rule N1 gives L to every ON, which is between two L.
;    So every level is 2 [UAX #9, rule I2], and rule L1 changes nothing.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The predicates of the proof, on bidirectional classes.

(local
 (define c0-p ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :left-to-right t
                    :european-number t
                    :european-separator t
                    :common-separator t
                    :other-neutral t
                    :nonspacing-mark t
                    :otherwise nil)
   :hooks (:fix)))

(local
 (define c1-p ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :left-to-right t
                    :european-number t
                    :european-separator t
                    :common-separator t
                    :other-neutral t
                    :otherwise nil)
   :hooks (:fix)))

(local
 (define c6-p ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :left-to-right t
                    :european-number t
                    :other-neutral t
                    :otherwise nil)
   :hooks (:fix)))

(local
 (define c7-p ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :left-to-right t
                    :other-neutral t
                    :otherwise nil)
   :hooks (:fix)))

(local
 (std::deflist c0-list-p (x)
   :guard (bidi-class-listp x)
   (c0-p x)))

(local
 (std::deflist c1-list-p (x)
   :guard (bidi-class-listp x)
   (c1-p x)))

(local
 (std::deflist c6-list-p (x)
   :guard (bidi-class-listp x)
   (c6-p x)))

(local
 (std::deflist c7-list-p (x)
   :guard (bidi-class-listp x)
   (c7-p x)))

; The last class is L or EN; the last class is L.

(local
 (define l-or-en-p (class)
   :returns (yes/no booleanp)
   (and (member-eq (bidi-class-kind class)
                   '(:left-to-right :european-number))
        t)
   :verify-guards nil
   :hooks nil))

(local
 (define last-l-en-p (x)
   :returns (yes/no booleanp)
   (and (consp x)
        (if (consp (cdr x))
            (last-l-en-p (cdr x))
          (l-or-en-p (car x))))
   :verify-guards nil
   :hooks nil))

(local
 (define last-l-p (x)
   :returns (yes/no booleanp)
   (and (consp x)
        (if (consp (cdr x))
            (last-l-p (cdr x))
          (equal (bidi-class-kind (car x)) :left-to-right)))
   :verify-guards nil
   :hooks nil))

; Only NSM; the last class that is not NSM is L or EN.

(local
 (define marks-p (x)
   :returns (yes/no booleanp)
   (or (atom x)
       (and (equal (bidi-class-kind (car x)) :nonspacing-mark)
            (marks-p (cdr x))))
   :verify-guards nil
   :hooks nil))

(local
 (define end-p (x)
   :returns (yes/no booleanp)
   (and (consp x)
        (or (end-p (cdr x))
            (and (l-or-en-p (car x))
                 (marks-p (cdr x)))))
   :verify-guards nil
   :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W1.

(defrulel c1-list-p-of-bidi-w1
  (implies (and (c0-list-p x)
                (c1-p previous))
           (c1-list-p (bidi-w1 x previous)))
  :induct (bidi-w1 x previous)
  :enable (bidi-w1
           c0-p
           c1-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel c1-list-p-of-bidi-w1-when-first-is-left-to-right
  (implies (and (c0-list-p x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (c1-list-p (bidi-w1 x previous)))
  :expand (bidi-w1 x previous)
  :enable c1-p)

(defrulel kind-of-car-of-bidi-w1
  (implies (and (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (equal (bidi-class-kind (car (bidi-w1 x previous)))
                  :left-to-right))
  :expand (bidi-w1 x previous))

(defrulel consp-of-bidi-w1
  (equal (consp (bidi-w1 x previous))
         (consp x))
  :expand (bidi-w1 x previous))

(defrulel last-l-en-p-of-bidi-w1-of-marks
  (implies (and (marks-p x)
                (consp x)
                (l-or-en-p previous))
           (last-l-en-p (bidi-w1 x previous)))
  :induct (bidi-w1 x previous)
  :enable (bidi-w1
           marks-p
           last-l-en-p
           l-or-en-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel last-l-en-p-of-bidi-w1
  (implies (end-p x)
           (last-l-en-p (bidi-w1 x previous)))
  :induct (bidi-w1 x previous)
  :enable (bidi-w1
           end-p
           last-l-en-p
           l-or-en-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules W2 and W3: there is no AL.

(defrulel bidi-w2-when-c1-list-p
  (implies (and (c1-list-p x)
                (bidi-class-listp x)
                (not (equal (bidi-class-kind strong) :arabic-letter)))
           (equal (bidi-w2 x strong)
                  x))
  :induct (bidi-w2 x strong)
  :enable (bidi-w2
           c1-p
           bidi-class-strong-p))

(defrulel bidi-w3-when-c1-list-p
  (implies (and (c1-list-p x)
                (bidi-class-listp x))
           (equal (bidi-w3 x)
                  x))
  :induct (bidi-w3 x)
  :enable (bidi-w3 c1-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W4.

(defrulel c1-list-p-of-bidi-w4
  (implies (and (c1-list-p x)
                (not (equal (bidi-class-kind previous) :arabic-number)))
           (c1-list-p (bidi-w4 x previous)))
  :induct (bidi-w4 x previous)
  :enable (bidi-w4 c1-p))

(defrulel kind-of-car-of-bidi-w4
  (implies (and (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (equal (bidi-class-kind (car (bidi-w4 x previous)))
                  :left-to-right))
  :expand (bidi-w4 x previous))

(defrulel consp-of-bidi-w4
  (equal (consp (bidi-w4 x previous))
         (consp x))
  :expand (bidi-w4 x previous))

(defrulel last-l-en-p-of-bidi-w4
  (implies (last-l-en-p x)
           (last-l-en-p (bidi-w4 x previous)))
  :induct (bidi-w4 x previous)
  :enable (bidi-w4
           last-l-en-p
           l-or-en-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W5: there is no ET.

(defrulel bidi-w5-forward-when-c1-list-p
  (implies (and (c1-list-p x)
                (bidi-class-listp x))
           (equal (bidi-w5-forward x after)
                  x))
  :induct (bidi-w5-forward x after)
  :enable (bidi-w5-forward c1-p))

(defrulel bidi-w5-when-c1-list-p
  (implies (and (c1-list-p x)
                (bidi-class-listp x))
           (equal (bidi-w5 x)
                  x))
  :enable bidi-w5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W6.

(defrulel c6-list-p-of-bidi-w6
  (implies (c1-list-p x)
           (c6-list-p (bidi-w6 x)))
  :induct (bidi-w6 x)
  :enable (bidi-w6 c1-p c6-p))

(defrulel kind-of-car-of-bidi-w6
  (implies (and (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (equal (bidi-class-kind (car (bidi-w6 x)))
                  :left-to-right))
  :expand (bidi-w6 x))

(defrulel consp-of-bidi-w6
  (equal (consp (bidi-w6 x))
         (consp x))
  :expand (bidi-w6 x))

(defrulel last-l-en-p-of-bidi-w6
  (implies (last-l-en-p x)
           (last-l-en-p (bidi-w6 x)))
  :induct (bidi-w6 x)
  :enable (bidi-w6
           last-l-en-p
           l-or-en-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W7: every EN becomes L,
; first when the last strong class is L and then when the first class is L.

(defrulel c7-list-p-of-bidi-w7
  (implies (and (c6-list-p x)
                (equal (bidi-class-kind strong) :left-to-right))
           (c7-list-p (bidi-w7 x strong)))
  :induct (bidi-w7 x strong)
  :enable (bidi-w7 c6-p c7-p))

(defrulel consp-of-bidi-w7
  (equal (consp (bidi-w7 x strong))
         (consp x))
  :expand (bidi-w7 x strong))

(defrulel last-l-p-of-bidi-w7
  (implies (and (c6-list-p x)
                (last-l-en-p x)
                (equal (bidi-class-kind strong) :left-to-right))
           (last-l-p (bidi-w7 x strong)))
  :induct (bidi-w7 x strong)
  :enable (bidi-w7
           c6-p
           last-l-en-p
           last-l-p
           l-or-en-p))

(defrulel c7-list-p-of-bidi-w7-when-first-is-left-to-right
  (implies (and (c6-list-p x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (c7-list-p (bidi-w7 x strong)))
  :expand (bidi-w7 x strong)
  :enable c7-p)

(defrulel last-l-p-of-bidi-w7-when-first-is-left-to-right
  (implies (and (c6-list-p x)
                (last-l-en-p x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (last-l-p (bidi-w7 x strong)))
  :expand ((bidi-w7 x strong)
           (last-l-en-p x))
  :enable last-l-p)

(defrulel kind-of-car-of-bidi-w7
  (implies (and (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right))
           (equal (bidi-class-kind (car (bidi-w7 x strong)))
                  :left-to-right))
  :expand (bidi-w7 x strong))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; After the weak rules: only L and ON, and L at the two ends.

(local
 (define ll-p (x)
   :returns (yes/no booleanp)
   (and (c7-list-p x)
        (consp x)
        (equal (bidi-class-kind (car x)) :left-to-right)
        (last-l-p x))
   :verify-guards nil
   :hooks nil))

(defrulel ll-p-of-bidi-resolve-weak-types
  (implies (and (c0-list-p x)
                (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right)
                (end-p x)
                (equal (bidi-class-kind sos) :right-to-left))
           (ll-p (bidi-resolve-weak-types x sos)))
  :enable (bidi-resolve-weak-types
           ll-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0.  No class R, AN or EN is inside a pair.

(defrulel not-bidi-n0-strong-inside-p-when-c7-list-p
  (implies (and (c7-list-p x)
                (equal direction (bidi-class-right-to-left)))
           (not (bidi-n0-strong-inside-p x position pair direction)))
  :induct (bidi-n0-strong-inside-p x position pair direction)
  :enable (bidi-n0-strong-inside-p
           c7-p
           bidi-class-direction))

; The strong class before a pair that opens after the first class is L.

(defrulel bidi-n0-context-when-c7-list-p
  (implies (and (c7-list-p x)
                (equal direction (bidi-class-left-to-right)))
           (equal (bidi-n0-context x count direction)
                  (bidi-class-left-to-right)))
  :induct (bidi-n0-context x count direction)
  :enable (bidi-n0-context
           c7-p
           bidi-class-direction))

(defrulel bidi-n0-context-when-first-is-left-to-right
  (implies (and (c7-list-p x)
                (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right)
                (posp count))
           (equal (bidi-n0-context x count direction)
                  (bidi-class-left-to-right)))
  :expand (bidi-n0-context x count direction)
  :enable bidi-class-direction)

; Setting the brackets of a pair to L.

(defrulel c7-list-p-of-bidi-n0-set-pair
  (implies (and (c7-list-p x)
                (equal (bidi-class-kind direction) :left-to-right))
           (c7-list-p (bidi-n0-set-pair x
                                        originals
                                        position
                                        pair
                                        direction
                                        after)))
  :induct (bidi-n0-set-pair x originals position pair direction after)
  :enable (bidi-n0-set-pair c7-p))

(defrulel consp-of-bidi-n0-set-pair
  (equal (consp (bidi-n0-set-pair x originals position pair direction after))
         (consp x))
  :expand (bidi-n0-set-pair x originals position pair direction after))

(defrulel kind-of-car-of-bidi-n0-set-pair
  (implies (and (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right)
                (equal (bidi-class-kind direction) :left-to-right))
           (equal (bidi-class-kind
                   (car (bidi-n0-set-pair x
                                          originals
                                          position
                                          pair
                                          direction
                                          after)))
                  :left-to-right))
  :expand (bidi-n0-set-pair x originals position pair direction after))

(defrulel last-l-p-of-bidi-n0-set-pair
  (implies (and (last-l-p x)
                (equal (bidi-class-kind direction) :left-to-right))
           (last-l-p (bidi-n0-set-pair x
                                       originals
                                       position
                                       pair
                                       direction
                                       after)))
  :induct (bidi-n0-set-pair x originals position pair direction after)
  :enable (bidi-n0-set-pair last-l-p))

; Leaving a pair as it is.

(defrulel c7-list-p-of-bidi-class-list-fix
  (implies (c7-list-p x)
           (c7-list-p (bidi-class-list-fix x)))
  :induct (len x)
  :enable (len bidi-class-list-fix))

(defrulel last-l-p-of-bidi-class-list-fix
  (implies (last-l-p x)
           (last-l-p (bidi-class-list-fix x)))
  :induct (len x)
  :enable (len bidi-class-list-fix last-l-p))

(defrulel kind-of-car-of-bidi-class-list-fix
  (implies (consp x)
           (equal (bidi-class-kind (car (bidi-class-list-fix x)))
                  (bidi-class-kind (car x))))
  :expand (bidi-class-list-fix x))

(defrulel ll-p-of-bidi-class-list-fix
  (implies (ll-p x)
           (ll-p (bidi-class-list-fix x)))
  :enable ll-p)

; One pair, then all the pairs.

(defrulel ll-p-of-bidi-n0-pair
  (implies (and (ll-p cur)
                (< 0 (bracket-pair->open pair))
                (equal embedding (bidi-class-right-to-left)))
           (ll-p (bidi-n0-pair cur originals pair sos embedding)))
  :enable (bidi-n0-pair ll-p))

(local
 (define opens-ok (pairs)
   :returns (yes/no booleanp)
   (or (atom pairs)
       (and (< 0 (bracket-pair->open (car pairs)))
            (opens-ok (cdr pairs))))
   :verify-guards nil
   :hooks nil))

(defrulel ll-p-of-bidi-n0-pairs
  (implies (and (ll-p cur)
                (opens-ok pairs)
                (equal embedding (bidi-class-right-to-left)))
           (ll-p (bidi-n0-pairs cur originals pairs sos embedding)))
  :induct (bidi-n0-pairs cur originals pairs sos embedding)
  :enable (bidi-n0-pairs opens-ok))

; No pair opens at the first class, which is L: a pair opens at a class ON.

(defrulel opens-ok-when-bidi-pairs-sound-p
  (implies (and (bidi-pairs-sound-p pairs classes roles)
                (equal (bidi-class-kind (car classes)) :left-to-right))
           (opens-ok pairs))
  :induct (len pairs)
  :enable (len
           bidi-pairs-sound-p
           bidi-pair-sound-p
           opens-ok
           nth))

(defrulel opens-ok-of-bidi-bracket-pairs-when-ll-p
  (implies (ll-p classes)
           (opens-ok (bidi-bracket-pairs classes roles)))
  :enable ll-p
  :disable opens-ok-when-bidi-pairs-sound-p
  :use (:instance opens-ok-when-bidi-pairs-sound-p
                  (pairs (bidi-bracket-pairs classes roles))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N1: every ON is between two L.
; First when the class before the list is L.

(defrulel bidi-neutral-run-end-when-ends-with-left-to-right
  (implies (and (c7-list-p x)
                (last-l-p x))
           (equal (bidi-neutral-run-end x eos)
                  (bidi-class-left-to-right)))
  :induct (len x)
  :enable (len
           c7-p
           last-l-p
           bidi-neutral-run-end
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction))

(defrulel bidi-n1-n2-when-ends-with-left-to-right
  (implies (and (c7-list-p x)
                (or (atom x)
                    (last-l-p x))
                (equal previous (bidi-class-left-to-right)))
           (equal (bidi-n1-n2 x previous eos embedding)
                  (acl2::repeat (len x) (bidi-class-left-to-right))))
  :induct (len x)
  :enable (len
           c7-p
           last-l-p
           acl2::repeat
           bidi-class-fix-when-left-to-right
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((:free (p s e) (bidi-n1-n2 x p s e))))

; The class before the list does not matter, because the first class is L.

(defrulel bidi-n1-n2-when-ll-p
  (implies (ll-p x)
           (equal (bidi-n1-n2 x previous eos embedding)
                  (acl2::repeat (len x) (bidi-class-left-to-right))))
  :enable (ll-p
           len
           acl2::repeat
           bidi-class-fix-when-left-to-right
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction)
  :expand ((bidi-n1-n2 x previous eos embedding)
           (last-l-p x)))

; The implicit levels at level 1: 2 for the class L.

(defrulel bidi-implicit-levels-of-repeat-of-left-to-right-at-level-1
  (implies (and (equal class (bidi-class-left-to-right))
                (equal level 1))
           (equal (bidi-implicit-levels (acl2::repeat n class) level)
                  (acl2::repeat n 2)))
  :induct (acl2::repeat n class)
  :enable (acl2::repeat
           bidi-implicit-level)
  :expand ((:free (a b) (bidi-implicit-levels (cons a b) 1))
           (bidi-implicit-levels nil 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The levels of the one isolating run sequence.

(defrulel bidi-resolve-sequence-when-left-to-right-label
  (implies (and (c0-list-p x)
                (consp x)
                (equal (bidi-class-kind (car x)) :left-to-right)
                (end-p x)
                (equal sos (bidi-class-right-to-left))
                (equal eos (bidi-class-right-to-left))
                (equal level 1))
           (equal (bidi-resolve-sequence x roles sos eos level)
                  (acl2::repeat (len x) 2)))
  :enable (bidi-resolve-sequence
           bidi-resolve-neutral-types
           bidi-n0
           bidi-level-direction))

; Rule L1 changes no level: there is no separator, no white space,
; and no character that rule X9 removes.

(local
 (define two-lists-induction (x y)
   (if (or (atom x)
           (atom y))
       nil
     (two-lists-induction (cdr x) (cdr y)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-reset-all-levels-when-c0-list-p
  (implies (and (c0-list-p classes)
                (nat-listp levels)
                (equal (len levels) (len classes)))
           (equal (mv-nth 0 (bidi-reset-all-levels classes
                                                   levels
                                                   paragraph-level))
                  levels))
  :induct (two-lists-induction classes levels)
  :enable (two-lists-induction
           bidi-reset-all-levels
           c0-p
           len
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel bidi-plain-class-listp-when-c0-list-p
  (implies (c0-list-p x)
           (bidi-plain-class-listp x))
  :induct (len x)
  :enable (len
           c0-p
           bidi-plain-class-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel nat-listp-of-repeat-of-2
  (nat-listp (acl2::repeat n 2))
  :induct (acl2::repeat n 2)
  :enable acl2::repeat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The classes of a label.

(local
 (define classes-of (cps ver)
   :returns (classes bidi-class-listp)
   (if (atom cps)
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

(defrulel len-of-classes-of
  (equal (len (classes-of cps ver))
         (len cps))
  :induct (len cps)
  :enable (len classes-of))

(defrulel consp-of-classes-of
  (equal (consp (classes-of cps ver))
         (consp cps))
  :expand (classes-of cps ver))

(defrulel car-of-classes-of
  (implies (consp cps)
           (equal (car (classes-of cps ver))
                  (code-point-bidi-class (car cps) ver)))
  :expand (classes-of cps ver))

(defrulel c0-list-p-of-classes-of
  (implies (and (bidi-rule-left-to-right-code-points-p label ver)
                (not (bidi-class-kind-present-p :european-terminator
                                                label
                                                ver))
                (not (bidi-class-kind-present-p :boundary-neutral
                                                label
                                                ver)))
           (c0-list-p (classes-of label ver)))
  :induct (len label)
  :enable (len
           classes-of
           c0-p
           bidi-rule-left-to-right-code-point-p
           bidi-class-kind-present-p))

(defrulel marks-p-of-classes-of
  (implies (bidi-marks-p cps ver)
           (marks-p (classes-of cps ver)))
  :induct (len cps)
  :enable (len
           classes-of
           marks-p
           bidi-mark-code-point-p))

(defrulel end-p-of-classes-of
  (implies (bidi-rule-left-to-right-end-p label ver)
           (end-p (classes-of label ver)))
  :induct (len label)
  :enable (len
           classes-of
           end-p
           l-or-en-p
           bidi-rule-left-to-right-end-p))

; What the Bidi Rule says of a label whose first class is L.

(defrulel left-to-right-label-when-bidi-rule-p
  (implies (and (bidi-rule-p label ver)
                (equal (bidi-class-kind
                        (code-point-bidi-class (car label) ver))
                       :left-to-right))
           (and (consp label)
                (bidi-rule-left-to-right-code-points-p label ver)
                (bidi-rule-left-to-right-end-p label ver)))
  :rule-classes :forward-chaining
  :enable bidi-rule-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-left-to-right-label
  :parents (bidi-rule-display)
  :short "Theorem that the Unicode Bidirectional Algorithm,
          in a paragraph from right to left,
          gives level 2 to every character of a left-to-right label
          that satisfies the strict rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second argument of @(tsee bidi-paragraph-all-levels)
     is the paragraph embedding level,
     which is 1 in a paragraph from right to left.
     The label is the whole paragraph.
     It satisfies @(tsee bidi-rule-strict-p),
     the strict rule derived from the Bidi Rule (see @(see bidi-rule)),
     and is not a right-to-left label
     (see @(tsee bidi-right-to-left-label-p)),
     so its first character is of class @('L') (@('Left_To_Right'))
     and it has no character of class
     @('R') (@('Right_To_Left')), @('AL') (@('Arabic_Letter')),
     @('AN') (@('Arabic_Number')), @('ET') (@('European_Terminator'))
     or @('BN') (@('Boundary_Neutral')).")
   (xdoc::p
    "The proof follows the algorithm rule by rule.
     Each mark takes the class of the character before it
     [UAX #9, rule W1].
     Each digit of class @('EN') (@('European_Number'))
     becomes @('L'), because the first character is of class @('L')
     and there is no @('R') [UAX #9, rule W7].
     The classes are then @('L') and @('ON') (@('Other_Neutral')),
     with @('L') first and last:
     the Bidi Rule asks that the last character that is not a mark
     be of class @('L') or @('EN').
     Rule N0 changes some brackets to @('L'),
     and rule N1 gives @('L') to each @('ON') that is left,
     since it is between two @('L').
     A character of class @('L') at the odd level 1 gets level 2
     [UAX #9, rule I2].
     Since no level is odd, the label is displayed as it is stored
     (see @(see bidi-display-even-levels-theorem)).
     The rule is disabled by default."))

  (defruled bidi-paragraph-all-levels-at-level-1-when-left-to-right-label
    (implies (and (bidi-rule-strict-p label ver)
                  (not (bidi-right-to-left-label-p label ver)))
             (equal (bidi-paragraph-all-levels
                     (code-points-to-bidi-chars label ver)
                     1)
                    (acl2::repeat (len label) 2)))
    :enable (bidi-paragraph-all-levels-when-plain-at-level
             bidi-rule-strict-p
             bidi-level-direction)))
