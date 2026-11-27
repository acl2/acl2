; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rearrangement")
(include-book "bidi-display")
(include-book "right-to-left-free")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-left-to-right
  :parents (bidirectional-algorithm)
  :short "Text without right-to-left characters
          is displayed in the order in which it is stored."
  :long
  (xdoc::topstring
   (xdoc::p
    "Take a text that has no character of the six bidirectional classes
     @('R'), @('AL'), @('AN'), @('RLE'), @('RLO') and @('RLI')
     (see @(tsee right-to-left-code-point-p)),
     in paragraphs from left to right,
     or whose direction is found by rules P2 and P3.
     Then the Unicode Bidirectional Algorithm [UAX #9]
     gives every character an even level,
     and the order of display is the order of the text.
     This is the theorem
     @('bidi-display-order-when-right-to-left-free-p').
     The whole text as it is displayed (see @(tsee bidi-display))
     is then the text as it is stored.
     This is the theorem
     @('bidi-display-when-right-to-left-free-p').")
   (xdoc::p
    "None of the six classes can be left out of the condition:
     for each of them, the tests of this library have a text
     with a character of that class, and of none of the other five,
     that is displayed in another order.
     In particular the two classes @('R') and @('AL') are not enough,
     because the Arabic-Indic digits, of class @('AN'),
     and the three formatting characters reorder text by themselves.")
   (xdoc::p
    "The proof follows the algorithm rule by rule.
     Without the three formatting classes,
     every level on the stack of rules X1 to X8 is even
     and no override is from right to left.
     Without @('R'), @('AL') and @('AN'),
     the rules for the weak types bring in none of them,
     and rule W7 turns every European number into @('L'),
     because the start of each sequence counts as @('L').
     Then no class counts as @('R') in rules N0 to N2,
     which therefore give the direction @('L')
     to every bracket and neutral character.
     So rules I1 and I2 leave every level as it is, even,
     and rule L2 has nothing to reverse."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-level-option-even-p ((level? acl2::maybe-natp))
  :returns (yes/no booleanp)
  :short "Check if an optional level is not an odd level."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds of an even level,
     which is a level of text from left to right,
     and of @('nil'), which stands for a character
     that has no level because rule X9 removes it."))
  (b* ((level? (acl2::maybe-natp-fix level?)))
    (or (not level?)
        (evenp level?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-levels-even-p (x)
  :guard (bidi-level-option-listp x)
  :short "Check that a list of optional levels has no odd level."
  :long
  (xdoc::topstring
   (xdoc::p
    "When this holds of the resolved levels of a text,
     rule L2 reverses nothing
     and the text is displayed in the order in which it is stored:
     see the theorem
     @('bidi-order-of-levels-when-bidi-levels-even-p')."))
  (bidi-level-option-even-p x)
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here to the last section, the events are local:
; they are the steps of the proof.

; Facts of arithmetic for the proofs of this book.

(defrulel fix-of-nfix
  (equal (fix (nfix x))
         (nfix x))
  :enable (fix nfix))

(defrulel evenp-of-+-of-2
  (implies (and (natp x)
                (evenp x))
           (evenp (+ 2 x)))
  :enable (evenp natp))

(defrulel evenp-of-max
  (implies (and (evenp x)
                (evenp y))
           (evenp (max x y)))
  :enable max)

(defrulel evenp-of-nfix-when-evenp
  (implies (evenp x)
           (evenp (nfix x)))
  :enable nfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The predicates of the proof, on bidirectional classes.
; SOURCE-CLASS-OK is for the classes of the characters of the text:
; none of the six classes that can turn the direction around.
; CLASS-OK is for the classes during the rules for the weak types:
; no R, no AL and no AN.
; RESOLVED-CLASS-OK is for the classes after rule W7:
; no EN either, so that no class counts as R in rules N0 to N2.

(local
 (define source-class-ok ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :right-to-left nil
                    :arabic-letter nil
                    :arabic-number nil
                    :right-to-left-embedding nil
                    :right-to-left-override nil
                    :right-to-left-isolate nil
                    :otherwise t)
   :hooks (:fix)))

(local
 (define class-ok ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :right-to-left nil
                    :arabic-letter nil
                    :arabic-number nil
                    :otherwise t)
   :hooks (:fix)))

(local
 (define resolved-class-ok ((class bidi-class-p))
   :returns (yes/no booleanp)
   (bidi-class-case class
                    :right-to-left nil
                    :arabic-letter nil
                    :arabic-number nil
                    :european-number nil
                    :otherwise t)
   :hooks (:fix)))

(local
 (std::deflist source-classes-ok (x)
   :guard (bidi-class-listp x)
   (source-class-ok x)))

(local
 (std::deflist classes-ok (x)
   :guard (bidi-class-listp x)
   (class-ok x)))

(local
 (std::deflist resolved-classes-ok (x)
   :guard (bidi-class-listp x)
   (resolved-class-ok x)))

(local
 (std::deflist levels-ok (x)
   :guard (nat-listp x)
   (evenp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules P2 and P3: without R and AL, the level found is 0.

(defrulel bidi-first-strong-when-source-classes-ok
  (implies (and (source-classes-ok classes)
                (natp depth)
                (bidi-first-strong classes depth in-isolate))
           (equal (bidi-class-kind
                   (bidi-first-strong classes depth in-isolate))
                  :left-to-right))
  :induct (bidi-first-strong classes depth in-isolate)
  :enable (bidi-first-strong
           source-class-ok
           bidi-class-strong-p
           natp
           nfix))

(defrulel bidi-first-strong-level-when-source-classes-ok
  (implies (source-classes-ok classes)
           (equal (bidi-first-strong-level classes in-isolate)
                  0))
  :enable (bidi-first-strong-level
           bidi-class-right-to-left-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules X1 to X8: the levels of the stack stay even
; and no override is from right to left.

(local
 (define status-ok ((status directional-status-p))
   :returns (yes/no booleanp)
   (and (evenp (directional-status->level status))
        (not (equal (directional-override-kind
                     (directional-status->override status))
                    :right-to-left)))
   :hooks (:fix)))

(local
 (std::deflist statuses-ok (x)
   :guard (directional-status-listp x)
   (status-ok x)))

(defrulel statuses-ok-of-directional-status-list-fix
  (equal (statuses-ok (directional-status-list-fix x))
         (statuses-ok x))
  :induct t
  :enable directional-status-list-fix)

(local
 (define state-ok ((st explicit-state-p))
   :returns (yes/no booleanp)
   (and (status-ok (explicit-state->top st))
        (statuses-ok (explicit-state->below st)))
   :hooks nil))

(defrulel state-ok-of-explicit-state-fix
  (equal (state-ok (explicit-state-fix st))
         (state-ok st))
  :enable state-ok)

(defrulel state-ok-of-explicit-state-enter-embedding
  (implies (and (state-ok st)
                (not (equal (directional-override-kind override)
                            :right-to-left)))
           (state-ok (explicit-state-enter-embedding st nil override)))
  :enable (state-ok
           status-ok
           explicit-state-enter-embedding
           least-greater-level))

(defrulel state-ok-of-explicit-state-enter-isolate
  (implies (state-ok st)
           (state-ok (explicit-state-enter-isolate st nil)))
  :enable (state-ok
           status-ok
           explicit-state-enter-isolate
           least-greater-level))

(defrulel status-ok-of-directional-status-pop-to-isolate
  (implies (and (status-ok top)
                (statuses-ok below))
           (and (status-ok
                 (mv-nth 0 (directional-status-pop-to-isolate top below)))
                (statuses-ok
                 (mv-nth 1 (directional-status-pop-to-isolate top below)))))
  :induct (directional-status-pop-to-isolate top below)
  :enable directional-status-pop-to-isolate)

(defrulel state-ok-of-explicit-state-leave-isolate
  (implies (state-ok st)
           (state-ok (explicit-state-leave-isolate st)))
  :enable (state-ok
           explicit-state-leave-isolate))

(defrulel state-ok-of-explicit-state-leave-embedding
  (implies (state-ok st)
           (state-ok (explicit-state-leave-embedding st)))
  :enable (state-ok
           explicit-state-leave-embedding))

(defrulel class-ok-of-apply-directional-override
  (implies (and (class-ok class)
                (not (equal (directional-override-kind override)
                            :right-to-left)))
           (class-ok (apply-directional-override class override)))
  :enable (apply-directional-override
           class-ok))

(defrulel class-ok-when-source-class-ok
  (implies (source-class-ok class)
           (class-ok class))
  :enable (source-class-ok class-ok))

(defrulel evenp-of-level-of-top-when-state-ok
  (implies (state-ok st)
           (evenp (directional-status->level (explicit-state->top st))))
  :enable (state-ok status-ok))

(defrulel directional-override-kind-of-top-when-state-ok
  (implies (state-ok st)
           (not (equal (directional-override-kind
                        (directional-status->override
                         (explicit-state->top st)))
                       :right-to-left)))
  :enable (state-ok status-ok))

(defrulel bidi-explicit-step-when-ok
  (implies (and (source-class-ok class)
                (source-classes-ok rest)
                (state-ok st)
                (evenp (nfix paragraph-level)))
           (b* (((mv level new-class new-st)
                 (bidi-explicit-step class rest st paragraph-level)))
             (and (evenp level)
                  (class-ok new-class)
                  (state-ok new-st))))
  :enable (bidi-explicit-step
           source-class-ok)
  :expand ((state-ok st)
           (state-ok (explicit-state-leave-isolate st))
           (status-ok (explicit-state->top st))
           (status-ok (explicit-state->top
                       (explicit-state-leave-isolate st)))))

(defrulel bidi-explicit-levels-from-when-ok
  (implies (and (source-classes-ok classes)
                (state-ok st)
                (evenp (nfix paragraph-level)))
           (b* (((mv levels new-classes)
                 (bidi-explicit-levels-from classes st paragraph-level)))
             (and (levels-ok levels)
                  (classes-ok new-classes))))
  :induct (bidi-explicit-levels-from classes st paragraph-level)
  :enable bidi-explicit-levels-from)

(defrulel bidi-explicit-levels-when-ok
  (implies (and (source-classes-ok classes)
                (evenp (nfix paragraph-level)))
           (b* (((mv levels new-classes)
                 (bidi-explicit-levels classes paragraph-level)))
             (and (levels-ok levels)
                  (classes-ok new-classes))))
  :enable (bidi-explicit-levels
           state-ok
           status-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules W1 to W7: they bring in no R, no AL and no AN,
; and with sos = L rule W7 turns every EN into L.

(defrulel classes-ok-of-bidi-w1
  (implies (and (classes-ok classes)
                (class-ok previous))
           (classes-ok (bidi-w1 classes previous)))
  :induct (bidi-w1 classes previous)
  :enable (bidi-w1 class-ok))

(defrulel classes-ok-of-bidi-w2
  (implies (and (classes-ok classes)
                (not (equal (bidi-class-kind strong) :arabic-letter)))
           (classes-ok (bidi-w2 classes strong)))
  :induct (bidi-w2 classes strong)
  :enable (bidi-w2 class-ok bidi-class-strong-p)
  :disable (bidi-class-fix-when-left-to-right
            bidi-class-fix-when-right-to-left
            bidi-class-fix-when-arabic-letter))

(defrulel classes-ok-of-bidi-w3
  (implies (classes-ok classes)
           (classes-ok (bidi-w3 classes)))
  :induct (bidi-w3 classes)
  :enable (bidi-w3 class-ok))

(defrulel classes-ok-of-bidi-w4
  (implies (and (classes-ok classes)
                (class-ok previous))
           (classes-ok (bidi-w4 classes previous)))
  :induct (bidi-w4 classes previous)
  :enable (bidi-w4 class-ok))

(defrulel classes-ok-of-bidi-w5-forward
  (implies (classes-ok classes)
           (classes-ok (bidi-w5-forward classes after-number)))
  :induct (bidi-w5-forward classes after-number)
  :enable (bidi-w5-forward class-ok))

(defrulel classes-ok-of-bidi-w5
  (implies (classes-ok classes)
           (classes-ok (bidi-w5 classes)))
  :enable bidi-w5)

(defrulel classes-ok-of-bidi-w6
  (implies (classes-ok classes)
           (classes-ok (bidi-w6 classes)))
  :induct (bidi-w6 classes)
  :enable (bidi-w6 class-ok))

(defrulel resolved-classes-ok-of-bidi-w7
  (implies (and (classes-ok classes)
                (equal (bidi-class-kind strong) :left-to-right))
           (resolved-classes-ok (bidi-w7 classes strong)))
  :induct (bidi-w7 classes strong)
  :enable (bidi-w7 class-ok resolved-class-ok)
  :disable (bidi-class-fix-when-left-to-right
            bidi-class-fix-when-right-to-left))

(defrulel resolved-classes-ok-of-bidi-resolve-weak-types
  (implies (and (classes-ok classes)
                (equal (bidi-class-kind sos) :left-to-right))
           (resolved-classes-ok (bidi-resolve-weak-types classes sos)))
  :enable (bidi-resolve-weak-types class-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules N0 to N2: with sos = L and the embedding direction L,
; and no class that counts as R, they bring in only L.

(defrulel resolved-classes-ok-of-bidi-class-list-fix
  (implies (resolved-classes-ok x)
           (resolved-classes-ok (bidi-class-list-fix x)))
  :induct t
  :enable bidi-class-list-fix)

(defrulel resolved-classes-ok-of-bidi-n0-set-pair
  (implies (and (resolved-classes-ok classes)
                (resolved-class-ok direction))
           (resolved-classes-ok
            (bidi-n0-set-pair classes
                              originals
                              position
                              pair
                              direction
                              after-bracket)))
  :induct (bidi-n0-set-pair classes
                            originals
                            position
                            pair
                            direction
                            after-bracket)
  :enable bidi-n0-set-pair)

(defrulel resolved-class-ok-of-bidi-n0-context
  (implies (and (resolved-classes-ok classes)
                (resolved-class-ok direction))
           (resolved-class-ok (bidi-n0-context classes count direction)))
  :induct (bidi-n0-context classes count direction)
  :enable (bidi-n0-context
           bidi-class-direction
           resolved-class-ok))

(defrulel resolved-classes-ok-of-bidi-n0-pair
  (implies (and (resolved-classes-ok classes)
                (equal (bidi-class-kind sos) :left-to-right)
                (equal (bidi-class-kind embedding) :left-to-right))
           (resolved-classes-ok
            (bidi-n0-pair classes originals pair sos embedding)))
  :enable (bidi-n0-pair resolved-class-ok)
  :use (:instance resolved-class-ok-of-bidi-n0-context
                  (count (bracket-pair->open pair))
                  (direction sos))
  :disable resolved-class-ok-of-bidi-n0-context)

(defrulel resolved-classes-ok-of-bidi-n0-pairs
  (implies (and (resolved-classes-ok classes)
                (equal (bidi-class-kind sos) :left-to-right)
                (equal (bidi-class-kind embedding) :left-to-right))
           (resolved-classes-ok
            (bidi-n0-pairs classes originals pairs sos embedding)))
  :induct (bidi-n0-pairs classes originals pairs sos embedding)
  :enable bidi-n0-pairs)

(defrulel bidi-class-kind-of-bidi-class-option-fix
  (implies x
           (equal (bidi-class-kind (bidi-class-option-fix x))
                  (bidi-class-kind x)))
  :enable bidi-class-option-fix)

(defrulel resolved-classes-ok-of-bidi-n1-n2
  (implies (and (resolved-classes-ok classes)
                (or (not previous?)
                    (resolved-class-ok previous?))
                (equal (bidi-class-kind embedding) :left-to-right))
           (resolved-classes-ok
            (bidi-n1-n2 classes previous? eos embedding)))
  :induct (bidi-n1-n2 classes previous? eos embedding)
  :enable (bidi-n1-n2
           bidi-class-direction
           resolved-class-ok))

(defrulel resolved-classes-ok-of-bidi-resolve-neutral-types
  (implies (and (resolved-classes-ok classes)
                (equal (bidi-class-kind sos) :left-to-right)
                (equal (bidi-class-kind embedding) :left-to-right))
           (resolved-classes-ok
            (bidi-resolve-neutral-types classes
                                        originals
                                        roles
                                        sos
                                        eos
                                        embedding)))
  :enable (bidi-resolve-neutral-types
           bidi-n0
           resolved-class-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules I1 and I2, and one isolating run sequence:
; at an even level, a class that is not R, AN or EN keeps the level.

(defrulel evenp-of-bidi-implicit-level
  (implies (and (resolved-class-ok class)
                (evenp (nfix level)))
           (evenp (bidi-implicit-level class level)))
  :enable (bidi-implicit-level resolved-class-ok))

(defrulel levels-ok-of-bidi-implicit-levels
  (implies (and (resolved-classes-ok classes)
                (evenp (nfix level)))
           (levels-ok (bidi-implicit-levels classes level)))
  :induct (bidi-implicit-levels classes level)
  :enable bidi-implicit-levels)

(defrulel bidi-level-direction-when-evenp
  (implies (evenp (nfix level))
           (equal (bidi-class-kind (bidi-level-direction level))
                  :left-to-right))
  :enable bidi-level-direction)

(defrulel levels-ok-of-bidi-resolve-sequence
  (implies (and (classes-ok classes)
                (equal (bidi-class-kind sos) :left-to-right)
                (evenp (nfix level)))
           (levels-ok (bidi-resolve-sequence classes roles sos eos level)))
  :enable bidi-resolve-sequence)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The characters with their explicit levels: rule X9,
; and the characters of a sequence.

(local
 (define lchar-ok ((lchar bidi-leveled-char-p))
   :returns (yes/no booleanp)
   (and (evenp (bidi-leveled-char->level lchar))
        (class-ok (bidi-leveled-char->class lchar)))
   :hooks (:fix)))

(local
 (std::deflist lchars-ok (x)
   :guard (bidi-leveled-char-listp x)
   (lchar-ok x)))

(defrulel lchars-ok-of-bidi-leveled-chars
  (implies (and (levels-ok levels)
                (classes-ok classes))
           (lchars-ok (bidi-leveled-chars chars levels classes)))
  :induct (bidi-leveled-chars chars levels classes)
  :enable (bidi-leveled-chars lchar-ok))

(defrulel lchars-ok-of-bidi-remove-by-x9
  (implies (lchars-ok lchars)
           (lchars-ok (bidi-remove-by-x9 lchars)))
  :induct (bidi-remove-by-x9 lchars)
  :enable bidi-remove-by-x9)

(defrulel lchar-ok-of-bidi-leveled-char-at
  (implies (lchars-ok lchars)
           (lchar-ok (bidi-leveled-char-at position lchars)))
  :induct (bidi-leveled-char-at position lchars)
  :enable (bidi-leveled-char-at lchar-ok class-ok))

(defrulel evenp-of-level-of-bidi-leveled-char-at
  (implies (lchars-ok lchars)
           (evenp (bidi-leveled-char->level
                   (bidi-leveled-char-at position lchars))))
  :induct (bidi-leveled-char-at position lchars)
  :enable (bidi-leveled-char-at lchar-ok))

(defrulel lchars-ok-of-bidi-leveled-chars-at
  (implies (lchars-ok lchars)
           (lchars-ok (bidi-leveled-chars-at positions lchars)))
  :induct (bidi-leveled-chars-at positions lchars)
  :enable bidi-leveled-chars-at)

(defrulel classes-ok-of-bidi-leveled-char-list-classes
  (implies (lchars-ok lchars)
           (classes-ok (bidi-leveled-char-list-classes lchars)))
  :induct (bidi-leveled-char-list-classes lchars)
  :enable (bidi-leveled-char-list-classes lchar-ok))

(defrulel levels-ok-of-bidi-leveled-char-list-levels
  (implies (lchars-ok lchars)
           (levels-ok (bidi-leveled-char-list-levels lchars)))
  :induct (bidi-leveled-char-list-levels lchars)
  :enable (bidi-leveled-char-list-levels lchar-ok))

(defrulel evenp-of-bidi-level-at
  (implies (and (lchars-ok lchars)
                (evenp (nfix paragraph-level)))
           (evenp (bidi-level-at position lchars paragraph-level)))
  :enable bidi-level-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule X10: every isolating run sequence, and all of them.

(defrulel bidi-level-direction-of-max-when-evenp
  (implies (and (natp x)
                (natp y)
                (evenp x)
                (evenp y))
           (equal (bidi-class-kind (bidi-level-direction (max x y)))
                  :left-to-right))
  :enable (bidi-level-direction max nfix natp))

(defrulel levels-ok-of-bidi-resolve-sequence-at
  (implies (and (lchars-ok lchars)
                (evenp (nfix paragraph-level)))
           (levels-ok
            (bidi-resolve-sequence-at positions lchars paragraph-level)))
  :enable bidi-resolve-sequence-at
  :disable max)

(defrulel levels-ok-of-nat-list-fix
  (implies (levels-ok x)
           (levels-ok (nat-list-fix x)))
  :induct t
  :enable nat-list-fix)

(defrulel levels-ok-of-nat-list-set
  (implies (and (levels-ok list)
                (evenp (nfix value)))
           (levels-ok (nat-list-set position value list)))
  :induct (nat-list-set position value list)
  :enable nat-list-set)

(defrulel levels-ok-of-nat-list-set-list
  (implies (and (levels-ok list)
                (levels-ok values))
           (levels-ok (nat-list-set-list positions values list)))
  :induct (nat-list-set-list positions values list)
  :enable nat-list-set-list)

(defrulel levels-ok-of-bidi-resolve-sequences-from
  (implies (and (lchars-ok lchars)
                (evenp (nfix paragraph-level))
                (levels-ok levels))
           (levels-ok (bidi-resolve-sequences-from position
                                                   lchars
                                                   paragraph-level
                                                   levels)))
  :induct (bidi-resolve-sequences-from position
                                       lchars
                                       paragraph-level
                                       levels)
  :enable bidi-resolve-sequences-from)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L1, the characters that rule X9 removed, and a whole paragraph.

(defrulel levels-ok-of-bidi-reset-levels
  (implies (and (levels-ok levels)
                (evenp (nfix paragraph-level)))
           (levels-ok
            (mv-nth 0 (bidi-reset-levels lchars levels paragraph-level))))
  :induct (bidi-reset-levels lchars levels paragraph-level)
  :enable bidi-reset-levels)

(defrulel bidi-levels-even-p-of-bidi-expand-levels
  (implies (levels-ok levels)
           (bidi-levels-even-p (bidi-expand-levels originals levels)))
  :induct (bidi-expand-levels originals levels)
  :enable (bidi-expand-levels bidi-level-option-even-p))

(defrulel bidi-levels-even-p-of-bidi-paragraph-levels
  (implies (and (source-classes-ok (bidi-char-list-classes chars))
                (evenp (nfix paragraph-level)))
           (bidi-levels-even-p (bidi-paragraph-levels chars paragraph-level)))
  :enable bidi-paragraph-levels)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A text: its paragraphs, and its code points.

(local
 (define char-ok ((char bidi-char-p))
   :returns (yes/no booleanp)
   (source-class-ok (bidi-char->class char))
   :hooks (:fix)))

(local
 (std::deflist chars-ok (x)
   :guard (bidi-char-listp x)
   (char-ok x)))

(defrulel chars-ok-of-bidi-char-list-fix
  (implies (chars-ok x)
           (chars-ok (bidi-char-list-fix x)))
  :induct t
  :enable bidi-char-list-fix)

(defrulel source-classes-ok-of-bidi-char-list-classes
  (implies (chars-ok chars)
           (source-classes-ok (bidi-char-list-classes chars)))
  :induct (bidi-char-list-classes chars)
  :enable (bidi-char-list-classes char-ok))

(defrulel bidi-paragraph-embedding-level-when-chars-ok
  (implies (and (chars-ok chars)
                (not (equal (paragraph-direction-kind direction)
                            :right-to-left)))
           (equal (bidi-paragraph-embedding-level chars direction)
                  0))
  :enable bidi-paragraph-embedding-level)

(defrulel chars-ok-of-take-of-bidi-paragraph-length
  (implies (chars-ok chars)
           (chars-ok (take (bidi-paragraph-length chars) chars)))
  :enable nfix)

(defrulel nfix-of-bidi-paragraph-length
  (equal (nfix (bidi-paragraph-length chars))
         (bidi-paragraph-length chars))
  :enable nfix)

(defrulel bidi-levels-even-p-of-bidi-levels-of-chars
  (implies (and (chars-ok chars)
                (not (equal (paragraph-direction-kind direction)
                            :right-to-left)))
           (bidi-levels-even-p (bidi-levels-of-chars chars direction)))
  :induct (bidi-levels-of-chars chars direction)
  :enable bidi-levels-of-chars)

(defrulel evenp-of-nfix-when-bidi-level-option-even-p
  (implies (and (bidi-level-option-even-p x)
                x)
           (evenp (nfix x)))
  :enable (bidi-level-option-even-p
           acl2::maybe-natp-fix
           nfix))

(defrulel not-bidi-lowest-odd-level-when-bidi-levels-even-p
  (implies (bidi-levels-even-p levels)
           (not (bidi-lowest-odd-level
                 (bidi-display-items levels position))))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items
           bidi-lowest-odd-level))

(defrulel chars-ok-of-code-points-to-bidi-chars
  (implies (right-to-left-free-p cps ver)
           (chars-ok (code-points-to-bidi-chars cps ver)))
  :induct (code-points-to-bidi-chars cps ver)
  :enable (code-points-to-bidi-chars
           code-point-bidi-char
           char-ok
           source-class-ok
           right-to-left-code-point-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-left-to-right-theorems
  :short "Theorems that text without right-to-left characters
          has only even levels and is displayed in the stored order."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem is about rule L2 alone:
     if no level is odd, the order of display is the order of the text
     (see @(tsee bidi-positions-with-level)).
     The second and the third are about a list of code points
     that has none of the classes that
     @(tsee right-to-left-code-point-p) recognizes,
     when the direction of the paragraphs is not given
     as right to left:
     every level is even, and the order of display
     is the order of the text.
     The characters that rule X9 removes have no level
     and are not in either order."))

  (defrule bidi-order-of-levels-when-bidi-levels-even-p
    (implies (bidi-levels-even-p levels)
             (equal (bidi-order-of-levels levels)
                    (bidi-positions-with-level levels 0)))
    :enable (bidi-order-of-levels
             bidi-display-item-list-positions-of-bidi-display-items))

  (defrulel bidi-order-of-chars-when-chars-ok
    (implies (and (chars-ok chars)
                  (not (equal (paragraph-direction-kind direction)
                              :right-to-left)))
             (equal (bidi-order-of-chars chars direction offset)
                    (bidi-positions-with-level
                     (bidi-levels-of-chars chars direction)
                     offset)))
    :induct (bidi-order-of-chars chars direction offset)
    :enable (bidi-order-of-chars
             bidi-paragraph-order)
    :expand ((bidi-levels-of-chars chars direction)))

  (defrule bidi-levels-even-p-of-bidi-levels-when-right-to-left-free-p
    (implies (and (right-to-left-free-p cps ver)
                  (not (equal (paragraph-direction-kind direction)
                              :right-to-left)))
             (bidi-levels-even-p (bidi-levels cps direction ver)))
    :enable bidi-levels)

  (defrule bidi-display-order-when-right-to-left-free-p
    (implies (and (right-to-left-free-p cps ver)
                  (not (equal (paragraph-direction-kind direction)
                              :right-to-left)))
             (equal (bidi-display-order cps direction ver)
                    (bidi-positions-with-level
                     (bidi-levels cps direction ver)
                     0)))
    :enable (bidi-display-order bidi-levels)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The text as displayed, with every character kept:
; the levels of the characters that rule X9 removes are even too,
; so rules L2, L3 and L4 change nothing.

(defrulel evenp-of-maybe-natp-fix-when-bidi-level-option-even-p
  (implies (and (bidi-level-option-even-p x)
                (acl2::maybe-natp-fix x))
           (evenp (acl2::maybe-natp-fix x)))
  :enable bidi-level-option-even-p)

(defrulel levels-ok-of-bidi-fill-levels
  (implies (and (bidi-levels-even-p levels)
                (evenp (nfix previous)))
           (levels-ok (bidi-fill-levels levels previous)))
  :induct (bidi-fill-levels levels previous)
  :enable bidi-fill-levels)

(defrulel levels-ok-of-bidi-reset-all-levels
  (implies (and (levels-ok levels)
                (evenp (nfix paragraph-level)))
           (levels-ok
            (mv-nth 0
                    (bidi-reset-all-levels classes levels paragraph-level))))
  :induct (bidi-reset-all-levels classes levels paragraph-level)
  :enable bidi-reset-all-levels)

(defrulel levels-ok-of-bidi-paragraph-all-levels
  (implies (and (source-classes-ok (bidi-char-list-classes chars))
                (evenp (nfix paragraph-level)))
           (levels-ok (bidi-paragraph-all-levels chars paragraph-level)))
  :enable bidi-paragraph-all-levels)

(defrulel bidi-levels-even-p-when-levels-ok
  (implies (and (nat-listp x)
                (levels-ok x))
           (bidi-levels-even-p x))
  :induct t
  :enable (bidi-level-option-even-p
           acl2::maybe-natp-fix
           nat-listp))

(local
 (define shown-ok ((char bidi-shown-char-p))
   :returns (yes/no booleanp)
   (evenp (bidi-shown-char->level char))
   :hooks (:fix)))

(local
 (std::deflist shown-list-ok (x)
   :guard (bidi-shown-char-listp x)
   (shown-ok x)))

(defrulel shown-list-ok-of-bidi-shown-chars
  (implies (levels-ok levels)
           (shown-list-ok (bidi-shown-chars cps levels)))
  :induct (bidi-shown-chars cps levels)
  :enable (bidi-shown-chars shown-ok))

(local
 (defun list-induction (x)
   (if (atom x)
       nil
     (list-induction (cdr x)))))

(defrulel bidi-move-marks-when-shown-list-ok
  (implies (shown-list-ok shown)
           (equal (bidi-move-marks shown nil ver)
                  (bidi-shown-char-list-fix shown)))
  :induct (list-induction shown)
  :enable (bidi-shown-char-list-fix shown-ok oddp)
  :expand ((bidi-move-marks shown nil ver)))

(defrulel bidi-mirror-chars-of-bidi-shown-chars-when-levels-ok
  (implies (and (levels-ok levels)
                (equal (len levels) (len cps)))
           (equal (bidi-mirror-chars (bidi-shown-chars cps levels) ver)
                  (code-point-list-fix cps)))
  :induct (bidi-shown-chars cps levels)
  :enable (bidi-shown-chars
           bidi-mirror-chars
           bidi-mirror-char
           code-point-list-fix
           oddp
           len
           fix))

(defrulel bidi-mirror-chars-of-bidi-arrange-paragraph-when-chars-ok
  (implies (and (chars-ok (code-points-to-bidi-chars cps ver))
                (not (equal (paragraph-direction-kind direction)
                            :right-to-left)))
           (equal (bidi-mirror-chars
                   (bidi-arrange-paragraph cps direction ver)
                   ver)
                  (code-point-list-fix cps)))
  :enable (bidi-arrange-paragraph
           bidi-arrange-with-levels
           bidi-shown-chars-at-of-bidi-positions-with-level))

(defrulel bidi-mirror-chars-of-append
  (equal (bidi-mirror-chars (append shown1 shown2) ver)
         (append (bidi-mirror-chars shown1 ver)
                 (bidi-mirror-chars shown2 ver)))
  :induct (list-induction shown1)
  :enable (bidi-mirror-chars append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of natural numbers that BIDI-LEVELS-EVEN-P recognizes
; has only even numbers.

(defruledl levels-ok-when-bidi-levels-even-p
  (implies (and (nat-listp x)
                (bidi-levels-even-p x))
           (levels-ok x))
  :induct t
  :enable (bidi-level-option-even-p
           acl2::maybe-natp-fix
           nat-listp))

(defsection bidi-display-even-levels-theorem
  :short "Theorem that a paragraph in which no level is odd
          is displayed as it is stored."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is about rules L2, L3 and L4 alone:
     the levels can be any list of natural numbers
     that is as long as the list of the code points.
     If none of them is odd, rule L2 reverses nothing,
     rule L3 moves no combining mark,
     and rule L4 replaces no character by its mirrored one.
     The levels need not be 0.
     A paragraph from right to left can have them:
     a left-to-right label that satisfies the strict rule
     derived from the Bidi Rule (see @(see bidi-rule))
     gets level 2 for each of its characters there
     (see @(see bidi-rule-left-to-right-label))."))

  (defrule bidi-mirror-chars-of-bidi-arrange-with-levels-when-even
    (implies (and (nat-listp levels)
                  (bidi-levels-even-p levels)
                  (equal (len levels) (len cps)))
             (equal (bidi-mirror-chars
                     (bidi-arrange-with-levels cps levels ver)
                     ver)
                    (code-point-list-fix cps)))
    :enable (bidi-arrange-with-levels
             bidi-shown-chars-at-of-bidi-positions-with-level
             levels-ok-when-bidi-levels-even-p)
    :disable bidi-levels-even-p-when-levels-ok))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-display-left-to-right-theorem
  :short "Theorem that text without right-to-left characters
          is displayed as it is, with every character kept."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as the theorems of
     @(see bidi-left-to-right-theorems)
     for the function @(tsee bidi-display),
     which also places the characters that rule X9 removes
     and applies rules L3 and L4:
     under the same condition, the text as displayed
     is the text as stored.
     Each of those characters takes the level of the character before it,
     which is even, so nothing is at an odd level:
     nothing is reversed, no combining mark is moved,
     and no character is mirrored."))

  (defrule bidi-display-when-right-to-left-free-p
    (implies (and (right-to-left-free-p cps ver)
                  (not (equal (paragraph-direction-kind direction)
                              :right-to-left)))
             (equal (bidi-display cps direction ver)
                    (code-point-list-fix cps)))
    :induct (bidi-arrange cps direction ver)
    :enable (bidi-display
             bidi-arrange
             bidi-mirror-chars
             code-point-list-fix
             nfix
             append-of-take-and-nthcdr-of-code-point-list-fix)))
