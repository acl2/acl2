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

(defxdoc+ bidi-explicit-rules
  :parents (bidirectional-algorithm)
  :short "The explicit levels and directions:
          rules X1 to X8 of the Unicode Bidirectional Algorithm."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules [UAX #9, Section 3.3.2] go through a paragraph once
     and give each character an embedding level,
     according to the explicit directional formatting characters
     before it:
     the embeddings (@('LRE') and @('RLE')),
     the overrides (@('LRO') and @('RLO')),
     the isolates (@('LRI'), @('RLI') and @('FSI')),
     and the characters that end them (@('PDF') and @('PDI')).
     An override also changes the class of the characters in its scope
     to @('L') or @('R').")
   (xdoc::p
    "The rules keep a stack, the directional status stack,
     with an entry for each embedding, override or isolate
     that is open and valid,
     and three counters.
     The stack never has more than 126 entries:
     an initiator that would bring the level above 125 has no effect,
     and the counters keep track of such initiators
     so that the characters that end them are not mistaken
     for the ends of valid ones.")
   (xdoc::p
    "In the specification the stack is never empty,
     and where it pops an entry it shows that another one remains.
     Here the last entry of the stack is kept apart from the others
     (see @(tsee explicit-state)), so the stack cannot be empty,
     and the functions do nothing where the specification
     shows that a case cannot arise."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-max-depth ()
  :returns (depth natp :rule-classes (:rewrite :type-prescription))
  :short "The highest explicit embedding level."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is 125; the specification calls it @('max_depth') [UAX #9, BD2].
     The implicit rules can add one to a level, so that the levels
     that the whole algorithm gives go up to 126."))
  125)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum directional-override
  :short "Fixtype of directional override statuses."
  :long
  (xdoc::topstring
   (xdoc::p
    "The directional override status says whether
     the class of the characters is to be changed,
     and to what [UAX #9, BD6]:
     not at all (neutral),
     to @('L') (left-to-right),
     or to @('R') (right-to-left)."))
  (:neutral ())
  (:left-to-right ())
  (:right-to-left ())
  :pred directional-override-p)

;;;;;;;;;;;;;;;;;;;;

(define apply-directional-override ((class bidi-class-p)
                                    (override directional-override-p))
  :returns (new-class bidi-class-p)
  :short "The bidirectional class of a character
          under a directional override status."
  (directional-override-case override
                             :neutral (bidi-class-fix class)
                             :left-to-right (bidi-class-left-to-right)
                             :right-to-left (bidi-class-right-to-left))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod directional-status
  :short "Fixtype of entries of the directional status stack."
  :long
  (xdoc::topstring
   (xdoc::p
    "An entry has an embedding level,
     a directional override status,
     and a directional isolate status,
     which is true when the entry was pushed by an isolate initiator
     [UAX #9, BD12 and Section 3.3.2]."))
  ((level nat)
   (override directional-override)
   (isolate bool))
  :pred directional-status-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist directional-status-list
  :short "Fixtype of lists of entries of the directional status stack."
  :elt-type directional-status
  :true-listp t
  :elementp-of-nil nil
  :pred directional-status-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod explicit-state
  :short "Fixtype of the states of rules X1 to X8."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state is the directional status stack and three counters
     [UAX #9, Section 3.3.2].
     The stack is given as its last entry (@('top'))
     and the list of the entries under it (@('below')),
     the most recent first.
     The overflow isolate count is the number of isolate initiators
     that had no effect because of the depth limit
     and whose matching @('PDI') has not been met.
     The overflow embedding count is the same for
     the embedding and override initiators and @('PDF'),
     not counting those inside such an isolate.
     The valid isolate count is the number of entries of the stack
     that an isolate initiator pushed."))
  ((top directional-status)
   (below directional-status-list)
   (overflow-isolates nat)
   (overflow-embeddings nat)
   (valid-isolates nat))
  :pred explicit-state-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define least-greater-level ((level natp) (odd booleanp))
  :returns (new-level natp :rule-classes (:rewrite :type-prescription))
  :short "The least odd level, or the least even level,
          greater than a level."
  :long
  (xdoc::topstring
   (xdoc::p
    "An initiator from right to left asks for the least odd level
     greater than the current one,
     and an initiator from left to right for the least even one
     [UAX #9, rules X2 to X5b]."))
  (b* ((level (lnfix level)))
    (if (iff (evenp level) odd)
        (+ 1 level)
      (+ 2 level)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define explicit-state-enter-embedding ((st explicit-state-p)
                                        (right-to-left booleanp)
                                        (override directional-override-p))
  :returns (new-st explicit-state-p)
  :short "The state after an embedding or override initiator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is what rules X2 to X5 have in common
     [UAX #9, rules X2 to X5].
     If the new level is at most 125 and both overflow counts are zero,
     the initiator is valid: an entry with the new level
     and the given override status is pushed.
     Otherwise, the overflow embedding count goes up by one
     if the overflow isolate count is zero."))
  (b* (((explicit-state st))
       (new-level (least-greater-level (directional-status->level st.top)
                                       right-to-left)))
    (cond ((and (<= new-level (bidi-max-depth))
                (equal st.overflow-isolates 0)
                (equal st.overflow-embeddings 0))
           (change-explicit-state
            st
            :top (make-directional-status :level new-level
                                          :override override
                                          :isolate nil)
            :below (cons st.top st.below)))
          ((equal st.overflow-isolates 0)
           (change-explicit-state
            st
            :overflow-embeddings (+ 1 st.overflow-embeddings)))
          (t (explicit-state-fix st))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define explicit-state-enter-isolate ((st explicit-state-p)
                                      (right-to-left booleanp))
  :returns (new-st explicit-state-p)
  :short "The state after an isolate initiator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the last step of rules X5a and X5b
     [UAX #9, rules X5a and X5b].
     If the new level is at most 125 and both overflow counts are zero,
     the initiator is valid: an entry with the new level,
     no override, and a true isolate status is pushed,
     and the valid isolate count goes up by one.
     Otherwise the overflow isolate count goes up by one."))
  (b* (((explicit-state st))
       (new-level (least-greater-level (directional-status->level st.top)
                                       right-to-left)))
    (if (and (<= new-level (bidi-max-depth))
             (equal st.overflow-isolates 0)
             (equal st.overflow-embeddings 0))
        (change-explicit-state
         st
         :top (make-directional-status
               :level new-level
               :override (directional-override-neutral)
               :isolate t)
         :below (cons st.top st.below)
         :valid-isolates (+ 1 st.valid-isolates))
      (change-explicit-state
       st
       :overflow-isolates (+ 1 st.overflow-isolates))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define directional-status-pop-to-isolate ((top directional-status-p)
                                           (below directional-status-listp))
  :returns (mv (new-top directional-status-p)
               (new-below directional-status-listp))
  :short "Pop the entries of the directional status stack
          down to the last one that an isolate initiator pushed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This pops entries while the isolate status of the last one is false
     [UAX #9, rule X6a].
     It stops at the bottom of the stack if there is no such entry,
     which the specification shows does not happen where this is used."))
  (cond ((directional-status->isolate top)
         (mv (directional-status-fix top)
             (directional-status-list-fix below)))
        ((endp below) (mv (directional-status-fix top) nil))
        (t (directional-status-pop-to-isolate (car below) (cdr below))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define explicit-state-leave-isolate ((st explicit-state-p))
  :returns (new-st explicit-state-p)
  :short "The state after a @('PDI')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the first step of rule X6a [UAX #9, rule X6a].
     If the overflow isolate count is not zero,
     the @('PDI') matches an isolate initiator that had no effect,
     and the count goes down by one.
     Otherwise, if the valid isolate count is zero,
     the @('PDI') matches nothing and nothing changes.
     Otherwise it matches a valid isolate initiator:
     the overflow embedding count becomes zero,
     the entries above the entry of that isolate are popped,
     that entry is popped too,
     and the valid isolate count goes down by one.
     This ends the embeddings and overrides inside the isolate
     that were still open."))
  (b* (((explicit-state st)))
    (cond ((> st.overflow-isolates 0)
           (change-explicit-state
            st
            :overflow-isolates (- st.overflow-isolates 1)))
          ((equal st.valid-isolates 0) (explicit-state-fix st))
          (t (b* (((mv top below)
                   (directional-status-pop-to-isolate st.top st.below))
                  ((mv top below)
                   (if (consp below)
                       (mv (car below) (cdr below))
                     (mv top below))))
               (change-explicit-state
                st
                :top top
                :below below
                :overflow-embeddings 0
                :valid-isolates (- st.valid-isolates 1))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define explicit-state-leave-embedding ((st explicit-state-p))
  :returns (new-st explicit-state-p)
  :short "The state after a @('PDF')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is rule X7 [UAX #9, rule X7].
     If the overflow isolate count is not zero, nothing changes.
     Otherwise, if the overflow embedding count is not zero,
     it goes down by one.
     Otherwise, if the last entry of the stack was not pushed
     by an isolate initiator and is not the only entry,
     it is popped.
     Otherwise the @('PDF') matches nothing and nothing changes."))
  (b* (((explicit-state st)))
    (cond ((> st.overflow-isolates 0) (explicit-state-fix st))
          ((> st.overflow-embeddings 0)
           (change-explicit-state
            st
            :overflow-embeddings (- st.overflow-embeddings 1)))
          ((and (not (directional-status->isolate st.top))
                (consp st.below))
           (change-explicit-state st
                                  :top (car st.below)
                                  :below (cdr st.below)))
          (t (explicit-state-fix st))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-explicit-step ((class bidi-class-p)
                            (rest bidi-class-listp)
                            (st explicit-state-p)
                            (paragraph-level natp))
  :returns (mv (level natp :rule-classes (:rewrite :type-prescription))
               (new-class bidi-class-p)
               (new-st explicit-state-p))
  :short "Apply rules X2 to X8 to one character."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the class of the character,
     the classes of the characters after it in the paragraph,
     the state, and the paragraph embedding level.
     The results are the explicit embedding level of the character,
     its class, which an override may have changed,
     and the new state.")
   (xdoc::ul
    (xdoc::li
     "An embedding or override initiator
      (@('RLE'), @('LRE'), @('RLO'), @('LRO'))
      changes the state by rules X2 to X5.")
    (xdoc::li
     "An isolate initiator (@('RLI'), @('LRI'), @('FSI'))
      gets the level and the override of the last entry of the stack,
      and then changes the state by rule X5a or X5b.
      An @('FSI') is treated as an @('RLI')
      if rules P2 and P3, applied to the characters
      between it and its matching @('PDI'), give level 1,
      and as an @('LRI') otherwise [UAX #9, rule X5c].")
    (xdoc::li
     "A @('PDI') first changes the state by rule X6a,
      and then gets the level and the override
      of what is then the last entry of the stack.")
    (xdoc::li
     "A @('PDF') changes the state by rule X7.")
    (xdoc::li
     "A paragraph separator (@('B')) gets the paragraph embedding level
      [UAX #9, rule X8].")
    (xdoc::li
     "Any other character gets the level and the override
      of the last entry of the stack [UAX #9, rule X6],
      except that the class @('BN') is not changed by an override."))
   (xdoc::p
    "The specification gives no level to the characters of the classes
     that rule X9 removes (see @(tsee bidi-class-removed-p)).
     Here they get the level of the last entry of the stack,
     which nothing uses."))
  (b* (((explicit-state st))
       ((directional-status top) st.top)
       (class (bidi-class-fix class)))
    (bidi-class-case
     class
     :right-to-left-embedding
     (mv top.level
         class
         (explicit-state-enter-embedding st
                                         t
                                         (directional-override-neutral)))
     :left-to-right-embedding
     (mv top.level
         class
         (explicit-state-enter-embedding st
                                         nil
                                         (directional-override-neutral)))
     :right-to-left-override
     (mv top.level
         class
         (explicit-state-enter-embedding
          st
          t
          (directional-override-right-to-left)))
     :left-to-right-override
     (mv top.level
         class
         (explicit-state-enter-embedding
          st
          nil
          (directional-override-left-to-right)))
     :right-to-left-isolate
     (mv top.level
         (apply-directional-override class top.override)
         (explicit-state-enter-isolate st t))
     :left-to-right-isolate
     (mv top.level
         (apply-directional-override class top.override)
         (explicit-state-enter-isolate st nil))
     :first-strong-isolate
     (mv top.level
         (apply-directional-override class top.override)
         (explicit-state-enter-isolate
          st
          (equal (bidi-first-strong-level rest t) 1)))
     :pop-directional-isolate
     (b* ((new-st (explicit-state-leave-isolate st))
          ((directional-status new-top) (explicit-state->top new-st)))
       (mv new-top.level
           (apply-directional-override class new-top.override)
           new-st))
     :pop-directional-format
     (mv top.level class (explicit-state-leave-embedding st))
     :paragraph-separator
     (mv (lnfix paragraph-level) class (explicit-state-fix st))
     :boundary-neutral
     (mv top.level class (explicit-state-fix st))
     :otherwise
     (mv top.level
         (apply-directional-override class top.override)
         (explicit-state-fix st))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-explicit-levels-from ((classes bidi-class-listp)
                                   (st explicit-state-p)
                                   (paragraph-level natp))
  :returns (mv (levels nat-listp)
               (new-classes bidi-class-listp))
  :short "Apply rules X2 to X8 to the characters of a paragraph,
          from a state."
  (b* (((when (endp classes)) (mv nil nil))
       ((mv level class st)
        (bidi-explicit-step (car classes) (cdr classes) st paragraph-level))
       ((mv levels new-classes)
        (bidi-explicit-levels-from (cdr classes) st paragraph-level)))
    (mv (cons level levels)
        (cons class new-classes)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-explicit-levels-from.levels
    (equal (len levels)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defret len-of-bidi-explicit-levels-from.new-classes
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-explicit-levels ((classes bidi-class-listp)
                              (paragraph-level natp))
  :returns (mv (levels nat-listp)
               (new-classes bidi-class-listp))
  :short "The explicit embedding levels of the characters of a paragraph,
          and their classes after the overrides."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the bidirectional classes
     of the characters of the paragraph,
     and the second is the paragraph embedding level.
     The stack starts with one entry,
     which has the paragraph embedding level, no override,
     and a false isolate status;
     the three counters start at zero [UAX #9, rule X1].
     Then rules X2 to X8 are applied to each character in turn
     (see @(tsee bidi-explicit-step)).")
   (xdoc::p
    "The two results are lists as long as the argument:
     the level of each character,
     and the class of each character,
     which is its own class unless an override changed it."))
  (bidi-explicit-levels-from
   classes
   (make-explicit-state
    :top (make-directional-status :level paragraph-level
                                  :override (directional-override-neutral)
                                  :isolate nil)
    :below nil
    :overflow-isolates 0
    :overflow-embeddings 0
    :valid-isolates 0)
   paragraph-level)
  :hooks (:fix)

  ///

  (defret len-of-bidi-explicit-levels.levels
    (equal (len levels)
           (len classes)))

  (defret len-of-bidi-explicit-levels.new-classes
    (equal (len new-classes)
           (len classes))))
