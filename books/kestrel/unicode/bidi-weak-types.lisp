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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-weak-types
  :parents (bidirectional-algorithm)
  :short "Resolving the weak types:
          rules W1 to W7 of the Unicode Bidirectional Algorithm."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules [UAX #9, Section 3.3.4] work on
     one isolating run sequence at a time
     (see @(see bidi-resolved-levels)).
     They change the classes of the nonspacing marks,
     of the numbers, and of the characters that separate or end numbers.
     After them, the classes that are left in the sequence are
     @('L'), @('R'), @('EN') (European Number), @('AN') (Arabic Number),
     and the neutral and isolate formatting classes.")
   (xdoc::p
    "Each rule is a function from the list of the classes
     of the characters of the sequence to a list of the same length.
     Where a rule looks at the character before the first one,
     it is given the class @('sos'), for start of sequence,
     which is @('L') or @('R') [UAX #9, rule X10].
     The rules are applied one after the other to the whole sequence;
     see @(tsee bidi-resolve-weak-types)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-w1 ((classes bidi-class-listp) (previous bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule W1: the nonspacing marks."
  :long
  (xdoc::topstring
   (xdoc::p
    "A nonspacing mark (@('NSM')) takes the class of the character
     before it, or the class @('ON') (Other Neutral)
     if that character is an isolate initiator or a @('PDI')
     [UAX #9, rule W1].
     The class of the character before it is the one
     that this rule has given it, if it is a mark too.
     The second argument is the class of the character before the list:
     @('sos') at first."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (new-class
        (cond ((not (equal (bidi-class-kind class) :nonspacing-mark))
               class)
              ((bidi-class-isolate-formatting-p previous)
               (bidi-class-other-neutral))
              (t (bidi-class-fix previous)))))
    (cons new-class
          (bidi-w1 (cdr classes) new-class)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w1
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w2 ((classes bidi-class-listp) (strong bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule W2: European numbers after an Arabic letter."
  :long
  (xdoc::topstring
   (xdoc::p
    "A European number (@('EN')) becomes an Arabic number (@('AN'))
     if the last strong class before it
     (@('R'), @('L') or @('AL'), or @('sos') if there is none)
     is @('AL') (Arabic Letter) [UAX #9, rule W2].
     The second argument is the last strong class before the list:
     @('sos') at first."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (strong (if (bidi-class-strong-p class)
                   class
                 (bidi-class-fix strong)))
       (new-class
        (if (and (equal (bidi-class-kind class) :european-number)
                 (equal (bidi-class-kind strong) :arabic-letter))
            (bidi-class-arabic-number)
          class)))
    (cons new-class
          (bidi-w2 (cdr classes) strong)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w2
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w3 ((classes bidi-class-listp))
  :returns (new-classes bidi-class-listp)
  :short "Rule W3: Arabic letters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every @('AL') (Arabic Letter) becomes @('R') [UAX #9, rule W3]."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes))))
    (cons (if (equal (bidi-class-kind class) :arabic-letter)
              (bidi-class-right-to-left)
            class)
          (bidi-w3 (cdr classes))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w3
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w4 ((classes bidi-class-listp) (previous bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule W4: one separator between two numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A single European separator (@('ES'))
     between two European numbers becomes a European number.
     A single common separator (@('CS'))
     between two numbers of the same class,
     both @('EN') or both @('AN'),
     becomes a number of that class [UAX #9, rule W4].
     The characters on the two sides are looked at
     as they were before this rule;
     a separator that changes had a number on each side,
     so its neighbors are not separators and do not change.
     The second argument is the class of the character before the list:
     @('sos') at first."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (previous (bidi-class-fix previous))
       (next? (and (consp (cdr classes))
                   (bidi-class-fix (cadr classes))))
       (new-class
        (cond ((and (equal (bidi-class-kind class) :european-separator)
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
          (bidi-w4 (cdr classes) class)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w4
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w5-forward ((classes bidi-class-listp) (after-number booleanp))
  :returns (new-classes bidi-class-listp)
  :short "The half of rule W5 for the terminators that follow a number."
  :long
  (xdoc::topstring
   (xdoc::p
    "A European terminator (@('ET')) becomes a European number
     if the character before it is a European number,
     or a terminator that this function has just turned into one.
     The second argument says whether the character before the list
     is such a number."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (new-class
        (if (and after-number
                 (equal (bidi-class-kind class) :european-terminator))
            (bidi-class-european-number)
          class)))
    (cons new-class
          (bidi-w5-forward (cdr classes)
                           (equal (bidi-class-kind new-class)
                                  :european-number))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w5-forward
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w5 ((classes bidi-class-listp))
  :returns (new-classes bidi-class-listp)
  :short "Rule W5: terminators next to European numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A sequence of European terminators (@('ET'))
     next to a European number, before it or after it,
     becomes European numbers [UAX #9, rule W5].
     We first change the terminators that follow a number,
     going forward (see @(tsee bidi-w5-forward)),
     and then, by doing the same on the reversed list,
     those that come before a number."))
  (rev (bidi-w5-forward (rev (bidi-w5-forward classes nil)) nil))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w5
    (equal (len new-classes)
           (len classes))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w6 ((classes bidi-class-listp))
  :returns (new-classes bidi-class-listp)
  :short "Rule W6: the separators and terminators that are left."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every @('ES'), @('ET') and @('CS') that rules W4 and W5
     have not changed becomes @('ON') (Other Neutral)
     [UAX #9, rule W6]."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes))))
    (cons (bidi-class-case class
                           :european-separator (bidi-class-other-neutral)
                           :european-terminator (bidi-class-other-neutral)
                           :common-separator (bidi-class-other-neutral)
                           :otherwise class)
          (bidi-w6 (cdr classes))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w6
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-w7 ((classes bidi-class-listp) (strong bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rule W7: European numbers after a left-to-right character."
  :long
  (xdoc::topstring
   (xdoc::p
    "A European number (@('EN')) becomes @('L')
     if the last strong class before it
     (@('R') or @('L'), or @('sos') if there is none)
     is @('L') [UAX #9, rule W7].
     The second argument is the last strong class before the list:
     @('sos') at first."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (strong (bidi-class-case class
                                :left-to-right class
                                :right-to-left class
                                :otherwise (bidi-class-fix strong)))
       (new-class
        (if (and (equal (bidi-class-kind class) :european-number)
                 (equal (bidi-class-kind strong) :left-to-right))
            (bidi-class-left-to-right)
          class)))
    (cons new-class
          (bidi-w7 (cdr classes) strong)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-w7
    (equal (len new-classes)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-resolve-weak-types ((classes bidi-class-listp)
                                 (sos bidi-class-p))
  :returns (new-classes bidi-class-listp)
  :short "Rules W1 to W7, in that order, on one isolating run sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each rule is applied to the whole sequence
     before the next one [UAX #9, rule X10]."))
  (b* ((classes (bidi-w1 classes sos))
       (classes (bidi-w2 classes sos))
       (classes (bidi-w3 classes))
       (classes (bidi-w4 classes sos))
       (classes (bidi-w5 classes))
       (classes (bidi-w6 classes)))
    (bidi-w7 classes sos))
  :hooks (:fix)

  ///

  (defret len-of-bidi-resolve-weak-types
    (equal (len new-classes)
           (len classes))))
