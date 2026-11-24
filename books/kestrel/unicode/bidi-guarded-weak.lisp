; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-weak-types")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book is a step of the proof of the theorem of the book
; bidi-guarded-theorem.lisp.  That book includes this one locally,
; through the book bidi-guarded-neutral.lisp.
; See the book bidi-guarded-theorem.lisp for the plan of the proof.
;
; This book defines the scan, which is the invariant of the proof,
; and proves that rules W1 to W7 of the Unicode Bidirectional Algorithm
; keep it, for a sequence with sos = L.
;
; The scan reads a list of classes together with a list of booleans,
; called OUTSIDE, that says for each position
; whether it is outside (T) or inside (NIL).
; The positions inside may have any classes, and may get any levels.
; The scan is a condition on the classes of the positions outside,
; under which the rules give every position outside the level 0.
; It has three states:
;
;   :FREE     at the start, and after a position outside whose class is L
;             or that follows a position outside in this state;
;   :INSIDE   after a position inside;
;   :ZONE     after a position outside that follows a position inside,
;             with no L between the two.
;
; In the state :FREE a position outside may have the class of
; a character that does not turn the direction: no R, AL or AN.
; After a position inside, the positions outside up to the first L
; (the zone) may not have the classes R, AL, EN and AN.
; After rules W1 to W7 they have classes that rules N1 and N2 resolve
; from the directions on the two sides of the zone.
; A zone ends with L or with the end of the sequence, where eos = L,
; and so they are all resolved to L;
; for that, a zone may not end with a position inside.
; The first position of a zone may not have the class ET or NSM,
; which rules W5 and W1 join to the character before.
;
; The classes allowed change as the rules are applied;
; the argument PHASE of the scan says which rules have been applied:
;
;   0   none: the classes of the characters;
;   1   rule W1 (and then also rules W2 to W5): no NSM is left;
;   2   rule W6: no ES, ET or CS is left;
;   3   rule W7 (and then also rule N0): no EN is left.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The kinds of the classes that a position outside may have,
; in the state :FREE, at the start of a zone, and further in a zone.
; The class L, which ends a zone, is not counted with the zone here.

(define bidi-scan-free-kind-p (kind (phase natp))
  :returns (yes/no booleanp)
  (b* ((phase (lnfix phase)))
    (or (eq kind :left-to-right)
        (eq kind :segment-separator)
        (eq kind :white-space)
        (eq kind :other-neutral)
        (and (<= phase 2)
             (eq kind :european-number))
        (and (<= phase 1)
             (or (eq kind :european-separator)
                 (eq kind :european-terminator)
                 (eq kind :common-separator)))
        (and (equal phase 0)
             (eq kind :nonspacing-mark))))
  :hooks nil)

(define bidi-scan-zone-first-kind-p (kind (phase natp))
  :returns (yes/no booleanp)
  (b* ((phase (lnfix phase)))
    (or (eq kind :segment-separator)
        (eq kind :white-space)
        (eq kind :other-neutral)
        (and (<= phase 1)
             (or (eq kind :european-separator)
                 (eq kind :common-separator)))))
  :hooks nil)

(define bidi-scan-zone-kind-p (kind (phase natp))
  :returns (yes/no booleanp)
  (b* ((phase (lnfix phase)))
    (or (eq kind :segment-separator)
        (eq kind :white-space)
        (eq kind :other-neutral)
        (and (<= phase 1)
             (or (eq kind :european-separator)
                 (eq kind :european-terminator)
                 (eq kind :common-separator)))
        (and (equal phase 0)
             (eq kind :nonspacing-mark))))
  :hooks nil)

; One step of the scan: the next state, or NIL if the scan fails.
; A state that is not :FREE or :INSIDE counts as :ZONE.

(define bidi-scan-step (st out (class bidi-class-p) (phase natp))
  :returns (new-st symbolp)
  (b* ((kind (bidi-class-kind class)))
    (cond ((not out) (if (or (eq st :free)
                             (eq st :inside))
                         :inside
                       nil))
          ((eq kind :left-to-right) :free)
          ((eq st :free) (and (bidi-scan-free-kind-p kind phase)
                              :free))
          ((eq st :inside) (and (bidi-scan-zone-first-kind-p kind phase)
                                :zone))
          (t (and (bidi-scan-zone-kind-p kind phase)
                  :zone))))
  :hooks nil)

; The scan succeeds.

(define bidi-scan-ok ((classes bidi-class-listp)
                      (outside boolean-listp)
                      st
                      (phase natp))
  :returns (yes/no booleanp)
  (b* (((when (endp classes)) t)
       (next (bidi-scan-step st (car outside) (car classes) phase)))
    (and next
         (bidi-scan-ok (cdr classes) (cdr outside) next phase)))
  :hooks nil)

; The state at the end of the scan, or NIL if the scan fails.

(define bidi-scan-end ((classes bidi-class-listp)
                       (outside boolean-listp)
                       st
                       (phase natp))
  :returns (new-st symbolp :hyp (symbolp st))
  (b* (((when (endp classes)) st)
       (next (bidi-scan-step st (car outside) (car classes) phase)))
    (and next
         (bidi-scan-end (cdr classes) (cdr outside) next phase)))
  :hooks nil)

; Every position that has a bracket role has the class ON.
; The paired brackets have the class ON,
; and the rules for the weak types do not change that class;
; so the bracket pairs of rule N0 are those of the text.

(define bidi-roles-neutral-p ((roles bidi-bracket-role-listp)
                              (classes bidi-class-listp))
  :returns (yes/no booleanp)
  (or (endp roles)
      (endp classes)
      (and (or (equal (bidi-bracket-role-kind (car roles)) :none)
               (equal (bidi-class-kind (car classes)) :other-neutral))
           (bidi-roles-neutral-p (cdr roles) (cdr classes))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here on, the events are local, except the theorems at the end.

; For each rule that goes along the list with a state of its own,
; there is a function for the induction,
; and a relation between the state of the scan and the state of the rule.
; The argument ALONG of the function is a list that goes along the classes:
; the list OUTSIDE, or a list of bracket roles
; (and then the state of the scan plays no part).

(local (in-theory (enable bidi-scan-step
                          bidi-scan-free-kind-p
                          bidi-scan-zone-first-kind-p
                          bidi-scan-zone-kind-p)))

; The rules that turn the fixing of a class of a known kind
; into a constant are disabled:
; with them, the same class is written in two ways in one goal.

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

(local
 (define list-induction (x)
   (if (consp x)
       (list-induction (cdr x))
     nil)
   :hooks nil))

; For the rules that have no state: rule W3, rule W6,
; and the backward part of rule W5.

(local
 (define scan-induction (classes along st (phase natp))
   (if (endp classes)
       (list along st)
     (scan-induction (cdr classes)
                     (cdr along)
                     (bidi-scan-step st (car along) (car classes) phase)
                     phase))
   :verify-guards nil
   :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W1: NSM takes the class of the character before.
; In the state :FREE that class is one allowed in that state,
; and in a zone it is one allowed in a zone;
; at the start of a zone there is no NSM.

(local
 (define w1-induction (classes along st previous)
   (b* (((when (endp classes)) (list along st previous))
        (class (bidi-class-fix (car classes)))
        (new-class
         (cond ((not (equal (bidi-class-kind class) :nonspacing-mark))
                class)
               ((bidi-class-isolate-formatting-p previous)
                (bidi-class-other-neutral))
               (t (bidi-class-fix previous)))))
     (w1-induction (cdr classes)
                   (cdr along)
                   (bidi-scan-step st (car along) (car classes) 0)
                   new-class))
   :verify-guards nil
   :hooks nil))

(local
 (define w1-relation (st (previous bidi-class-p))
   :returns (yes/no booleanp)
   (b* ((kind (bidi-class-kind previous)))
     (cond ((eq st :free) (bidi-scan-free-kind-p kind 1))
           ((eq st :inside) t)
           (t (bidi-scan-zone-kind-p kind 1))))
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-w1
  (implies (and (bidi-scan-ok classes outside st 0)
                (w1-relation st previous))
           (bidi-scan-ok (bidi-w1 classes previous) outside st 1))
  :induct (w1-induction classes outside st previous)
  :enable (w1-induction
           w1-relation
           bidi-scan-ok
           bidi-w1
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p)
  :expand ((bidi-w1 classes previous)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 1))))

(defrulel bidi-roles-neutral-p-of-bidi-w1
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w1 classes previous)))
  :induct (w1-induction classes roles st previous)
  :enable (w1-induction
           bidi-roles-neutral-p
           bidi-w1)
  :expand ((bidi-w1 classes previous)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W2: EN becomes AN after AL.
; In the state :FREE the last strong class is L,
; and elsewhere a position outside has no EN.

(local
 (define w2-induction (classes along st strong)
   (b* (((when (endp classes)) (list along st strong))
        (class (bidi-class-fix (car classes)))
        (strong (if (bidi-class-strong-p class)
                    class
                  (bidi-class-fix strong))))
     (w2-induction (cdr classes)
                   (cdr along)
                   (bidi-scan-step st (car along) (car classes) 1)
                   strong))
   :verify-guards nil
   :hooks nil))

(local
 (define strong-relation (st (strong bidi-class-p))
   :returns (yes/no booleanp)
   (or (not (eq st :free))
       (equal (bidi-class-kind strong) :left-to-right))
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-w2
  (implies (and (bidi-scan-ok classes outside st 1)
                (strong-relation st strong))
           (bidi-scan-ok (bidi-w2 classes strong) outside st 1))
  :induct (w2-induction classes outside st strong)
  :enable (w2-induction
           strong-relation
           bidi-scan-ok
           bidi-w2
           bidi-class-strong-p)
  :expand ((bidi-w2 classes strong)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 1))))

(defrulel bidi-roles-neutral-p-of-bidi-w2
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w2 classes strong)))
  :induct (w2-induction classes roles st strong)
  :enable (w2-induction
           bidi-roles-neutral-p
           bidi-w2)
  :expand ((bidi-w2 classes strong)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W3: AL becomes R.  No position outside has AL.

(defrulel bidi-scan-ok-of-bidi-w3
  (implies (bidi-scan-ok classes outside st 1)
           (bidi-scan-ok (bidi-w3 classes) outside st 1))
  :induct (scan-induction classes outside st 1)
  :enable (scan-induction
           bidi-scan-ok
           bidi-w3)
  :expand ((bidi-w3 classes)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 1))))

(defrulel bidi-roles-neutral-p-of-bidi-w3
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w3 classes)))
  :induct (scan-induction classes roles st 1)
  :enable (scan-induction
           bidi-roles-neutral-p
           bidi-w3)
  :expand ((bidi-w3 classes)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W4: a separator between two numbers becomes a number.
; In the state :FREE the class before is not AN, so the number is EN.
; In a zone, and at its start, the class after is not that of a number,
; because the zone goes on or ends with L.

(local
 (define w4-induction (classes along st previous)
   (if (endp classes)
       (list along st previous)
     (w4-induction (cdr classes)
                   (cdr along)
                   (bidi-scan-step st (car along) (car classes) 1)
                   (bidi-class-fix (car classes))))
   :verify-guards nil
   :hooks nil))

(local
 (define w4-relation (st (previous bidi-class-p))
   :returns (yes/no booleanp)
   (or (not (eq st :free))
       (not (equal (bidi-class-kind previous) :arabic-number)))
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-w4
  (implies (and (bidi-scan-ok classes outside st 1)
                (w4-relation st previous))
           (bidi-scan-ok (bidi-w4 classes previous) outside st 1))
  :induct (w4-induction classes outside st previous)
  :enable (w4-induction
           w4-relation
           bidi-scan-ok
           bidi-w4)
  :expand ((bidi-w4 classes previous)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 1))
           (bidi-scan-ok (cdr classes) (cdr outside) :zone 1)))

(defrulel bidi-roles-neutral-p-of-bidi-w4
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w4 classes previous)))
  :induct (w4-induction classes roles st previous)
  :enable (w4-induction
           bidi-roles-neutral-p
           bidi-w4)
  :expand ((bidi-w4 classes previous)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W5, forward: ET after EN becomes EN.
; A zone has no EN, and does not start with ET.

(local
 (define w5-induction (classes along st after-number)
   (b* (((when (endp classes)) (list along st after-number))
        (class (bidi-class-fix (car classes)))
        (new-class
         (if (and after-number
                  (equal (bidi-class-kind class) :european-terminator))
             (bidi-class-european-number)
           class)))
     (w5-induction (cdr classes)
                   (cdr along)
                   (bidi-scan-step st (car along) (car classes) 1)
                   (equal (bidi-class-kind new-class) :european-number)))
   :verify-guards nil
   :hooks nil))

(local
 (define w5-relation (st after-number)
   :returns (yes/no booleanp)
   (or (eq st :free)
       (eq st :inside)
       (not after-number))
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-w5-forward
  (implies (and (bidi-scan-ok classes outside st 1)
                (w5-relation st after-number))
           (bidi-scan-ok (bidi-w5-forward classes after-number) outside st 1))
  :induct (w5-induction classes outside st after-number)
  :enable (w5-induction
           w5-relation
           bidi-scan-ok
           bidi-w5-forward)
  :expand ((bidi-w5-forward classes after-number)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 1))))

(defrulel bidi-roles-neutral-p-of-bidi-w5-forward
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w5-forward classes after-number)))
  :induct (w5-induction classes roles st after-number)
  :enable (w5-induction
           bidi-roles-neutral-p
           bidi-w5-forward)
  :expand ((bidi-w5-forward classes after-number)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W5, backward: ET before EN becomes EN.
; The definition of the rule reverses the list, goes forward
; and reverses the result; here is the same from the end of the list.

(local
 (define w5-backward ((classes bidi-class-listp))
   :returns (new-classes bidi-class-listp)
   (b* (((when (endp classes)) nil)
        (class (bidi-class-fix (car classes)))
        (rest (w5-backward (cdr classes))))
     (cons (if (and (equal (bidi-class-kind class) :european-terminator)
                    (consp rest)
                    (equal (bidi-class-kind (car rest)) :european-number))
               (bidi-class-european-number)
             class)
           rest))
   :verify-guards :after-returns
   :hooks nil
   ///
   (defret consp-of-w5-backward
     (equal (consp new-classes)
            (consp classes))
     :hints (("Goal" :expand (w5-backward classes))))))

; Whether the forward part, at the end of a list, is after a number.

(local
 (define w5-flag ((classes bidi-class-listp) after-number)
   :returns (yes/no booleanp)
   (b* (((when (endp classes)) (and after-number t))
        (class (bidi-class-fix (car classes)))
        (new-class
         (if (and after-number
                  (equal (bidi-class-kind class) :european-terminator))
             (bidi-class-european-number)
           class)))
     (w5-flag (cdr classes)
              (equal (bidi-class-kind new-class) :european-number)))
   :hooks nil))

(defrulel bidi-w5-forward-of-append
  (equal (bidi-w5-forward (append x y) after-number)
         (append (bidi-w5-forward x after-number)
                 (bidi-w5-forward y (w5-flag x after-number))))
  :induct (bidi-w5-forward x after-number)
  :enable (bidi-w5-forward
           w5-flag))

(defrulel bidi-w5-forward-when-flag-not-nil
  (implies (and after-number
                (syntaxp (not (equal after-number ''t))))
           (equal (bidi-w5-forward classes after-number)
                  (bidi-w5-forward classes t)))
  :expand ((bidi-w5-forward classes after-number)
           (bidi-w5-forward classes t)))

(defrulel w5-flag-when-flag-not-nil
  (implies (and after-number
                (syntaxp (not (equal after-number ''t))))
           (equal (w5-flag classes after-number)
                  (w5-flag classes t)))
  :expand ((w5-flag classes after-number)
           (w5-flag classes t)))

(defrulel w5-flag-of-append
  (equal (w5-flag (append x y) after-number)
         (w5-flag y (w5-flag x after-number)))
  :induct (w5-flag x after-number)
  :enable w5-flag)

(defrulel w5-flag-of-rev
  (equal (w5-flag (rev classes) nil)
         (and (consp classes)
              (equal (bidi-class-kind (car (w5-backward classes)))
                     :european-number)))
  :induct (list-induction classes)
  :enable (list-induction
           rev
           w5-backward
           w5-flag))

(defrulel bidi-w5-forward-of-rev
  (equal (bidi-w5-forward (rev classes) nil)
         (rev (w5-backward classes)))
  :induct (list-induction classes)
  :enable (list-induction
           rev
           w5-backward
           bidi-w5-forward))

(defrulel bidi-w5-in-terms-of-w5-backward
  (equal (bidi-w5 classes)
         (w5-backward (bidi-w5-forward classes nil)))
  :enable bidi-w5)

; In a zone, no ET becomes EN, because the zone goes on without EN
; or ends with L.

(defrulel not-number-first-of-w5-backward-in-zone
  (implies (and (bidi-scan-ok classes outside st 1)
                (not (eq st :free))
                (not (eq st :inside))
                (consp classes))
           (not (equal (bidi-class-kind (car (w5-backward classes)))
                       :european-number)))
  :induct (scan-induction classes outside st 1)
  :enable (scan-induction
           bidi-scan-ok
           w5-backward))

(defrulel bidi-scan-ok-of-w5-backward
  (implies (bidi-scan-ok classes outside st 1)
           (bidi-scan-ok (w5-backward classes) outside st 1))
  :induct (scan-induction classes outside st 1)
  :enable (scan-induction
           bidi-scan-ok
           w5-backward)
  :expand ((w5-backward classes)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 1))))

(defrulel bidi-roles-neutral-p-of-w5-backward
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (w5-backward classes)))
  :induct (scan-induction classes roles st 1)
  :enable (scan-induction
           bidi-roles-neutral-p
           w5-backward)
  :expand ((w5-backward classes)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W6: ES, ET and CS become ON.

(defrulel bidi-scan-ok-of-bidi-w6
  (implies (bidi-scan-ok classes outside st 1)
           (bidi-scan-ok (bidi-w6 classes) outside st 2))
  :induct (scan-induction classes outside st 1)
  :enable (scan-induction
           bidi-scan-ok
           bidi-w6)
  :expand ((bidi-w6 classes)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 2))))

(defrulel bidi-roles-neutral-p-of-bidi-w6
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w6 classes)))
  :induct (scan-induction classes roles st 1)
  :enable (scan-induction
           bidi-roles-neutral-p
           bidi-w6)
  :expand ((bidi-w6 classes)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule W7: EN becomes L after L.
; In the state :FREE the last strong class is L,
; and elsewhere a position outside has no EN.

(local
 (define w7-induction (classes along st strong)
   (b* (((when (endp classes)) (list along st strong))
        (class (bidi-class-fix (car classes)))
        (strong (bidi-class-case class
                                 :left-to-right class
                                 :right-to-left class
                                 :otherwise (bidi-class-fix strong))))
     (w7-induction (cdr classes)
                   (cdr along)
                   (bidi-scan-step st (car along) (car classes) 2)
                   strong))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-w7
  (implies (and (bidi-scan-ok classes outside st 2)
                (strong-relation st strong))
           (bidi-scan-ok (bidi-w7 classes strong) outside st 3))
  :induct (w7-induction classes outside st strong)
  :enable (w7-induction
           strong-relation
           bidi-scan-ok
           bidi-w7)
  :expand ((bidi-w7 classes strong)
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 3))))

(defrulel bidi-roles-neutral-p-of-bidi-w7
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-w7 classes strong)))
  :induct (w7-induction classes roles st strong)
  :enable (w7-induction
           bidi-roles-neutral-p
           bidi-w7)
  :expand ((bidi-w7 classes strong)
           (:free (a b) (bidi-roles-neutral-p roles (cons a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems of this book.

; This theorem does not name the class L in its conclusion:
; the prover writes that class as a constant,
; which a call of BIDI-CLASS-LEFT-TO-RIGHT would not match.

(defrule bidi-scan-ok-of-bidi-resolve-weak-types
  (implies (and (bidi-scan-ok classes outside :free 0)
                (equal sos (bidi-class-left-to-right)))
           (bidi-scan-ok (bidi-resolve-weak-types classes sos)
                         outside
                         :free
                         3))
  :enable (bidi-resolve-weak-types
           w1-relation
           strong-relation
           w4-relation
           w5-relation))

(defrule bidi-roles-neutral-p-of-bidi-resolve-weak-types
  (implies (bidi-roles-neutral-p roles classes)
           (bidi-roles-neutral-p roles (bidi-resolve-weak-types classes sos)))
  :enable bidi-resolve-weak-types)
