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

; This book is a step of the proofs of the theorems of the books
; bidi-guarded-theorem.lisp and bidi-self-contained.lisp.
; Those books include this one locally,
; through the book bidi-guarded-neutral.lisp.
; See each of the two books for the plan of its proof.
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
;
; For the second proof, this book also proves that rules W1 to W7
; do in a window what they do to the window alone.
; A window is a run of positions inside that starts
; with the class R, AL or AN and has positions outside,
; or nothing, on its two sides: see the section "Windows" below.

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

; The part of a list at the positions N to N+M-1, called a window.
; The argument OUTSIDE is not used.  It is there for the rewrite rules
; about windows: their hypotheses are about the marks,
; and a rule finds the marks in this argument.

(define bidi-window ((n natp) (m natp) outside (list true-listp))
  :returns (part true-listp)
  (take m (nthcdr n list))
  :ignore-ok t
  :irrelevant-formals-ok t
  :hooks nil)

; The kinds of the classes of the characters that start a part inside:
; R, AL and AN.  The first position of a window has such a class.

(define bidi-window-start-kind-p (kind)
  :returns (yes/no booleanp)
  (or (eq kind :right-to-left)
      (eq kind :arabic-letter)
      (eq kind :arabic-number))
  :hooks nil)

; The marks at the two ends of a window, in a list of a given length:
; the first and the last position of the window are inside,
; and the position before the window and the position after it
; are outside, if they are in the list.

(define bidi-window-marks-p ((n natp) (m natp) outside (length natp))
  :returns (yes/no booleanp)
  (and (natp n)
       (posp m)
       (natp length)
       (<= (+ n m) length)
       (not (nth n outside))
       (or (equal n 0)
           (nth (- n 1) outside))
       (not (nth (+ -1 n m) outside))
       (or (equal (+ n m) length)
           (nth (+ n m) outside))
       t)
  :verify-guards nil
  :hooks nil)

(defrule len-of-bidi-window
  (equal (len (bidi-window n m outside list))
         (nfix m))
  :enable bidi-window)

(defrule bidi-class-listp-of-bidi-window
  (implies (and (bidi-class-listp list)
                (natp n)
                (natp m)
                (<= (+ n m) (len list)))
           (bidi-class-listp (bidi-window n m outside list)))
  :enable (bidi-window nfix))

(defrule car-of-bidi-window
  (implies (posp m)
           (equal (car (bidi-window n m outside list))
                  (nth n list)))
  :expand (take m (nthcdr n list))
  :enable (bidi-window posp))

(defrule consp-of-bidi-window
  (equal (consp (bidi-window n m outside list))
         (posp m))
  :enable (bidi-window posp zp))

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

; Windows.
;
; A window is a run of positions that starts with a position inside
; whose class is R, AL or AN, that comes at the start of the sequence
; or after a position outside, and whose last position is inside
; and comes at the end of the sequence or before a position outside.
; The rest of this book proves that, on a sequence with sos = L
; on which the scan succeeds, rules W1 to W7 do in a window
; what they do to the window alone:
; taking the window and applying a rule can be done in either order.
;
; A rule that goes along the list with a state of its own
; reaches the window in some state.  For each such rule,
; a function gives the state after N positions (W1-STATE, ...),
; the rest of the result from a position is the result
; on the rest of the list from that state (NTHCDR-OF-...),
; and that state does the same to the window as the state at the start:
; because of the first class of the window (rules W1, W4 and W5),
; or because the scan is in the state :FREE there (rules W2 and W7).
; A rule that looks at the class after (rules W4 and W5)
; finds after the window a class that is not that of a number,
; and so does there what it does at the end of a list.

; The state of the scan after N positions.

(local
 (define scan-at ((n natp) classes outside st (phase natp))
   (b* (((when (or (zp n)
                   (endp classes)))
         st)
        (next (bidi-scan-step st (car outside) (car classes) phase)))
     (and next
          (scan-at (- n 1) (cdr classes) (cdr outside) next phase)))
   :verify-guards nil
   :hooks nil))

; One step of the scan, at a position inside and at a position outside.
; With these three rules the lemmas about the scan up to a position
; are proved without the cases of the definition of the step.
; They are not local: the book bidi-guarded-neutral.lisp uses them too.

(defruled bidi-scan-step-when-inside-position
  (implies (not out)
           (equal (bidi-scan-step st out class phase)
                  (if (or (eq st :free)
                          (eq st :inside))
                      :inside
                    nil))))

(defruled bidi-scan-step-when-outside-position
  (implies out
           (not (equal (bidi-scan-step st out class phase)
                       :inside))))

(defruled bidi-class-kind-when-bidi-scan-step-after-inside
  (implies (and (bidi-scan-step :inside out class phase)
                out)
           (and (not (equal (bidi-class-kind class) :european-number))
                (not (equal (bidi-class-kind class) :arabic-number))
                (not (equal (bidi-class-kind class) :european-terminator))
                (not (equal (bidi-class-kind class) :nonspacing-mark)))))

; At the first position of a window the scan is in the state :FREE.

(defrulel scan-at-of-start-of-window
  (implies (and (bidi-scan-ok classes outside st phase)
                (natp n)
                (< n (len classes))
                (not (nth n outside))
                (if (equal n 0)
                    (eq st :free)
                  (nth (- n 1) outside)))
           (equal (scan-at n classes outside st phase)
                  :free))
  :induct (scan-at n classes outside st phase)
  :expand ((:free (st) (bidi-scan-ok classes outside st phase))
           (:free (st) (bidi-scan-ok (cdr classes) (cdr outside) st phase)))
  :enable (scan-at
           nth
           len
           bidi-scan-step-when-inside-position
           bidi-scan-step-when-outside-position)
  :disable bidi-scan-step)

; The position after a window does not have the class of a number,
; and does not have the class ET or NSM.
; This rule is not local either.

(defruled bidi-class-kind-of-nth-after-window
  (implies (and (bidi-scan-ok classes outside st phase)
                (posp j)
                (< j (len classes))
                (not (nth (- j 1) outside))
                (nth j outside))
           (and (not (equal (bidi-class-kind (nth j classes))
                            :european-number))
                (not (equal (bidi-class-kind (nth j classes))
                            :arabic-number))
                (not (equal (bidi-class-kind (nth j classes))
                            :european-terminator))
                (not (equal (bidi-class-kind (nth j classes))
                            :nonspacing-mark))))
  :induct (scan-at j classes outside st phase)
  :expand ((:free (st) (bidi-scan-ok classes outside st phase))
           (:free (st) (bidi-scan-ok (cdr classes) (cdr outside) st phase)))
  :enable (scan-at
           nth
           len
           bidi-scan-step-when-inside-position
           bidi-class-kind-when-bidi-scan-step-after-inside)
  :disable bidi-scan-step)

(local (in-theory (enable bidi-class-kind-of-nth-after-window)))

(defrulel fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :enable fix)

; The rules on the empty list.

(defrulel bidi-w1-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w1 classes previous)
                  nil))
  :expand (bidi-w1 classes previous))

(defrulel bidi-w2-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w2 classes strong)
                  nil))
  :expand (bidi-w2 classes strong))

(defrulel bidi-w3-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w3 classes)
                  nil))
  :expand (bidi-w3 classes))

(defrulel bidi-w4-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w4 classes previous)
                  nil))
  :expand (bidi-w4 classes previous))

(defrulel bidi-w5-forward-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w5-forward classes after-number)
                  nil))
  :expand (bidi-w5-forward classes after-number))

(defrulel w5-backward-when-not-consp
  (implies (not (consp classes))
           (equal (w5-backward classes)
                  nil))
  :expand (w5-backward classes))

(defrulel len-of-w5-backward
  (equal (len (w5-backward classes))
         (len classes))
  :induct (len classes)
  :expand (w5-backward classes)
  :enable len)

(defrulel bidi-w6-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w6 classes)
                  nil))
  :expand (bidi-w6 classes))

(defrulel bidi-w7-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-w7 classes strong)
                  nil))
  :expand (bidi-w7 classes strong))

;;;;;;;;;;;;;;;;;;;;

; Rule W1 in a window.  The first class of a window is not NSM.

(local
 (define w1-state ((n natp) classes previous)
   (b* (((when (or (zp n)
                   (endp classes)))
         previous)
        (class (bidi-class-fix (car classes)))
        (new-class
         (cond ((not (equal (bidi-class-kind class) :nonspacing-mark))
                class)
               ((bidi-class-isolate-formatting-p previous)
                (bidi-class-other-neutral))
               (t (bidi-class-fix previous)))))
     (w1-state (- n 1) (cdr classes) new-class))
   :verify-guards nil
   :hooks nil))

(defrulel w1-state-when-zp
  (implies (zp n)
           (equal (w1-state n classes previous)
                  previous))
  :expand (w1-state n classes previous))

(defrulel nthcdr-of-bidi-w1
  (equal (nthcdr n (bidi-w1 classes previous))
         (bidi-w1 (nthcdr n classes)
                  (w1-state n classes previous)))
  :induct (w1-state n classes previous)
  :expand (bidi-w1 classes previous)
  :enable (w1-state nthcdr))

(defrulel take-of-bidi-w1
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-w1 classes previous))
                  (bidi-w1 (take m classes) previous)))
  :induct (w1-state m classes previous)
  :expand ((bidi-w1 classes previous)
           (:free (a b) (bidi-w1 (cons a b) previous)))
  :enable (w1-state take len nfix))

(defrulel bidi-w1-of-w1-state
  (implies (and (consp classes)
                (not (equal (bidi-class-kind (car classes))
                            :nonspacing-mark)))
           (equal (bidi-w1 classes (w1-state n other previous))
                  (bidi-w1 classes previous)))
  :expand ((bidi-w1 classes (w1-state n other previous))
           (bidi-w1 classes previous)))

(defrulel bidi-class-kind-of-nth-of-bidi-w1
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind (nth n (bidi-w1 classes previous)))
                  (bidi-class-kind (nth n classes))))
  :induct (w1-state n classes previous)
  :expand (bidi-w1 classes previous)
  :enable (w1-state nth bidi-window-start-kind-p acl2::default-car))

(defrulel bidi-window-of-bidi-w1
  (implies (and (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes))))
           (equal (bidi-window n m outside (bidi-w1 classes previous))
                  (bidi-w1 (bidi-window n m outside classes) previous)))
  :enable (bidi-window
           bidi-window-marks-p
           bidi-window-start-kind-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W2 in a window.  The rule depends on the last strong class
; only through whether it is AL; in the state :FREE it is L.

(local
 (define w2-state ((n natp) classes strong)
   (b* (((when (or (zp n)
                   (endp classes)))
         strong)
        (class (bidi-class-fix (car classes)))
        (strong (if (bidi-class-strong-p class)
                    class
                  (bidi-class-fix strong))))
     (w2-state (- n 1) (cdr classes) strong))
   :verify-guards nil
   :hooks nil))

(defrulel w2-state-when-zp
  (implies (zp n)
           (equal (w2-state n classes strong)
                  strong))
  :expand (w2-state n classes strong))

(defrulel nthcdr-of-bidi-w2
  (equal (nthcdr n (bidi-w2 classes strong))
         (bidi-w2 (nthcdr n classes)
                  (w2-state n classes strong)))
  :induct (w2-state n classes strong)
  :expand (bidi-w2 classes strong)
  :enable (w2-state nthcdr))

(defrulel take-of-bidi-w2
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-w2 classes strong))
                  (bidi-w2 (take m classes) strong)))
  :induct (w2-state m classes strong)
  :expand ((bidi-w2 classes strong)
           (:free (a b) (bidi-w2 (cons a b) strong)))
  :enable (w2-state take len nfix))

(local
 (define w2-two-induction (classes strong1 strong2)
   (b* (((when (endp classes)) (list strong1 strong2))
        (class (bidi-class-fix (car classes))))
     (w2-two-induction (cdr classes)
                       (if (bidi-class-strong-p class)
                           class
                         (bidi-class-fix strong1))
                       (if (bidi-class-strong-p class)
                           class
                         (bidi-class-fix strong2))))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w2-when-not-after-arabic-letter
  (implies (and (not (equal (bidi-class-kind strong1) :arabic-letter))
                (not (equal (bidi-class-kind strong2) :arabic-letter)))
           (equal (equal (bidi-w2 classes strong1)
                         (bidi-w2 classes strong2))
                  t))
  :induct (w2-two-induction classes strong1 strong2)
  :expand ((bidi-w2 classes strong1)
           (bidi-w2 classes strong2))
  :enable (w2-two-induction bidi-class-strong-p))

(local
 (define w2-at-induction ((n natp) classes outside st strong)
   (b* (((when (or (zp n)
                   (endp classes)))
         (list outside st strong))
        (class (bidi-class-fix (car classes)))
        (strong (if (bidi-class-strong-p class)
                    class
                  (bidi-class-fix strong))))
     (w2-at-induction (- n 1)
                      (cdr classes)
                      (cdr outside)
                      (bidi-scan-step st (car outside) (car classes) 1)
                      strong))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-class-kind-of-w2-state-when-free
  (implies (and (bidi-scan-ok classes outside st 1)
                (strong-relation st strong)
                (equal (scan-at n classes outside st 1) :free))
           (equal (bidi-class-kind (w2-state n classes strong))
                  :left-to-right))
  :induct (w2-at-induction n classes outside st strong)
  :expand ((:free (st) (bidi-scan-ok classes outside st 1))
           (:free (st) (scan-at n classes outside st 1))
           (w2-state n classes strong))
  :enable (w2-at-induction
           strong-relation
           bidi-class-strong-p))

(defrulel bidi-class-kind-of-nth-of-bidi-w2
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind (nth n (bidi-w2 classes strong)))
                  (bidi-class-kind (nth n classes))))
  :induct (w2-state n classes strong)
  :expand (bidi-w2 classes strong)
  :enable (w2-state nth bidi-window-start-kind-p acl2::default-car))

(defrulel bidi-window-of-bidi-w2
  (implies (and (bidi-scan-ok classes outside :free 1)
                (bidi-window-marks-p n m outside (len classes))
                (equal (bidi-class-kind strong) :left-to-right))
           (equal (bidi-window n m outside (bidi-w2 classes strong))
                  (bidi-w2 (bidi-window n m outside classes) strong)))
  :enable (bidi-window
           bidi-window-marks-p
           strong-relation
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W3 in a window.

(defrulel nthcdr-of-bidi-w3
  (equal (nthcdr n (bidi-w3 classes))
         (bidi-w3 (nthcdr n classes)))
  :induct (nthcdr n classes)
  :expand (bidi-w3 classes)
  :enable nthcdr)

(defrulel take-of-bidi-w3
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-w3 classes))
                  (bidi-w3 (take m classes))))
  :induct (take m classes)
  :expand ((bidi-w3 classes)
           (:free (a b) (bidi-w3 (cons a b))))
  :enable (take len nfix))

; The kind of a class after the rule.  The rule about the first class
; of a window is stated with this function, and not with an IF,
; so that the rewriter can use it under the other rules.

(local
 (define w3-kind (kind)
   (if (eq kind :arabic-letter)
       :right-to-left
     kind)
   :hooks nil))

(defrulel bidi-window-start-kind-p-of-w3-kind
  (equal (bidi-window-start-kind-p (w3-kind kind))
         (bidi-window-start-kind-p kind))
  :enable (w3-kind bidi-window-start-kind-p))

(defrulel w3-kind-is-not-arabic-letter
  (not (equal (w3-kind kind) :arabic-letter))
  :enable w3-kind)

(defrulel bidi-class-kind-of-nth-of-bidi-w3
  (equal (bidi-class-kind (nth n (bidi-w3 classes)))
         (w3-kind (bidi-class-kind (nth n classes))))
  :induct (nth n classes)
  :expand (bidi-w3 classes)
  :enable (nth w3-kind acl2::default-car))

(defrulel bidi-window-of-bidi-w3
  (implies (bidi-window-marks-p n m outside (len classes))
           (equal (bidi-window n m outside (bidi-w3 classes))
                  (bidi-w3 (bidi-window n m outside classes))))
  :enable (bidi-window
           bidi-window-marks-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W4 in a window.  The first class of a window is not ES or CS,
; and the class after a window is not EN or AN.

(local
 (define w4-state ((n natp) classes previous)
   (if (or (zp n)
           (endp classes))
       previous
     (w4-state (- n 1) (cdr classes) (bidi-class-fix (car classes))))
   :verify-guards nil
   :hooks nil))

(defrulel w4-state-when-zp
  (implies (zp n)
           (equal (w4-state n classes previous)
                  previous))
  :expand (w4-state n classes previous))

(defrulel nthcdr-of-bidi-w4
  (equal (nthcdr n (bidi-w4 classes previous))
         (bidi-w4 (nthcdr n classes)
                  (w4-state n classes previous)))
  :induct (w4-state n classes previous)
  :expand (bidi-w4 classes previous)
  :enable (w4-state nthcdr))

(defrulel take-of-bidi-w4
  (implies (and (<= (nfix m) (len classes))
                (or (equal (nfix m) (len classes))
                    (and (not (equal (bidi-class-kind (nth m classes))
                                     :european-number))
                         (not (equal (bidi-class-kind (nth m classes))
                                     :arabic-number)))))
           (equal (take m (bidi-w4 classes previous))
                  (bidi-w4 (take m classes) previous)))
  :induct (w4-state m classes previous)
  :expand ((bidi-w4 classes previous)
           (:free (a b) (bidi-w4 (cons a b) previous)))
  :enable (w4-state take len nth nfix))

(defrulel bidi-w4-of-w4-state
  (implies (and (consp classes)
                (not (equal (bidi-class-kind (car classes))
                            :european-separator))
                (not (equal (bidi-class-kind (car classes))
                            :common-separator)))
           (equal (bidi-w4 classes (w4-state n other previous))
                  (bidi-w4 classes previous)))
  :expand ((bidi-w4 classes (w4-state n other previous))
           (bidi-w4 classes previous)))

(defrulel bidi-class-kind-of-nth-of-bidi-w4
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind (nth n (bidi-w4 classes previous)))
                  (bidi-class-kind (nth n classes))))
  :induct (w4-state n classes previous)
  :expand (bidi-w4 classes previous)
  :enable (w4-state nth bidi-window-start-kind-p acl2::default-car))

(defrulel bidi-window-of-bidi-w4
  (implies (and (bidi-scan-ok classes outside :free 1)
                (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes))))
           (equal (bidi-window n m outside (bidi-w4 classes previous))
                  (bidi-w4 (bidi-window n m outside classes) previous)))
  :cases ((equal (+ n m) (len classes)))
  :enable (bidi-window
           bidi-window-marks-p
           bidi-window-start-kind-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W5 in a window, forward.  The first class of a window is not ET.

(local
 (define w5f-state ((n natp) classes after-number)
   (b* (((when (or (zp n)
                   (endp classes)))
         after-number)
        (class (bidi-class-fix (car classes)))
        (new-class
         (if (and after-number
                  (equal (bidi-class-kind class) :european-terminator))
             (bidi-class-european-number)
           class)))
     (w5f-state (- n 1)
                (cdr classes)
                (equal (bidi-class-kind new-class) :european-number)))
   :verify-guards nil
   :hooks nil))

(defrulel w5f-state-when-zp
  (implies (zp n)
           (equal (w5f-state n classes after-number)
                  after-number))
  :expand (w5f-state n classes after-number))

(defrulel nthcdr-of-bidi-w5-forward
  (equal (nthcdr n (bidi-w5-forward classes after-number))
         (bidi-w5-forward (nthcdr n classes)
                          (w5f-state n classes after-number)))
  :induct (w5f-state n classes after-number)
  :expand ((:free (after-number) (bidi-w5-forward classes after-number)))
  :enable (w5f-state nthcdr))

(defrulel take-of-bidi-w5-forward
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-w5-forward classes after-number))
                  (bidi-w5-forward (take m classes) after-number)))
  :induct (w5f-state m classes after-number)
  :expand ((:free (after-number) (bidi-w5-forward classes after-number))
           (:free (a b after-number)
                  (bidi-w5-forward (cons a b) after-number)))
  :enable (w5f-state take len nfix))

(defrulel bidi-w5-forward-of-w5f-state
  (implies (and (consp classes)
                (not (equal (bidi-class-kind (car classes))
                            :european-terminator)))
           (equal (bidi-w5-forward classes (w5f-state n other after-number))
                  (bidi-w5-forward classes after-number)))
  :expand ((bidi-w5-forward classes (w5f-state n other after-number))
           (bidi-w5-forward classes after-number))
  :disable bidi-w5-forward-when-flag-not-nil)

(defrulel bidi-class-kind-of-nth-of-bidi-w5-forward
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind
                   (nth n (bidi-w5-forward classes after-number)))
                  (bidi-class-kind (nth n classes))))
  :induct (w5f-state n classes after-number)
  :expand ((:free (after-number) (bidi-w5-forward classes after-number)))
  :enable (w5f-state nth bidi-window-start-kind-p acl2::default-car)
  :disable bidi-w5-forward-when-flag-not-nil)

(defrulel bidi-window-of-bidi-w5-forward
  (implies (and (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes))))
           (equal (bidi-window n m outside
                               (bidi-w5-forward classes after-number))
                  (bidi-w5-forward (bidi-window n m outside classes)
                                   after-number)))
  :enable (bidi-window
           bidi-window-marks-p
           bidi-window-start-kind-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W5 in a window, backward.
; The class after a window is not EN or ET.

(defrulel nthcdr-of-w5-backward
  (equal (nthcdr n (w5-backward classes))
         (w5-backward (nthcdr n classes)))
  :induct (nthcdr n classes)
  :expand (w5-backward classes)
  :enable nthcdr)

(defrulel take-of-w5-backward
  (implies (and (<= (nfix m) (len classes))
                (or (equal (nfix m) (len classes))
                    (and (not (equal (bidi-class-kind (nth m classes))
                                     :european-number))
                         (not (equal (bidi-class-kind (nth m classes))
                                     :european-terminator)))))
           (equal (take m (w5-backward classes))
                  (w5-backward (take m classes))))
  :induct (take m classes)
  :expand ((w5-backward classes)
           (w5-backward (cdr classes))
           (:free (a b) (w5-backward (cons a b))))
  :enable (take len nth nfix))

(defrulel bidi-class-kind-of-nth-of-w5-backward
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind (nth n (w5-backward classes)))
                  (bidi-class-kind (nth n classes))))
  :induct (nth n classes)
  :expand (w5-backward classes)
  :enable (nth bidi-window-start-kind-p acl2::default-car))

(defrulel bidi-window-of-w5-backward
  (implies (and (bidi-scan-ok classes outside :free 1)
                (bidi-window-marks-p n m outside (len classes)))
           (equal (bidi-window n m outside (w5-backward classes))
                  (w5-backward (bidi-window n m outside classes))))
  :cases ((equal (+ n m) (len classes)))
  :enable (bidi-window
           bidi-window-marks-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W6 in a window.

(defrulel nthcdr-of-bidi-w6
  (equal (nthcdr n (bidi-w6 classes))
         (bidi-w6 (nthcdr n classes)))
  :induct (nthcdr n classes)
  :expand (bidi-w6 classes)
  :enable nthcdr)

(defrulel take-of-bidi-w6
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-w6 classes))
                  (bidi-w6 (take m classes))))
  :induct (take m classes)
  :expand ((bidi-w6 classes)
           (:free (a b) (bidi-w6 (cons a b))))
  :enable (take len nfix))

(defrulel bidi-class-kind-of-nth-of-bidi-w6
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind (nth n (bidi-w6 classes)))
                  (bidi-class-kind (nth n classes))))
  :induct (nth n classes)
  :expand (bidi-w6 classes)
  :enable (nth bidi-window-start-kind-p acl2::default-car))

(defrulel bidi-window-of-bidi-w6
  (implies (bidi-window-marks-p n m outside (len classes))
           (equal (bidi-window n m outside (bidi-w6 classes))
                  (bidi-w6 (bidi-window n m outside classes))))
  :enable (bidi-window
           bidi-window-marks-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule W7 in a window.  The rule depends on the last strong class
; only through whether it is L; in the state :FREE it is L.

(local
 (define w7-state ((n natp) classes strong)
   (b* (((when (or (zp n)
                   (endp classes)))
         strong)
        (class (bidi-class-fix (car classes)))
        (strong (bidi-class-case class
                                 :left-to-right class
                                 :right-to-left class
                                 :otherwise (bidi-class-fix strong))))
     (w7-state (- n 1) (cdr classes) strong))
   :verify-guards nil
   :hooks nil))

(defrulel w7-state-when-zp
  (implies (zp n)
           (equal (w7-state n classes strong)
                  strong))
  :expand (w7-state n classes strong))

(defrulel nthcdr-of-bidi-w7
  (equal (nthcdr n (bidi-w7 classes strong))
         (bidi-w7 (nthcdr n classes)
                  (w7-state n classes strong)))
  :induct (w7-state n classes strong)
  :expand (bidi-w7 classes strong)
  :enable (w7-state nthcdr))

(defrulel take-of-bidi-w7
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-w7 classes strong))
                  (bidi-w7 (take m classes) strong)))
  :induct (w7-state m classes strong)
  :expand ((bidi-w7 classes strong)
           (:free (a b) (bidi-w7 (cons a b) strong)))
  :enable (w7-state take len nfix))

(local
 (define w7-two-induction (classes strong1 strong2)
   (b* (((when (endp classes)) (list strong1 strong2))
        (class (bidi-class-fix (car classes))))
     (w7-two-induction (cdr classes)
                       (bidi-class-case class
                                        :left-to-right class
                                        :right-to-left class
                                        :otherwise (bidi-class-fix strong1))
                       (bidi-class-case class
                                        :left-to-right class
                                        :right-to-left class
                                        :otherwise (bidi-class-fix strong2))))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-w7-when-after-left-to-right
  (implies (and (equal (bidi-class-kind strong1) :left-to-right)
                (equal (bidi-class-kind strong2) :left-to-right))
           (equal (equal (bidi-w7 classes strong1)
                         (bidi-w7 classes strong2))
                  t))
  :induct (w7-two-induction classes strong1 strong2)
  :expand ((bidi-w7 classes strong1)
           (bidi-w7 classes strong2))
  :enable w7-two-induction)

(local
 (define w7-at-induction ((n natp) classes outside st strong)
   (b* (((when (or (zp n)
                   (endp classes)))
         (list outside st strong))
        (class (bidi-class-fix (car classes)))
        (strong (bidi-class-case class
                                 :left-to-right class
                                 :right-to-left class
                                 :otherwise (bidi-class-fix strong))))
     (w7-at-induction (- n 1)
                      (cdr classes)
                      (cdr outside)
                      (bidi-scan-step st (car outside) (car classes) 2)
                      strong))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-class-kind-of-w7-state-when-free
  (implies (and (bidi-scan-ok classes outside st 2)
                (strong-relation st strong)
                (equal (scan-at n classes outside st 2) :free))
           (equal (bidi-class-kind (w7-state n classes strong))
                  :left-to-right))
  :induct (w7-at-induction n classes outside st strong)
  :expand ((:free (st) (bidi-scan-ok classes outside st 2))
           (:free (st) (scan-at n classes outside st 2))
           (w7-state n classes strong))
  :enable (w7-at-induction
           strong-relation))

(defrulel bidi-class-kind-of-nth-of-bidi-w7
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (equal (bidi-class-kind (nth n (bidi-w7 classes strong)))
                  (bidi-class-kind (nth n classes))))
  :induct (w7-state n classes strong)
  :expand (bidi-w7 classes strong)
  :enable (w7-state nth bidi-window-start-kind-p acl2::default-car))

(defrulel bidi-window-of-bidi-w7
  (implies (and (bidi-scan-ok classes outside :free 2)
                (bidi-window-marks-p n m outside (len classes))
                (equal (bidi-class-kind strong) :left-to-right))
           (equal (bidi-window n m outside (bidi-w7 classes strong))
                  (bidi-w7 (bidi-window n m outside classes) strong)))
  :enable (bidi-window
           bidi-window-marks-p
           strong-relation
           nfix))

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

; Rules W1 to W7 do in a window what they do to the window alone.

(defruled bidi-window-of-bidi-resolve-weak-types
  (implies (and (bidi-scan-ok classes outside :free 0)
                (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
                (equal sos (bidi-class-left-to-right)))
           (equal (bidi-window n m outside
                               (bidi-resolve-weak-types classes sos))
                  (bidi-resolve-weak-types (bidi-window n m outside classes)
                                           sos)))
  :enable (bidi-resolve-weak-types
           w1-relation
           strong-relation
           w4-relation
           w5-relation))

; The first class of a window stays one of R, AL and AN, and is not AL.

(defruled bidi-window-start-kind-p-of-nth-of-bidi-resolve-weak-types
  (implies (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
           (and (bidi-window-start-kind-p
                 (bidi-class-kind
                  (nth n (bidi-resolve-weak-types classes sos))))
                (not (equal (bidi-class-kind
                             (nth n (bidi-resolve-weak-types classes sos)))
                            :arabic-letter))))
  :enable bidi-resolve-weak-types)
