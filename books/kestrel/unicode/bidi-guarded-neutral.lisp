; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-resolved-levels")
(include-book "bidi-guarded-plain")
(include-book "bidi-guarded-brackets")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book is a step of the proof of the theorem of the book
; bidi-guarded-theorem.lisp, which includes this book locally.
; See that book for the plan of the proof.
;
; This book proves that rule N0 of the Unicode Bidirectional Algorithm
; keeps the scan (see the book bidi-guarded-weak.lisp),
; that rules N1 and N2 then give the class L to every position outside,
; and so that rules I1 and I2 give it the level 0.
; With the theorem of the book bidi-guarded-weak.lisp,
; this gives the theorem at the end of this book:
; if the scan succeeds on the classes of a sequence with sos = eos = L
; and embedding level 0, every position outside gets the level 0.
;
; Rule N0 needs a condition on the bracket pairs:
; a pair whose opening bracket is inside has its closing bracket inside.
; The rule gives the two brackets of a pair the class L or the class R.
; The class L does no harm to the scan anywhere.
; The class R is given only if the context before the opening bracket
; is R and there is a strong R, and no strong L, inside the pair.
; For an opening bracket outside that cannot be:
; in the state :FREE the context is L,
; and in a zone the first strong class after the bracket is L.
; So the class R is given only to pairs that are inside,
; and to the marks (NSM) that follow their brackets,
; which are inside too: the first position of a zone is not a mark.
;
; The definitions of this book are for the proof only.
; The guards of those that look into a list at a position
; that may be beyond its end are not verified.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definition that the book bidi-guarded-theorem.lisp uses.

; Every pair whose opening bracket is inside has its closing bracket inside.

(define bidi-pairs-closed-inside-p ((pairs bracket-pair-listp)
                                    (outside boolean-listp))
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (or (nth (bracket-pair->open (car pairs)) outside)
               (not (nth (bracket-pair->close (car pairs)) outside)))
           (bidi-pairs-closed-inside-p (cdr pairs) outside)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here on, the events are local, except the theorem at the end.

; A theorem that is to be used as a rewrite rule
; does not name the class L or the class R in its conclusion:
; the prover writes those classes as constants,
; which a call of BIDI-CLASS-LEFT-TO-RIGHT would not match.
; The conclusion has a variable instead (LEFT, RIGHT, SOS, ...),
; and a hypothesis says which class the variable is.

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

(defrulel fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :enable fix)

(local
 (define list-induction (x)
   (if (consp x)
       (list-induction (cdr x))
     nil)
   :hooks nil))

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

; Facts about the scan.

; The state :FREE allows everything that another state allows.

(defrulel bidi-scan-ok-from-free-when-bidi-scan-ok
  (implies (bidi-scan-ok classes outside st phase)
           (bidi-scan-ok classes outside :free phase))
  :induct (scan-induction classes outside st phase)
  :enable (scan-induction bidi-scan-ok))

(defrulel bidi-scan-ok-of-nil
  (bidi-scan-ok nil outside st phase)
  :expand (bidi-scan-ok nil outside st phase))

(defrulel bidi-scan-ok-of-bidi-class-list-fix
  (equal (bidi-scan-ok (bidi-class-list-fix classes) outside st phase)
         (bidi-scan-ok classes outside st phase))
  :induct (scan-induction classes outside st phase)
  :enable (scan-induction
           bidi-scan-ok
           bidi-class-list-fix))

; A mark (NSM), in the classes of the characters,
; that follows a position inside is inside:
; the first position of a zone is not a mark.

(local
 (define marks-inside-p ((originals bidi-class-listp)
                         (outside boolean-listp)
                         previous-inside)
   :returns (yes/no booleanp)
   (or (endp originals)
       (and (or (not previous-inside)
                (not (equal (bidi-class-kind (car originals))
                            :nonspacing-mark))
                (not (car outside)))
            (marks-inside-p (cdr originals)
                            (cdr outside)
                            (not (car outside)))))
   :hooks nil))

(local
 (define marks-induction (originals outside st previous-inside)
   (if (endp originals)
       (list outside st previous-inside)
     (marks-induction (cdr originals)
                      (cdr outside)
                      (bidi-scan-step st (car outside) (car originals) 0)
                      (not (car outside))))
   :verify-guards nil
   :hooks nil))

(defrulel marks-inside-p-when-bidi-scan-ok
  (implies (and (bidi-scan-ok originals outside st 0)
                (or (not previous-inside)
                    (eq st :inside)))
           (marks-inside-p originals outside previous-inside))
  :induct (marks-induction originals outside st previous-inside)
  :expand ((:free (st) (bidi-scan-ok originals outside st 0))
           (:free (previous-inside)
                  (marks-inside-p originals outside previous-inside)))
  :enable marks-induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0: a pair whose opening bracket is outside is not given the class R.

; In a zone, if there is no strong L inside the pair,
; there is no strong R either: the zone goes on up to an L.

(local
 (define zone-induction (classes outside st (position natp))
   (if (endp classes)
       (list outside st position)
     (zone-induction (cdr classes)
                     (cdr outside)
                     (bidi-scan-step st (car outside) (car classes) 3)
                     (+ 1 (nfix position))))
   :verify-guards nil
   :hooks nil))

(defrulel no-strong-right-inside-pair-in-zone
  (implies (and (bidi-scan-ok classes outside st 3)
                (not (eq st :free))
                (not (eq st :inside))
                (natp position)
                (< (bracket-pair->open pair) position)
                (equal left (bidi-class-left-to-right))
                (equal right (bidi-class-right-to-left))
                (not (bidi-n0-strong-inside-p classes position pair left)))
           (not (bidi-n0-strong-inside-p classes position pair right)))
  :induct (zone-induction classes outside st position)
  :expand ((:free (st) (bidi-scan-ok classes outside st 3))
           (:free (direction)
                  (bidi-n0-strong-inside-p classes position pair direction)))
  :enable (zone-induction
           bidi-class-direction
           nfix))

; Up to the opening bracket: in the state :FREE,
; the direction that the context has so far is L.

(local
 (define context-induction (classes outside st (position natp) pair direction)
   (if (or (endp classes)
           (>= (nfix position) (bracket-pair->open pair)))
       (list outside st direction)
     (context-induction (cdr classes)
                        (cdr outside)
                        (bidi-scan-step st (car outside) (car classes) 3)
                        (+ 1 (nfix position))
                        pair
                        (or (bidi-class-direction (car classes))
                            direction)))
   :verify-guards nil
   :hooks nil))

(defruledl bidi-n0-context-when-opener-outside-lemma
  (b* ((open (bracket-pair->open pair)))
    (implies (and (bidi-scan-ok classes outside st 3)
                  (equal left (bidi-class-left-to-right))
                  (equal right (bidi-class-right-to-left))
                  (or (not (eq st :free))
                      (equal direction left))
                  (natp position)
                  (<= position open)
                  (nth (- open position) outside)
                  (not (equal (bidi-class-kind (nth (- open position) classes))
                              :left-to-right))
                  (not (bidi-n0-strong-inside-p classes position pair left))
                  (bidi-n0-strong-inside-p classes position pair right))
             (not (equal (bidi-n0-context classes (- open position) direction)
                         right))))
  :induct (context-induction classes outside st position pair direction)
  :expand ((:free (st) (bidi-scan-ok classes outside st 3))
           (:free (position direction)
                  (bidi-n0-strong-inside-p classes position pair direction)))
  :enable (context-induction
           bidi-n0-context
           bidi-class-direction
           nth
           nfix))

(defrulel bidi-n0-context-when-opener-outside
  (b* ((open (bracket-pair->open pair)))
    (implies (and (bidi-scan-ok classes outside :free 3)
                  (equal left (bidi-class-left-to-right))
                  (equal right (bidi-class-right-to-left))
                  (nth open outside)
                  (not (equal (bidi-class-kind (nth open classes))
                              :left-to-right))
                  (not (bidi-n0-strong-inside-p classes 0 pair left))
                  (bidi-n0-strong-inside-p classes 0 pair right))
             (not (equal (bidi-n0-context classes open left)
                         right))))
  :use (:instance bidi-n0-context-when-opener-outside-lemma
                  (st :free)
                  (position 0)
                  (direction left))
  :enable fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0: giving the class L to the brackets of a pair,
; and to the marks that follow them, keeps the scan.
; After a position outside that gets the class L the state is :FREE,
; which allows everything that the state before allowed.

(local
 (define set-left-induction (classes originals outside st (position natp)
                                     pair after-bracket)
   (b* (((when (endp classes)) (list originals outside st after-bracket))
        (position (nfix position))
        (originals (bidi-class-list-fix originals))
        (bracket (or (equal position (bracket-pair->open pair))
                     (equal position (bracket-pair->close pair))))
        (mark (and after-bracket
                   (bidi-starts-with-mark-p originals))))
     (list (set-left-induction (cdr classes)
                               (cdr originals)
                               (cdr outside)
                               (bidi-scan-step st (car outside) (car classes) 3)
                               (+ 1 position)
                               pair
                               (or bracket mark))
           (set-left-induction (cdr classes)
                               (cdr originals)
                               (cdr outside)
                               :free
                               (+ 1 position)
                               pair
                               (or bracket mark))))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-n0-set-pair-to-left
  (implies (and (bidi-scan-ok classes outside st 3)
                (equal left (bidi-class-left-to-right)))
           (bidi-scan-ok (bidi-n0-set-pair classes
                                           originals
                                           position
                                           pair
                                           left
                                           after-bracket)
                         outside
                         st
                         3))
  :induct (set-left-induction classes originals outside st position
                              pair after-bracket)
  :expand ((:free (position left after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    left
                                    after-bracket))
           (:free (st) (bidi-scan-ok classes outside st 3))
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 3)))
  :enable set-left-induction)

; Rule N0: giving any class to positions inside keeps the scan.
; The positions are those of the two brackets of the pair,
; and those of the marks that follow them, which are inside.

(local
 (define set-inside-induction (classes originals outside st (position natp)
                                       pair after-bracket previous-inside)
   (b* (((when (endp classes))
         (list originals outside st after-bracket previous-inside))
        (position (nfix position))
        (bracket (or (equal position (bracket-pair->open pair))
                     (equal position (bracket-pair->close pair))))
        (mark (and after-bracket
                   (bidi-starts-with-mark-p originals))))
     (set-inside-induction (cdr classes)
                           (cdr originals)
                           (cdr outside)
                           (bidi-scan-step st (car outside) (car classes) 3)
                           (+ 1 position)
                           pair
                           (or bracket mark)
                           (not (car outside))))
   :verify-guards nil
   :hooks nil))

(defrulel marks-inside-p-when-not-consp
  (implies (not (consp originals))
           (marks-inside-p originals outside previous-inside))
  :expand (marks-inside-p originals outside previous-inside))

(defrulel marks-inside-p-of-bidi-class-list-fix
  (equal (marks-inside-p (bidi-class-list-fix originals)
                         outside
                         previous-inside)
         (marks-inside-p originals outside previous-inside))
  :induct (marks-inside-p originals outside previous-inside)
  :enable (marks-inside-p
           bidi-class-list-fix))

(defrulel bidi-scan-ok-of-bidi-n0-set-pair-inside
  (b* ((open (bracket-pair->open pair))
       (close (bracket-pair->close pair)))
    (implies (and (bidi-scan-ok classes outside st 3)
                  (marks-inside-p originals outside previous-inside)
                  (or (not after-bracket)
                      previous-inside)
                  (natp position)
                  (or (< open position)
                      (not (nth (- open position) outside)))
                  (or (< close position)
                      (not (nth (- close position) outside))))
             (bidi-scan-ok (bidi-n0-set-pair classes
                                             originals
                                             position
                                             pair
                                             direction
                                             after-bracket)
                           outside
                           st
                           3)))
  :induct (set-inside-induction classes originals outside st position
                                pair after-bracket previous-inside)
  :expand ((:free (position after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket))
           (:free (previous-inside)
                  (marks-inside-p originals outside previous-inside))
           (:free (st) (bidi-scan-ok classes outside st 3))
           (:free (a b st) (bidi-scan-ok (cons a b) outside st 3)))
  :enable (set-inside-induction
           bidi-starts-with-mark-p
           acl2::default-cdr
           nth
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0 for one pair.

(defrulel bidi-scan-ok-of-bidi-n0-pair
  (b* ((open (bracket-pair->open pair))
       (close (bracket-pair->close pair)))
    (implies (and (bidi-scan-ok classes outside :free 3)
                  (marks-inside-p originals outside nil)
                  (or (not (nth open outside))
                      (not (equal (bidi-class-kind (nth open classes))
                                  :left-to-right)))
                  (or (nth open outside)
                      (not (nth close outside)))
                  (equal sos (bidi-class-left-to-right))
                  (equal embedding (bidi-class-left-to-right)))
             (bidi-scan-ok (bidi-n0-pair classes originals pair sos embedding)
                           outside
                           :free
                           3)))
  :enable bidi-n0-pair)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule N0 for all the pairs.
; When a pair is treated, the opening brackets outside
; of the pairs that are left still do not have the class L
; (OPENERS-FRESH-P), because the rule changes no position of theirs:
; they are not the two brackets of the pair treated,
; and they are not marks (OPENERS-CLEAR-P, PAIRS-APART-P).

(local
 (define openers-fresh-p ((pairs bracket-pair-listp) classes outside)
   :returns (yes/no booleanp)
   (or (endp pairs)
       (b* ((open (bracket-pair->open (car pairs))))
         (and (or (not (nth open outside))
                  (not (equal (bidi-class-kind (nth open classes))
                              :left-to-right)))
              (openers-fresh-p (cdr pairs) classes outside))))
   :verify-guards nil
   :hooks nil))

(local
 (define openers-clear-p ((pairs bracket-pair-listp)
                          (pair bracket-pair-p)
                          originals)
   :returns (yes/no booleanp)
   (or (endp pairs)
       (b* ((open (bracket-pair->open (car pairs))))
         (and (not (equal open (bracket-pair->open pair)))
              (not (equal open (bracket-pair->close pair)))
              (not (equal (bidi-class-kind (nth open originals))
                          :nonspacing-mark))
              (openers-clear-p (cdr pairs) pair originals))))
   :verify-guards nil
   :hooks nil))

(local
 (define pairs-apart-p ((pairs bracket-pair-listp) originals)
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (openers-clear-p (cdr pairs) (car pairs) originals)
            (pairs-apart-p (cdr pairs) originals)))
   :verify-guards nil
   :hooks nil))

; The rule leaves the class of a position that is not one of the two
; brackets and not a mark.

(local
 (define set-nth-induction ((index natp) classes originals (position natp)
                            pair after-bracket)
   (b* (((when (or (zp index)
                   (endp classes)))
         (list originals after-bracket))
        (position (nfix position))
        (bracket (or (equal position (bracket-pair->open pair))
                     (equal position (bracket-pair->close pair))))
        (mark (and after-bracket
                   (bidi-starts-with-mark-p originals))))
     (set-nth-induction (- index 1)
                        (cdr classes)
                        (cdr originals)
                        (+ 1 position)
                        pair
                        (or bracket mark)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-class-kind-of-nth-of-bidi-n0-set-pair
  (implies (and (natp index)
                (natp position)
                (not (equal (+ position index) (bracket-pair->open pair)))
                (not (equal (+ position index) (bracket-pair->close pair)))
                (not (equal (bidi-class-kind (nth index originals))
                            :nonspacing-mark)))
           (equal (bidi-class-kind
                   (nth index
                        (bidi-n0-set-pair classes
                                          originals
                                          position
                                          pair
                                          direction
                                          after-bracket)))
                  (bidi-class-kind (nth index classes))))
  :induct (set-nth-induction index classes originals position
                             pair after-bracket)
  :expand (:free (position after-bracket)
                 (bidi-n0-set-pair classes
                                   originals
                                   position
                                   pair
                                   direction
                                   after-bracket))
  :enable (set-nth-induction
           bidi-starts-with-mark-p
           acl2::default-car
           acl2::default-cdr
           nth
           nfix))

(defrulel bidi-class-kind-of-nth-of-bidi-n0-pair
  (implies (and (natp index)
                (not (equal index (bracket-pair->open pair)))
                (not (equal index (bracket-pair->close pair)))
                (not (equal (bidi-class-kind (nth index originals))
                            :nonspacing-mark)))
           (equal (bidi-class-kind
                   (nth index
                        (bidi-n0-pair classes originals pair sos embedding)))
                  (bidi-class-kind (nth index classes))))
  :enable bidi-n0-pair)

(defrulel openers-fresh-p-of-bidi-n0-pair
  (implies (and (openers-fresh-p pairs classes outside)
                (openers-clear-p pairs pair originals))
           (openers-fresh-p pairs
                            (bidi-n0-pair classes originals pair sos embedding)
                            outside))
  :induct (list-induction pairs)
  :enable (list-induction
           openers-fresh-p
           openers-clear-p))

(local
 (define n0-pairs-induction (classes originals pairs sos embedding)
   (if (endp pairs)
       classes
     (n0-pairs-induction (bidi-n0-pair classes
                                       originals
                                       (car pairs)
                                       sos
                                       embedding)
                         originals
                         (cdr pairs)
                         sos
                         embedding))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-ok-of-bidi-n0-pairs
  (implies (and (bidi-scan-ok classes outside :free 3)
                (marks-inside-p originals outside nil)
                (bidi-pairs-closed-inside-p pairs outside)
                (openers-fresh-p pairs classes outside)
                (pairs-apart-p pairs originals)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (bidi-scan-ok (bidi-n0-pairs classes originals pairs sos embedding)
                         outside
                         :free
                         3))
  :induct (n0-pairs-induction classes originals pairs sos embedding)
  :expand ((:free (sos embedding)
                  (bidi-n0-pairs classes originals pairs sos embedding))
           (bidi-pairs-closed-inside-p pairs outside)
           (openers-fresh-p pairs classes outside)
           (pairs-apart-p pairs originals))
  :enable n0-pairs-induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The conditions on the pairs hold for the pairs that rule N0 finds.

(defrulel openers-clear-p-when-bidi-pairs-sound-p
  (implies (and (bidi-pairs-sound-p pairs classes roles)
                (not (member-equal (bracket-pair->open pair)
                                   (bidi-pair-opens pairs)))
                (equal (bidi-bracket-role-kind
                        (nth (bracket-pair->close pair) roles))
                       :close))
           (openers-clear-p pairs pair classes))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-sound-p
           bidi-pair-sound-p
           bidi-pair-opens
           openers-clear-p))

(defruledl pairs-apart-p-when-bidi-pairs-sound-p
  (implies (and (bidi-pairs-sound-p pairs classes roles)
                (no-duplicatesp-equal (bidi-pair-opens pairs)))
           (pairs-apart-p pairs classes))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-sound-p
           bidi-pair-sound-p
           bidi-pair-opens
           pairs-apart-p))

(defrulel pairs-apart-p-of-bidi-bracket-pairs
  (pairs-apart-p (bidi-bracket-pairs classes roles) classes)
  :use (:instance pairs-apart-p-when-bidi-pairs-sound-p
                  (pairs (bidi-bracket-pairs classes roles))))

; The pairs are found after rules W1 to W7,
; with the classes that those rules give.
; Every position with a bracket role has the class ON before those rules,
; and so after them; the pairs are the same,
; and their opening brackets have the class ON after the rules.

(local
 (define nth-two-induction ((index natp) x y)
   (if (or (zp index)
           (atom x)
           (atom y))
       nil
     (nth-two-induction (- index 1) (cdr x) (cdr y)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-class-kind-of-nth-when-bidi-roles-neutral-p
  (implies (and (bidi-roles-neutral-p roles classes)
                (equal (bidi-bracket-role-kind (nth index roles)) :open)
                (< (nfix index) (len classes)))
           (equal (bidi-class-kind (nth index classes))
                  :other-neutral))
  :induct (nth-two-induction index roles classes)
  :enable (nth-two-induction
           bidi-roles-neutral-p
           acl2::default-car
           nth
           len
           nfix))

(defrulel index-below-len-when-kind-is-neutral
  (implies (equal (bidi-class-kind (nth index classes)) :other-neutral)
           (< (nfix index) (len classes)))
  :rule-classes :forward-chaining
  :induct (nth index classes)
  :enable (nth len nfix))

(defruledl openers-fresh-p-when-bidi-pairs-sound-p
  (implies (and (bidi-pairs-sound-p pairs classes roles)
                (bidi-roles-neutral-p roles new-classes)
                (equal (len new-classes) (len classes)))
           (openers-fresh-p pairs new-classes outside))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-sound-p
           bidi-pair-sound-p
           openers-fresh-p))

(defrulel openers-fresh-p-of-bidi-bracket-pairs
  (implies (bidi-roles-neutral-p roles classes)
           (openers-fresh-p (bidi-bracket-pairs classes roles)
                            (bidi-resolve-weak-types classes sos)
                            outside))
  :use (:instance openers-fresh-p-when-bidi-pairs-sound-p
                  (pairs (bidi-bracket-pairs classes roles))
                  (new-classes (bidi-resolve-weak-types classes sos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules N1 and N2: every position outside gets the class L.
; In the state :FREE the direction before a neutral is L,
; so the neutral becomes L by rule N1 or by rule N2.
; In a zone the direction after a neutral is L.

(local
 (define outside-left-p ((outside boolean-listp) (classes bidi-class-listp))
   :returns (yes/no booleanp)
   (or (endp classes)
       (and (or (not (car outside))
                (equal (bidi-class-kind (car classes)) :left-to-right))
            (outside-left-p (cdr outside) (cdr classes))))
   :measure (acl2-count classes)
   :hooks nil))

(defrulel bidi-neutral-run-end-in-zone
  (implies (and (bidi-scan-ok classes outside st 3)
                (not (eq st :free))
                (not (eq st :inside))
                (equal eos (bidi-class-left-to-right)))
           (equal (bidi-neutral-run-end classes eos)
                  (bidi-class-left-to-right)))
  :induct (scan-induction classes outside st 3)
  :expand ((:free (st) (bidi-scan-ok classes outside st 3))
           (:free (eos) (bidi-neutral-run-end classes eos)))
  :enable (scan-induction
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction))

(local
 (define neutral-induction (classes outside st previous?)
   (b* (((when (endp classes)) (list outside st previous?))
        (class (bidi-class-fix (car classes))))
     (neutral-induction (cdr classes)
                        (cdr outside)
                        (bidi-scan-step st (car outside) (car classes) 3)
                        (if (bidi-class-neutral-or-isolate-p class)
                            (bidi-class-option-fix previous?)
                          (bidi-class-direction class))))
   :verify-guards nil
   :hooks nil))

(defruledl outside-left-p-of-bidi-n1-n2-lemma
  (implies (and (bidi-scan-ok classes outside st 3)
                (equal left (bidi-class-left-to-right))
                (or (not (eq st :free))
                    (equal previous? left))
                (equal eos left)
                (equal embedding left))
           (outside-left-p outside
                           (bidi-n1-n2 classes previous? eos embedding)))
  :induct (neutral-induction classes outside st previous?)
  :expand ((:free (st) (bidi-scan-ok classes outside st 3))
           (:free (previous? eos embedding)
                  (bidi-n1-n2 classes previous? eos embedding))
           (:free (eos) (bidi-neutral-run-end classes eos))
           (:free (a b) (outside-left-p outside (cons a b))))
  :enable (neutral-induction
           outside-left-p
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction))

(defrulel outside-left-p-of-bidi-n1-n2
  (implies (and (bidi-scan-ok classes outside :free 3)
                (equal previous? (bidi-class-left-to-right))
                (equal eos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (outside-left-p outside
                           (bidi-n1-n2 classes previous? eos embedding)))
  :enable outside-left-p-of-bidi-n1-n2-lemma)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules I1 and I2: at the level 0, the class L gets the level 0.

(local
 (define two-lists-induction (x y)
   (if (consp y)
       (two-lists-induction (cdr x) (cdr y))
     nil)
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-outside-zero-p-of-bidi-implicit-levels
  (implies (outside-left-p outside classes)
           (bidi-outside-zero-p outside (bidi-implicit-levels classes 0)))
  :induct (two-lists-induction outside classes)
  :expand ((bidi-implicit-levels classes 0)
           (:free (a b) (bidi-outside-zero-p outside (cons a b))))
  :enable (two-lists-induction
           outside-left-p
           bidi-outside-zero-p
           bidi-implicit-level))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem of this book.

(defrule bidi-outside-zero-p-of-bidi-resolve-sequence-when-bidi-scan-ok
  (implies (and (bidi-scan-ok classes outside :free 0)
                (bidi-roles-neutral-p roles classes)
                (bidi-pairs-closed-inside-p (bidi-bracket-pairs classes roles)
                                            outside)
                (equal sos (bidi-class-left-to-right))
                (equal eos (bidi-class-left-to-right)))
           (bidi-outside-zero-p
            outside
            (bidi-resolve-sequence classes roles sos eos 0)))
  :enable (bidi-resolve-sequence
           bidi-resolve-neutral-types
           bidi-n0
           bidi-level-direction))
