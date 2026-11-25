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

; This book is a step of the proofs of the theorems of the books
; bidi-guarded-theorem.lisp and bidi-self-contained.lisp,
; which include this book locally.
; See each of the two books for the plan of its proof.
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
; For the second proof, this book also proves that rules N0 to N2,
; and then rules I1 and I2, do in a window
; (see the book bidi-guarded-weak.lisp) what they do to the window alone,
; given the bracket pairs of the sequence that close in the window.
; With the theorem about windows of the book bidi-guarded-weak.lisp,
; this gives the two theorems about windows at the end of this book:
; the levels of a window, before rule L1, depend only on the classes
; of the window and on those bracket pairs.
;
; The definitions of this book are for the proofs only.
; The guards of those that look into a list at a position
; that may be beyond its end are not verified.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definitions that the two books use:
; the first is for the book bidi-guarded-theorem.lisp,
; and the others, about windows, for the book bidi-self-contained.lisp.

; Every pair whose opening bracket is inside has its closing bracket inside.

(define bidi-pairs-closed-inside-p ((pairs bracket-pair-listp)
                                    (outside boolean-listp))
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (or (nth (bracket-pair->open (car pairs)) outside)
               (not (nth (bracket-pair->close (car pairs)) outside)))
           (bidi-pairs-closed-inside-p (cdr pairs) outside)))
  :hooks nil)

; The definitions for windows (see the book bidi-guarded-weak.lisp).

; A pair fits a window, from N and of length M, if:
; its opening bracket is before its closing bracket;
; neither bracket is at the first position of the window;
; if its opening bracket is in the window, its closing bracket is too;
; and if only its closing bracket is in the window,
; its opening bracket is outside.

(define bidi-window-pair-p ((pair bracket-pair-p) (n natp) (m natp) outside)
  :returns (yes/no booleanp)
  (b* (((bracket-pair pair)))
    (and (< pair.open pair.close)
         (not (equal pair.open n))
         (not (equal pair.close n))
         (or (< pair.open n)
             (<= (+ n m) pair.open)
             (< pair.close (+ n m)))
         (or (<= n pair.open)
             (< pair.close n)
             (<= (+ n m) pair.close)
             (and (nth pair.open outside) t))))
  :verify-guards nil
  :hooks nil)

(define bidi-window-pairs-p ((pairs bracket-pair-listp)
                             (n natp)
                             (m natp)
                             outside)
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (bidi-window-pair-p (car pairs) n m outside)
           (bidi-window-pairs-p (cdr pairs) n m outside)))
  :verify-guards nil
  :hooks nil)

; Rule N0 for one pair, on a window alone.
; The window is the part from the position N of a sequence,
; and the pair is a pair of the sequence, with positions in the sequence.
; A pair whose closing bracket is not in the window changes nothing.
; A pair with only its closing bracket in the window
; gets the embedding direction:
; this is what the rule does in the sequence for such a pair
; when its opening bracket is outside.
; For a pair in the window the rule is applied as it is written,
; and the context before the opening bracket is looked for in the window.

(define bidi-n0-pair-in-window ((window bidi-class-listp)
                                (originals bidi-class-listp)
                                (pair bracket-pair-p)
                                (n natp)
                                (sos bidi-class-p)
                                (embedding bidi-class-p))
  :returns (new-window bidi-class-listp)
  (b* (((bracket-pair pair))
       (n (lnfix n))
       (embedding (bidi-class-fix embedding))
       (opposite (if (equal (bidi-class-kind embedding) :left-to-right)
                     (bidi-class-right-to-left)
                   (bidi-class-left-to-right)))
       ((when (or (< pair.close n)
                  (<= (+ n (len window)) pair.close)))
        (bidi-class-list-fix window))
       ((when (< pair.open n))
        (bidi-n0-set-pair window originals n pair embedding nil))
       ((when (bidi-n0-strong-inside-p window n pair embedding))
        (bidi-n0-set-pair window originals n pair embedding nil))
       ((unless (bidi-n0-strong-inside-p window n pair opposite))
        (bidi-class-list-fix window))
       (context (bidi-n0-context window (- pair.open n) sos)))
    (bidi-n0-set-pair window
                      originals
                      n
                      pair
                      (if (equal context opposite)
                          opposite
                        embedding)
                      nil))
  :verify-guards nil
  :hooks nil
  ///
  (defret len-of-bidi-n0-pair-in-window
    (equal (len new-window)
           (len window))))

(define bidi-n0-window ((window bidi-class-listp)
                        (originals bidi-class-listp)
                        (pairs bracket-pair-listp)
                        (n natp)
                        (sos bidi-class-p)
                        (embedding bidi-class-p))
  :returns (new-window bidi-class-listp)
  (if (endp pairs)
      (bidi-class-list-fix window)
    (bidi-n0-window (bidi-n0-pair-in-window window
                                            originals
                                            (car pairs)
                                            n
                                            sos
                                            embedding)
                    originals
                    (cdr pairs)
                    n
                    sos
                    embedding))
  :verify-guards nil
  :hooks nil)

; The levels of a window, from its classes and the pairs of the sequence,
; before rule L1: rules W1 to W7, N0 to N2, I1 and I2 on the window alone,
; with sos = eos = L and the embedding level 0.

(define bidi-window-levels ((window bidi-class-listp)
                            (pairs bracket-pair-listp)
                            (n natp))
  :returns (levels nat-listp)
  (b* ((left (bidi-class-left-to-right))
       (weak (bidi-resolve-weak-types window left))
       (neutral (bidi-n1-n2 (bidi-n0-window weak window pairs n left left)
                            left
                            left
                            left)))
    (bidi-implicit-levels neutral 0))
  :verify-guards nil
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here on, the events are local, except the theorems at the end.

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

; Windows.
;
; The rest of this book proves that rules N0, N1 and N2, and then
; rules I1 and I2, do in a window what the functions for windows,
; defined at the start of this book, do to the window alone.
; See the book bidi-guarded-weak.lisp for what a window is,
; and for rules W1 to W7.

(defrulel natp-and-bound-when-bidi-window-marks-p
  (implies (bidi-window-marks-p n m outside length)
           (and (natp n)
                (posp m)
                (<= (+ n m) length)))
  :rule-classes :forward-chaining
  :enable bidi-window-marks-p)

(local
 (define nthcdr-induction ((k natp) x)
   (if (or (zp k)
           (atom x))
       nil
     (nthcdr-induction (- k 1) (cdr x)))
   :verify-guards nil
   :hooks nil))

(local
 (define position-induction (classes (position natp))
   (if (endp classes)
       position
     (position-induction (cdr classes) (+ 1 (nfix position))))
   :verify-guards nil
   :hooks nil))

(local
 (define take-position-induction ((m natp) classes (position natp))
   (if (or (zp m)
           (endp classes))
       position
     (take-position-induction (- m 1) (cdr classes) (+ 1 (nfix position))))
   :verify-guards nil
   :hooks nil))

;;;;;;;;;;;;;;;;;;;;

; Rule N0, the part that gives a class to the two brackets of a pair
; and to the marks that follow them (BIDI-N0-SET-PAIR), in a window.
; It goes along the list with a flag,
; which is true after a bracket and after the marks that follow it.
; The first position of a window is not a mark, so the flag plays no part.

(defrulel bidi-n0-set-pair-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket)
                  nil))
  :expand (bidi-n0-set-pair classes
                            originals
                            position
                            pair
                            direction
                            after-bracket))

; The flag after K positions.

(local
 (define set-pair-flag ((k natp) classes originals (position natp)
                        pair after-bracket)
   (b* (((when (or (zp k)
                   (endp classes)))
         after-bracket)
        (position (nfix position))
        (bracket (or (equal position (bracket-pair->open pair))
                     (equal position (bracket-pair->close pair))))
        (mark (and after-bracket
                   (bidi-starts-with-mark-p originals))))
     (set-pair-flag (- k 1)
                    (cdr classes)
                    (cdr originals)
                    (+ 1 position)
                    pair
                    (or bracket mark)))
   :verify-guards nil
   :hooks nil))

(defrulel nthcdr-of-bidi-n0-set-pair
  (implies (and (natp position)
                (bidi-class-listp originals))
           (equal (nthcdr k
                          (bidi-n0-set-pair classes
                                            originals
                                            position
                                            pair
                                            direction
                                            after-bracket))
                  (bidi-n0-set-pair (nthcdr k classes)
                                    (nthcdr k originals)
                                    (+ position (nfix k))
                                    pair
                                    direction
                                    (set-pair-flag k
                                                   classes
                                                   originals
                                                   position
                                                   pair
                                                   after-bracket))))
  :induct (set-pair-flag k classes originals position pair after-bracket)
  :expand ((:free (position after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket)))
  :enable (set-pair-flag nthcdr nfix))

(defruledl bidi-n0-set-pair-when-not-mark
  (implies (and (syntaxp (not (equal after-bracket ''nil)))
                (not (bidi-starts-with-mark-p originals)))
           (equal (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    nil)))
  :expand ((:free (after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket))))

(local
 (define set-pair-take-induction ((m natp) classes originals (position natp)
                                  pair after-bracket)
   (b* (((when (or (zp m)
                   (endp classes)))
         (list originals after-bracket))
        (position (nfix position))
        (bracket (or (equal position (bracket-pair->open pair))
                     (equal position (bracket-pair->close pair))))
        (mark (and after-bracket
                   (bidi-starts-with-mark-p originals))))
     (set-pair-take-induction (- m 1)
                              (cdr classes)
                              (cdr originals)
                              (+ 1 position)
                              pair
                              (or bracket mark)))
   :verify-guards nil
   :hooks nil))

(defrulel take-of-bidi-n0-set-pair
  (implies (and (<= (nfix m) (len classes))
                (<= (nfix m) (len originals))
                (bidi-class-listp originals))
           (equal (take m
                        (bidi-n0-set-pair classes
                                          originals
                                          position
                                          pair
                                          direction
                                          after-bracket))
                  (bidi-n0-set-pair (take m classes)
                                    (take m originals)
                                    position
                                    pair
                                    direction
                                    after-bracket)))
  :induct (set-pair-take-induction m classes originals position
                                   pair after-bracket)
  :expand ((:free (position after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket))
           (:free (a b c position after-bracket)
                  (bidi-n0-set-pair (cons a b)
                                    c
                                    position
                                    pair
                                    direction
                                    after-bracket)))
  :enable (set-pair-take-induction
           bidi-starts-with-mark-p
           take
           len
           nfix))

; A list with neither bracket of the pair is left as it is.

(local
 (define set-pair-induction (classes originals (position natp))
   (if (endp classes)
       (list originals position)
     (set-pair-induction (cdr classes)
                         (cdr originals)
                         (+ 1 (nfix position))))
   :verify-guards nil
   :hooks nil))

(defruledl bidi-n0-set-pair-when-no-bracket-ahead
  (implies (and (not after-bracket)
                (natp position)
                (or (< (bracket-pair->open pair) position)
                    (<= (+ position (len classes))
                        (bracket-pair->open pair)))
                (or (< (bracket-pair->close pair) position)
                    (<= (+ position (len classes))
                        (bracket-pair->close pair))))
           (equal (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket)
                  (bidi-class-list-fix classes)))
  :induct (set-pair-induction classes originals position)
  :expand ((:free (position)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    nil)))
  :enable (set-pair-induction
           bidi-class-list-fix
           acl2::default-cdr
           len
           nfix))

; The pair and the position moved together.

(local
 (define set-pair-shift-induction (classes originals (position natp)
                                           (offset natp) pair after-bracket)
   (b* (((when (endp classes)) (list originals after-bracket))
        (position (nfix position))
        (bracket (or (equal (- position (nfix offset))
                            (bracket-pair->open pair))
                     (equal (- position (nfix offset))
                            (bracket-pair->close pair))))
        (mark (and after-bracket
                   (bidi-starts-with-mark-p originals))))
     (set-pair-shift-induction (cdr classes)
                               (cdr originals)
                               (+ 1 position)
                               offset
                               pair
                               (or bracket mark)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n0-set-pair-of-bidi-pair-shift
  (implies (and (natp offset)
                (natp position)
                (<= offset position)
                (bidi-class-listp originals))
           (equal (bidi-n0-set-pair classes
                                    originals
                                    position
                                    (bidi-pair-shift pair offset)
                                    direction
                                    after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    (- position offset)
                                    pair
                                    direction
                                    after-bracket)))
  :induct (set-pair-shift-induction classes originals position offset
                                    pair after-bracket)
  :expand ((:free (position pair after-bracket)
                  (bidi-n0-set-pair classes
                                    originals
                                    position
                                    pair
                                    direction
                                    after-bracket)))
  :enable (set-pair-shift-induction nfix))

(defruledl bidi-window-of-bidi-n0-set-pair
  (implies (and (bidi-class-listp originals)
                (equal (len originals) (len classes))
                (natp n)
                (natp m)
                (<= (+ n m) (len classes))
                (not (equal (bidi-class-kind (nth n originals))
                            :nonspacing-mark)))
           (equal (bidi-window n m outside
                               (bidi-n0-set-pair classes
                                                 originals
                                                 0
                                                 pair
                                                 direction
                                                 nil))
                  (bidi-n0-set-pair (bidi-window n m outside classes)
                                    (bidi-window n m outside originals)
                                    n
                                    pair
                                    direction
                                    nil)))
  :enable (bidi-window
           bidi-n0-set-pair-when-not-mark
           bidi-starts-with-mark-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule N0, the search for a strong class inside a pair, in a window.

(defrulel bidi-n0-strong-inside-p-when-past-close
  (implies (<= (bracket-pair->close pair) (nfix position))
           (not (bidi-n0-strong-inside-p classes position pair direction)))
  :expand (bidi-n0-strong-inside-p classes position pair direction)
  :enable nfix)

(defrulel bidi-n0-strong-inside-p-when-not-consp
  (implies (not (consp classes))
           (not (bidi-n0-strong-inside-p classes position pair direction)))
  :expand (bidi-n0-strong-inside-p classes position pair direction))

(defrulel bidi-n0-strong-inside-p-of-take
  (implies (and (natp position)
                (<= (nfix m) (len classes))
                (<= (bracket-pair->close pair) (+ position (nfix m))))
           (equal (bidi-n0-strong-inside-p (take m classes)
                                           position
                                           pair
                                           direction)
                  (bidi-n0-strong-inside-p classes position pair direction)))
  :induct (take-position-induction m classes position)
  :expand ((:free (position)
                  (bidi-n0-strong-inside-p classes position pair direction))
           (:free (a b position)
                  (bidi-n0-strong-inside-p (cons a b)
                                           position
                                           pair
                                           direction)))
  :enable (take-position-induction take len nfix))

(defrulel bidi-n0-strong-inside-p-of-nthcdr
  (implies (and (natp k)
                (natp position)
                (<= k position)
                (<= position (+ 1 (bracket-pair->open pair))))
           (equal (bidi-n0-strong-inside-p (nthcdr k classes)
                                           position
                                           pair
                                           direction)
                  (bidi-n0-strong-inside-p classes
                                           (- position k)
                                           pair
                                           direction)))
  :induct (nthcdr-induction k classes)
  :expand ((:free (position)
                  (bidi-n0-strong-inside-p classes position pair direction)))
  :enable (nthcdr-induction nthcdr nfix))

(defrulel bidi-n0-strong-inside-p-of-bidi-pair-shift
  (implies (and (natp offset)
                (natp position)
                (<= offset position))
           (equal (bidi-n0-strong-inside-p classes
                                           position
                                           (bidi-pair-shift pair offset)
                                           direction)
                  (bidi-n0-strong-inside-p classes
                                           (- position offset)
                                           pair
                                           direction)))
  :induct (position-induction classes position)
  :expand ((:free (position pair)
                  (bidi-n0-strong-inside-p classes position pair direction)))
  :enable (position-induction nfix))

(defruledl bidi-n0-strong-inside-p-when-direction-inside
  (implies (and (natp position)
                (natp j)
                (<= position j)
                (< (bracket-pair->open pair) j)
                (< j (bracket-pair->close pair))
                (< (- j position) (len classes))
                (equal (bidi-class-direction (nth (- j position) classes))
                       (bidi-class-fix direction)))
           (bidi-n0-strong-inside-p classes position pair direction))
  :induct (position-induction classes position)
  :expand ((:free (position)
                  (bidi-n0-strong-inside-p classes position pair direction)))
  :enable (position-induction nth len nfix))

(defrulel bidi-n0-strong-inside-p-of-bidi-window
  (implies (and (natp n)
                (natp m)
                (<= (+ n m) (len classes))
                (<= n (bracket-pair->open pair))
                (<= (bracket-pair->close pair) (+ n m)))
           (equal (bidi-n0-strong-inside-p (bidi-window n m outside classes)
                                           n
                                           pair
                                           direction)
                  (bidi-n0-strong-inside-p classes 0 pair direction)))
  :enable (bidi-window nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule N0, the context before the opening bracket of a pair, in a window.
; The first class of a window has a direction,
; so the context of a bracket in the window is found in the window.

(local
 (define context-take-induction ((m natp) classes (count natp) direction)
   (if (or (zp m)
           (endp classes)
           (zp count))
       direction
     (context-take-induction (- m 1)
                             (cdr classes)
                             (- count 1)
                             (or (bidi-class-direction (car classes))
                                 direction)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n0-context-when-zp
  (implies (zp count)
           (equal (bidi-n0-context classes count direction)
                  (bidi-class-fix direction)))
  :expand (bidi-n0-context classes count direction)
  :enable nfix)

(defrulel bidi-n0-context-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-n0-context classes count direction)
                  (bidi-class-fix direction)))
  :expand (bidi-n0-context classes count direction))

(defrulel bidi-n0-context-of-take
  (implies (and (<= (nfix count) (nfix m))
                (<= (nfix m) (len classes)))
           (equal (bidi-n0-context (take m classes) count direction)
                  (bidi-n0-context classes count direction)))
  :induct (context-take-induction m classes count direction)
  :expand ((:free (direction)
                  (bidi-n0-context classes count direction))
           (:free (a b direction)
                  (bidi-n0-context (cons a b) count direction))
           (:free (direction)
                  (bidi-n0-context nil count direction)))
  :enable (context-take-induction take len nfix))

(local
 (define context-nthcdr-induction ((k natp) classes direction)
   (if (or (zp k)
           (endp classes))
       direction
     (context-nthcdr-induction (- k 1)
                               (cdr classes)
                               (or (bidi-class-direction (car classes))
                                   direction)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n0-context-of-nthcdr-lemma
  (implies (and (natp k)
                (posp count)
                (< k (len classes))
                (bidi-class-direction (nth k classes)))
           (equal (bidi-n0-context (nthcdr k classes) count direction2)
                  (bidi-n0-context classes (+ count k) direction)))
  :rule-classes nil
  :induct (context-nthcdr-induction k classes direction)
  :expand ((:free (count direction)
                  (bidi-n0-context classes count direction)))
  :enable (context-nthcdr-induction nthcdr nth len nfix))

(defrulel bidi-n0-context-of-nthcdr
  (implies (and (natp k)
                (posp count)
                (< k (len classes))
                (bidi-class-direction (nth k classes)))
           (equal (bidi-n0-context (nthcdr k classes) count direction)
                  (bidi-n0-context classes (+ count k) direction)))
  :use (:instance bidi-n0-context-of-nthcdr-lemma (direction2 direction)))

(defrulel bidi-n0-context-of-bidi-window
  (implies (and (natp n)
                (natp m)
                (posp count)
                (<= count m)
                (<= (+ n m) (len classes))
                (bidi-class-direction (nth n classes)))
           (equal (bidi-n0-context (bidi-window n m outside classes)
                                   count
                                   direction)
                  (bidi-n0-context classes (+ count n) direction)))
  :enable (bidi-window nfix))

;;;;;;;;;;;;;;;;;;;;

; Rule N0 for one pair, in a window.
; For a pair with only its closing bracket in the window,
; the first position of the window is between the two brackets
; and has the direction R; the opening bracket is outside,
; and so the rule gives the pair the class L (see above).

(defrulel bidi-window-of-bidi-n0-pair
  (b* ((open (bracket-pair->open pair)))
    (implies (and (bidi-class-listp classes)
                  (bidi-class-listp originals)
                  (equal (len originals) (len classes))
                  (bidi-scan-ok classes outside :free 3)
                  (bidi-window-marks-p n m outside (len classes))
                  (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
                  (not (equal (bidi-class-kind (nth n classes))
                              :arabic-letter))
                  (bidi-window-start-kind-p
                   (bidi-class-kind (nth n originals)))
                  (bidi-window-pair-p pair n m outside)
                  (or (not (nth open outside))
                      (not (equal (bidi-class-kind (nth open classes))
                                  :left-to-right)))
                  (equal sos (bidi-class-left-to-right))
                  (equal embedding (bidi-class-left-to-right)))
             (equal (bidi-window n m outside
                                 (bidi-n0-pair classes
                                               originals
                                               pair
                                               sos
                                               embedding))
                    (bidi-n0-pair-in-window (bidi-window n m outside classes)
                                            (bidi-window n m outside originals)
                                            pair
                                            n
                                            sos
                                            embedding))))
  :use (:instance bidi-n0-strong-inside-p-when-direction-inside
                  (j n)
                  (position 0)
                  (direction (bidi-class-right-to-left)))
  :enable (bidi-n0-pair
           bidi-n0-pair-in-window
           bidi-window-pair-p
           bidi-window-start-kind-p
           bidi-window-of-bidi-n0-set-pair
           bidi-n0-set-pair-when-no-bracket-ahead
           bidi-class-direction
           nfix))

; The first class of a window stays under rule N0.

(defrulel bidi-class-kind-of-nth-of-bidi-n0-pairs
  (implies (and (bidi-window-pairs-p pairs n m outside)
                (natp n)
                (not (equal (bidi-class-kind (nth n originals))
                            :nonspacing-mark)))
           (equal (bidi-class-kind
                   (nth n
                        (bidi-n0-pairs classes originals pairs sos embedding)))
                  (bidi-class-kind (nth n classes))))
  :induct (n0-pairs-induction classes originals pairs sos embedding)
  :expand ((:free (sos embedding)
                  (bidi-n0-pairs classes originals pairs sos embedding))
           (bidi-window-pairs-p pairs n m outside))
  :enable (n0-pairs-induction
           bidi-window-pair-p))

; Rule N0 for all the pairs, in a window.

(defrulel bidi-window-of-bidi-n0-pairs
  (implies (and (bidi-class-listp classes)
                (bidi-class-listp originals)
                (equal (len originals) (len classes))
                (bidi-scan-ok classes outside :free 3)
                (marks-inside-p originals outside nil)
                (bidi-pairs-closed-inside-p pairs outside)
                (openers-fresh-p pairs classes outside)
                (pairs-apart-p pairs originals)
                (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
                (not (equal (bidi-class-kind (nth n classes))
                            :arabic-letter))
                (bidi-window-start-kind-p (bidi-class-kind (nth n originals)))
                (bidi-window-pairs-p pairs n m outside)
                (equal sos (bidi-class-left-to-right))
                (equal embedding (bidi-class-left-to-right)))
           (equal (bidi-window n m outside
                               (bidi-n0-pairs classes
                                              originals
                                              pairs
                                              sos
                                              embedding))
                  (bidi-n0-window (bidi-window n m outside classes)
                                  (bidi-window n m outside originals)
                                  pairs
                                  n
                                  sos
                                  embedding)))
  :induct (n0-pairs-induction classes originals pairs sos embedding)
  :expand ((:free (sos embedding)
                  (bidi-n0-pairs classes originals pairs sos embedding))
           (:free (window originals sos embedding)
                  (bidi-n0-window window originals pairs n sos embedding))
           (bidi-pairs-closed-inside-p pairs outside)
           (openers-fresh-p pairs classes outside)
           (pairs-apart-p pairs originals)
           (bidi-window-pairs-p pairs n m outside))
  :enable (n0-pairs-induction
           bidi-window-pair-p
           bidi-window-start-kind-p))

;;;;;;;;;;;;;;;;;;;;

; The function for rule N0 on a window uses only the pairs
; whose closing bracket is in the window,
; and gives the same result when the pairs and the start of the window
; are moved together.

(defrulel bidi-n0-pair-in-window-of-bidi-pair-shift
  (implies (and (natp offset)
                (natp n)
                (<= offset n)
                (bidi-class-listp originals))
           (equal (bidi-n0-pair-in-window window
                                          originals
                                          (bidi-pair-shift pair offset)
                                          n
                                          sos
                                          embedding)
                  (bidi-n0-pair-in-window window
                                          originals
                                          pair
                                          (- n offset)
                                          sos
                                          embedding)))
  :enable (bidi-n0-pair-in-window nfix))

(defruledl bidi-n0-window-of-bidi-pairs-shift
  (implies (and (natp offset)
                (natp n)
                (bidi-class-listp originals))
           (equal (bidi-n0-window window
                                  originals
                                  (bidi-pairs-shift pairs offset)
                                  (+ n offset)
                                  sos
                                  embedding)
                  (bidi-n0-window window originals pairs n sos embedding)))
  :induct (bidi-n0-window window originals pairs n sos embedding)
  :expand ((:free (n)
                  (bidi-n0-window window
                                  originals
                                  (bidi-pairs-shift pairs offset)
                                  n
                                  sos
                                  embedding))
           (bidi-pairs-shift pairs offset))
  :enable bidi-n0-window)

(defruledl bidi-n0-window-of-bidi-pairs-closing-in
  (implies (and (bidi-class-listp window)
                (natp n)
                (equal end (+ n (len window))))
           (equal (bidi-n0-window window
                                  originals
                                  (bidi-pairs-closing-in pairs n end)
                                  n
                                  sos
                                  embedding)
                  (bidi-n0-window window originals pairs n sos embedding)))
  :induct (bidi-n0-window window originals pairs n sos embedding)
  :expand ((:free (end) (bidi-pairs-closing-in pairs n end))
           (:free (window a b)
                  (bidi-n0-window window
                                  originals
                                  (cons a b)
                                  n
                                  sos
                                  embedding)))
  :enable (bidi-n0-window
           bidi-n0-pair-in-window
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rules N1 and N2 in a window.
; The first class of a window is not that of a neutral,
; so the direction before the window plays no part.
; The neutrals at the end of a window are followed by a zone,
; whose end has the direction L, the one of eos.

(local
 (define n1-state ((k natp) classes previous?)
   (b* (((when (or (zp k)
                   (endp classes)))
         previous?)
        (class (bidi-class-fix (car classes))))
     (n1-state (- k 1)
               (cdr classes)
               (if (bidi-class-neutral-or-isolate-p class)
                   (bidi-class-option-fix previous?)
                 (bidi-class-direction class))))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-n1-n2-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-n1-n2 classes previous? eos embedding)
                  nil))
  :expand (bidi-n1-n2 classes previous? eos embedding))

(defrulel nthcdr-of-bidi-n1-n2
  (equal (nthcdr k (bidi-n1-n2 classes previous? eos embedding))
         (bidi-n1-n2 (nthcdr k classes)
                     (n1-state k classes previous?)
                     eos
                     embedding))
  :induct (n1-state k classes previous?)
  :expand ((:free (previous?)
                  (bidi-n1-n2 classes previous? eos embedding)))
  :enable (n1-state nthcdr))

(defrulel bidi-n1-n2-of-n1-state
  (implies (and (consp classes)
                (not (bidi-class-neutral-or-isolate-p (car classes))))
           (equal (bidi-n1-n2 classes
                              (n1-state k other previous?)
                              eos
                              embedding)
                  (bidi-n1-n2 classes previous? eos embedding)))
  :expand ((:free (previous?)
                  (bidi-n1-n2 classes previous? eos embedding))))

(defrulel bidi-neutral-run-end-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-neutral-run-end classes eos)
                  (bidi-class-fix eos)))
  :expand (bidi-neutral-run-end classes eos))

(defrulel bidi-neutral-run-end-of-take
  (implies (and (<= (nfix m) (len classes))
                (equal (bidi-neutral-run-end (nthcdr m classes) eos)
                       (bidi-class-fix eos)))
           (equal (bidi-neutral-run-end (take m classes) eos)
                  (bidi-neutral-run-end classes eos)))
  :induct (nthcdr-induction m classes)
  :expand ((bidi-neutral-run-end classes eos)
           (:free (a b) (bidi-neutral-run-end (cons a b) eos)))
  :enable (nthcdr-induction take nthcdr len nfix))

(defrulel take-of-bidi-n1-n2
  (implies (and (<= (nfix m) (len classes))
                (equal (bidi-neutral-run-end (nthcdr m classes) eos)
                       (bidi-class-fix eos)))
           (equal (take m (bidi-n1-n2 classes previous? eos embedding))
                  (bidi-n1-n2 (take m classes) previous? eos embedding)))
  :induct (n1-state m classes previous?)
  :expand ((:free (previous?)
                  (bidi-n1-n2 classes previous? eos embedding))
           (:free (previous?)
                  (bidi-n1-n2 (take m classes) previous? eos embedding)))
  :enable (n1-state nthcdr len nfix))

; After a position inside, the neutrals go on up to an L or the end.

(defrulel bidi-neutral-run-end-after-inside
  (implies (and (bidi-scan-ok classes outside :inside 3)
                (car outside)
                (equal eos (bidi-class-left-to-right)))
           (equal (bidi-neutral-run-end classes eos)
                  (bidi-class-left-to-right)))
  :expand ((bidi-scan-ok classes outside :inside 3)
           (:free (eos) (bidi-neutral-run-end classes eos)))
  :enable (bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           bidi-class-direction))

(local
 (define scan-nthcdr-induction ((j natp) classes outside st)
   (if (or (zp j)
           (endp classes))
       st
     (scan-nthcdr-induction (- j 1)
                            (cdr classes)
                            (cdr outside)
                            (bidi-scan-step st
                                            (car outside)
                                            (car classes)
                                            3)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-neutral-run-end-after-window
  (implies (and (bidi-scan-ok classes outside st 3)
                (posp j)
                (< j (len classes))
                (not (nth (- j 1) outside))
                (nth j outside)
                (equal eos (bidi-class-left-to-right)))
           (equal (bidi-neutral-run-end (nthcdr j classes) eos)
                  (bidi-class-left-to-right)))
  :induct (scan-nthcdr-induction j classes outside st)
  :expand ((:free (st) (bidi-scan-ok classes outside st 3)))
  :enable (scan-nthcdr-induction
           nthcdr
           nth
           len
           bidi-scan-step-when-inside-position)
  :disable bidi-scan-step)

(defrulel bidi-window-of-bidi-n1-n2
  (implies (and (bidi-scan-ok classes outside :free 3)
                (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
                (equal eos (bidi-class-left-to-right)))
           (equal (bidi-window n m outside
                               (bidi-n1-n2 classes previous? eos embedding))
                  (bidi-n1-n2 (bidi-window n m outside classes)
                              previous?
                              eos
                              embedding)))
  :cases ((equal (+ n m) (len classes)))
  :enable (bidi-window
           bidi-window-marks-p
           bidi-window-start-kind-p
           bidi-class-neutral-or-isolate-p
           bidi-class-neutral-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           nfix))

;;;;;;;;;;;;;;;;;;;;

; Rules I1 and I2 in a window.

(defrulel nthcdr-of-bidi-implicit-levels
  (equal (nthcdr k (bidi-implicit-levels classes level))
         (bidi-implicit-levels (nthcdr k classes) level))
  :induct (nthcdr-induction k classes)
  :expand ((bidi-implicit-levels classes level)
           (bidi-implicit-levels nil level))
  :enable (nthcdr-induction nthcdr))

(defrulel take-of-bidi-implicit-levels
  (implies (<= (nfix m) (len classes))
           (equal (take m (bidi-implicit-levels classes level))
                  (bidi-implicit-levels (take m classes) level)))
  :induct (nthcdr-induction m classes)
  :expand ((bidi-implicit-levels classes level)
           (bidi-implicit-levels nil level)
           (:free (a b) (bidi-implicit-levels (cons a b) level)))
  :enable (nthcdr-induction take len nfix))

(defrulel bidi-window-of-bidi-implicit-levels
  (implies (and (natp n)
                (natp m)
                (<= (+ n m) (len classes)))
           (equal (bidi-window n m outside
                               (bidi-implicit-levels classes level))
                  (bidi-implicit-levels (bidi-window n m outside classes)
                                        level)))
  :enable (bidi-window nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem of this book for the first proof.

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

; The theorems about windows.

; The levels of a window, before rule L1, are those that
; BIDI-WINDOW-LEVELS gives from the classes of the window
; and the bracket pairs of the sequence.

(defruled bidi-window-of-bidi-resolve-sequence
  (implies (and (bidi-class-listp classes)
                (bidi-scan-ok classes outside :free 0)
                (bidi-roles-neutral-p roles classes)
                (bidi-pairs-closed-inside-p (bidi-bracket-pairs classes roles)
                                            outside)
                (bidi-window-marks-p n m outside (len classes))
                (bidi-window-start-kind-p (bidi-class-kind (nth n classes)))
                (bidi-window-pairs-p (bidi-bracket-pairs classes roles)
                                     n
                                     m
                                     outside)
                (equal sos (bidi-class-left-to-right))
                (equal eos (bidi-class-left-to-right)))
           (equal (bidi-window n m outside
                               (bidi-resolve-sequence classes roles sos eos 0))
                  (bidi-window-levels (bidi-window n m outside classes)
                                      (bidi-bracket-pairs classes roles)
                                      n)))
  :enable (bidi-resolve-sequence
           bidi-resolve-neutral-types
           bidi-n0
           bidi-level-direction
           bidi-window-levels
           bidi-window-of-bidi-resolve-weak-types
           bidi-window-start-kind-p-of-nth-of-bidi-resolve-weak-types)
  :expand ((bidi-window-start-kind-p (bidi-class-kind (nth n classes)))))

; Two lists of pairs give a window the same levels
; if those of their pairs that close in the window
; are the same, up to a move by a number of positions.

(defruled bidi-window-levels-of-same-pairs-in-window
  (implies (and (bidi-class-listp window)
                (natp n)
                (natp offset)
                (equal (bidi-pairs-closing-in pairs1
                                              (+ n offset)
                                              (+ n offset (len window)))
                       (bidi-pairs-shift
                        (bidi-pairs-closing-in pairs2 n (+ n (len window)))
                        offset)))
           (equal (bidi-window-levels window pairs1 (+ n offset))
                  (bidi-window-levels window pairs2 n)))
  :enable bidi-window-levels
  :use ((:instance bidi-n0-window-of-bidi-pairs-closing-in
                   (window (bidi-resolve-weak-types
                            window
                            (bidi-class-left-to-right)))
                   (originals window)
                   (pairs pairs1)
                   (n (+ n offset))
                   (end (+ n offset (len window)))
                   (sos (bidi-class-left-to-right))
                   (embedding (bidi-class-left-to-right)))
        (:instance bidi-n0-window-of-bidi-pairs-closing-in
                   (window (bidi-resolve-weak-types
                            window
                            (bidi-class-left-to-right)))
                   (originals window)
                   (pairs pairs2)
                   (end (+ n (len window)))
                   (sos (bidi-class-left-to-right))
                   (embedding (bidi-class-left-to-right)))
        (:instance bidi-n0-window-of-bidi-pairs-shift
                   (window (bidi-resolve-weak-types
                            window
                            (bidi-class-left-to-right)))
                   (originals window)
                   (pairs (bidi-pairs-closing-in pairs2
                                                 n
                                                 (+ n (len window))))
                   (sos (bidi-class-left-to-right))
                   (embedding (bidi-class-left-to-right)))))
