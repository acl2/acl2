; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-confinement")

(local (include-book "bidi-guarded-neutral"))

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book proves that a plain text whose segments are guarded
; is confined: see the section at the end of the book.
; Everything before that section is local.
;
; The plan of the proof.
;
; 1. Mark each position of the text as outside or inside.
;    In each segment, the positions before the first character
;    of class R, AL or AN are outside,
;    and that character and the rest of the segment are inside.
;    So a segment that is not right-to-left is all outside.
;    The marks are a list of booleans, called OUTSIDE, with T for outside.
;
; 2. The scan (book bidi-guarded-weak.lisp) is a condition
;    on the classes of the positions outside.
;    The conditions on the segments make the scan succeed
;    on the classes of the characters (this book).
;
; 3. A plain text at the paragraph embedding level 0
;    is one isolating run sequence with sos = eos = L,
;    and rule L1 only lowers levels to 0 (book bidi-guarded-plain.lisp).
;
; 4. Rules W1 to W7 keep the scan (book bidi-guarded-weak.lisp).
;    Rule N0 keeps it too, if every bracket pair
;    whose opening bracket is inside has its closing bracket inside,
;    which the third condition on the segments gives (this book);
;    this uses facts about the bracket pairs
;    (book bidi-guarded-brackets.lisp).
;    After rules N1 and N2 every position outside has the class L,
;    and so gets the level 0 (book bidi-guarded-neutral.lisp).
;
; 5. At each cut between two segments, the position before the cut
;    or the position after it is outside, and so has the level 0:
;    the cut is clean (this book).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :enable fix)

(defrulel nfix-of-len
  (equal (nfix (len x))
         (len x))
  :enable nfix)

(local
 (define list-induction (x)
   (if (consp x)
       (list-induction (cdr x))
     nil)
   :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The classes of the characters of a list of code points.

(local
 (define cp-classes ((cps code-point-listp) (ver versionp))
   :returns (classes bidi-class-listp)
   (if (endp cps)
       nil
     (cons (code-point-bidi-class (car cps) ver)
           (cp-classes (cdr cps) ver)))
   :hooks nil
   ///
   (defret len-of-cp-classes
     (equal (len classes)
            (len cps))
     :hints (("Goal" :induct t :in-theory (enable len))))))

(defrulel bidi-char-list-classes-of-code-points-to-bidi-chars
  (equal (bidi-char-list-classes (code-points-to-bidi-chars cps ver))
         (cp-classes cps ver))
  :induct (list-induction cps)
  :enable (list-induction
           cp-classes
           bidi-char-list-classes
           code-points-to-bidi-chars
           code-point-bidi-char))

(defrulel cp-classes-when-not-consp
  (implies (not (consp cps))
           (equal (cp-classes cps ver)
                  nil))
  :expand (cp-classes cps ver))

(defrulel cp-classes-of-append
  (equal (cp-classes (append x y) ver)
         (append (cp-classes x ver)
                 (cp-classes y ver)))
  :induct (list-induction x)
  :enable (list-induction cp-classes))

(defrulel bidi-plain-class-listp-of-cp-classes
  (implies (bidi-plain-p cps ver)
           (bidi-plain-class-listp (cp-classes cps ver)))
  :induct (list-induction cps)
  :enable (list-induction
           cp-classes
           bidi-plain-code-point-p
           bidi-plain-class-p))

; Every paired bracket has the class ON.

(defrulel bidi-roles-neutral-p-of-code-points-to-bidi-chars
  (bidi-roles-neutral-p (bidi-char-list-brackets
                         (code-points-to-bidi-chars cps ver))
                        (cp-classes cps ver))
  :induct (list-induction cps)
  :enable (list-induction
           cp-classes
           bidi-roles-neutral-p
           bidi-char-list-brackets
           code-points-to-bidi-chars
           code-point-bidi-char))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The marks of a segment, and of the text.
; The argument INSIDE of the first function says
; whether a character of class R, AL or AN has been passed.

(local
 (define segment-outside ((cps code-point-listp) (ver versionp) inside)
   :returns (outside boolean-listp)
   (b* (((when (endp cps)) nil)
        (inside (or (and inside t)
                    (right-to-left-code-point-p (car cps) ver))))
     (cons (not inside)
           (segment-outside (cdr cps) ver inside)))
   :hooks nil
   ///
   (defret len-of-segment-outside
     (equal (len outside)
            (len cps))
     :hints (("Goal" :induct t :in-theory (enable len))))))

(local
 (define segments-outside ((segments code-point-list-listp) (ver versionp))
   :returns (outside true-listp)
   (if (endp segments)
       nil
     (append (segment-outside (car segments) ver nil)
             (segments-outside (cdr segments) ver)))
   :hooks nil
   ///
   (defret len-of-segments-outside
     (equal (len outside)
            (len (acl2::flatten segments)))
     :hints (("Goal" :induct t :in-theory (enable len acl2::flatten))))))

; Inside, every mark is NIL.

(defrulel nth-of-segment-outside-when-inside
  (not (nth index (segment-outside cps ver t)))
  :induct (nth index cps)
  :expand (segment-outside cps ver t)
  :enable nth)

; A segment without a character of class R, AL or AN is all outside.

(defrulel nth-of-segment-outside-when-right-to-left-free-p
  (implies (and (right-to-left-free-p cps ver)
                (< (nfix index) (len cps)))
           (nth index (segment-outside cps ver nil)))
  :induct (nth index cps)
  :expand (segment-outside cps ver nil)
  :enable (nth len nfix))

; After a position inside, the rest of the segment is inside.

(local
 (define nth-nth-induction ((i natp) (j natp) cps ver inside)
   (if (or (zp i)
           (zp j)
           (atom cps))
       (list ver inside)
     (nth-nth-induction (- i 1)
                        (- j 1)
                        (cdr cps)
                        ver
                        (or (and inside t)
                            (right-to-left-code-point-p (car cps) ver))))
   :verify-guards nil
   :hooks nil))

(defrulel nth-of-segment-outside-after-inside
  (implies (and (not (nth i (segment-outside cps ver inside)))
                (<= (nfix i) (nfix j)))
           (not (nth j (segment-outside cps ver inside))))
  :induct (nth-nth-induction i j cps ver inside)
  :expand ((:free (inside) (segment-outside cps ver inside)))
  :enable (nth-nth-induction nth nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The scan of the text.

; The scan of two lists one after the other.

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

(defrulel bidi-scan-ok-of-append
  (implies (and (equal (len outside1) (len classes1))
                st)
           (equal (bidi-scan-ok (append classes1 classes2)
                                (append outside1 outside2)
                                st
                                phase)
                  (and (bidi-scan-end classes1 outside1 st phase)
                       (bidi-scan-ok classes2
                                     outside2
                                     (bidi-scan-end classes1 outside1 st phase)
                                     phase))))
  :induct (scan-induction classes1 outside1 st phase)
  :expand ((append classes1 classes2)
           (append outside1 outside2)
           (:free (a b o st) (bidi-scan-ok (cons a b) o st phase))
           (bidi-scan-end classes1 outside1 st phase))
  :enable (scan-induction len))

; What the scan needs of the text that is left, for each state:
; nothing in the state :FREE;
; after a position inside, that the text turns left-to-right
; and does not attach to what is before;
; in a zone, that the text turns left-to-right.

(local
 (define scan-invariant (st (rest code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (cond ((eq st :free) t)
         ((eq st :inside) (and (bidi-turns-left-to-right-p rest ver)
                               (not (bidi-attaches-p rest ver))))
         ((eq st :zone) (bidi-turns-left-to-right-p rest ver))
         (t nil))
   :hooks nil))

; The scan of the part of a segment that is inside.

(local
 (define inside-induction (cps st)
   (if (endp cps)
       st
     (inside-induction (cdr cps) :inside))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-end-of-segment-outside-when-inside
  (implies (or (eq st :free)
               (eq st :inside))
           (equal (bidi-scan-end (cp-classes cps ver)
                                 (segment-outside cps ver t)
                                 st
                                 0)
                  (if (consp cps)
                      :inside
                    st)))
  :induct (inside-induction cps st)
  :expand ((cp-classes cps ver)
           (segment-outside cps ver t)
           (:free (a b o st) (bidi-scan-end (cons a b) o st 0))
           (:free (o st) (bidi-scan-end nil o st 0)))
  :enable (inside-induction
           bidi-scan-step))

; The scan of a segment.

(local
 (define segment-induction (cps st ver)
   (cond ((endp cps) st)
         ((right-to-left-code-point-p (car cps) ver) st)
         (t (segment-induction (cdr cps)
                               (bidi-scan-step st
                                               t
                                               (code-point-bidi-class (car cps)
                                                                      ver)
                                               0)
                               ver)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-end-of-segment
  (b* ((new-st (bidi-scan-end (cp-classes cps ver)
                              (segment-outside cps ver nil)
                              st
                              0)))
    (implies (and (bidi-plain-p cps ver)
                  (scan-invariant st (append cps rest) ver)
                  (or (right-to-left-free-p cps ver)
                      (and (bidi-turns-left-to-right-p rest ver)
                           (not (bidi-attaches-p rest ver)))))
             (and (scan-invariant new-st rest ver)
                  (implies (not (right-to-left-free-p cps ver))
                           (equal new-st :inside)))))
  :induct (segment-induction cps st ver)
  :expand ((cp-classes cps ver)
           (segment-outside cps ver nil)
           (append cps rest)
           (:free (a b o st) (bidi-scan-end (cons a b) o st 0))
           (:free (o st) (bidi-scan-end nil o st 0))
           (:free (a b) (bidi-turns-left-to-right-p (cons a b) ver)))
  :enable (segment-induction
           scan-invariant
           bidi-scan-step
           bidi-scan-free-kind-p
           bidi-scan-zone-first-kind-p
           bidi-scan-zone-kind-p
           bidi-attaches-p
           bidi-plain-code-point-p
           right-to-left-code-point-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel bidi-scan-end-of-segment-is-a-state
  (implies (and (scan-invariant st (append cps rest) ver)
                (bidi-plain-p cps ver)
                (or (right-to-left-free-p cps ver)
                    (and (bidi-turns-left-to-right-p rest ver)
                         (not (bidi-attaches-p rest ver)))))
           (bidi-scan-end (cp-classes cps ver)
                          (segment-outside cps ver nil)
                          st
                          0))
  :use bidi-scan-end-of-segment
  :disable bidi-scan-end-of-segment
  :enable scan-invariant)

; The scan of the text.

(local
 (define segments-induction (segments st (start natp) ver)
   (if (endp segments)
       (list st start)
     (segments-induction (cdr segments)
                         (bidi-scan-end (cp-classes (car segments) ver)
                                        (segment-outside (car segments) ver nil)
                                        st
                                        0)
                         (+ (nfix start) (len (car segments)))
                         ver))
   :verify-guards nil
   :hooks nil))

(defrulel scan-invariant-forward-to-state
  (implies (scan-invariant st rest ver)
           st)
  :rule-classes :forward-chaining
  :enable scan-invariant)

(defrulel bidi-scan-ok-of-segments
  (implies (and (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-guarded-segments-from-p segments start pairs ver)
                (scan-invariant st (acl2::flatten segments) ver))
           (bidi-scan-ok (cp-classes (acl2::flatten segments) ver)
                         (segments-outside segments ver)
                         st
                         0))
  :induct (segments-induction segments st start ver)
  :expand ((acl2::flatten segments)
           (segments-outside segments ver)
           (bidi-guarded-segments-from-p segments start pairs ver)
           (:free (o st) (bidi-scan-ok nil o st 0)))
  :enable segments-induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The bracket pairs: a pair whose opening bracket is inside
; has its closing bracket inside.

(local
 (define start-induction (segments (start natp))
   (if (endp segments)
       start
     (start-induction (cdr segments)
                      (+ (nfix start) (len (car segments)))))
   :verify-guards nil
   :hooks nil))

(defruledl nth-of-segments-outside-of-close-lemma
  (b* ((open (bracket-pair->open pair))
       (close (bracket-pair->close pair)))
    (implies (and (code-point-list-listp segments)
                  (bidi-guarded-segments-from-p segments start (list pair) ver)
                  (natp start)
                  (<= start open)
                  (< open close)
                  (not (nth (- open start) (segments-outside segments ver))))
             (not (nth (- close start) (segments-outside segments ver)))))
  :induct (start-induction segments start)
  :expand ((segments-outside segments ver)
           (bidi-guarded-segments-from-p segments start (list pair) ver)
           (:free (start end)
                  (bidi-bracket-pairs-closed-p (list pair) start end))
           (:free (start end)
                  (bidi-bracket-pairs-closed-p nil start end)))
  :enable (start-induction nfix))

(defrulel nth-of-segments-outside-of-close
  (b* ((open (bracket-pair->open pair))
       (close (bracket-pair->close pair)))
    (implies (and (code-point-list-listp segments)
                  (bidi-guarded-segments-from-p segments 0 (list pair) ver)
                  (< open close)
                  (not (nth open (segments-outside segments ver))))
             (not (nth close (segments-outside segments ver)))))
  :use (:instance nth-of-segments-outside-of-close-lemma (start 0)))

(defrulel bidi-guarded-segments-from-p-of-fewer-pairs
  (implies (and (bidi-guarded-segments-from-p segments start pairs ver)
                (consp pairs))
           (and (bidi-guarded-segments-from-p segments
                                              start
                                              (cdr pairs)
                                              ver)
                (bidi-guarded-segments-from-p segments
                                              start
                                              (list (car pairs))
                                              ver)))
  :induct (start-induction segments start)
  :expand ((:free (pairs)
                  (bidi-guarded-segments-from-p segments start pairs ver))
           (:free (start end)
                  (bidi-bracket-pairs-closed-p pairs start end))
           (:free (start end)
                  (bidi-bracket-pairs-closed-p (list (car pairs)) start end))
           (:free (start end)
                  (bidi-bracket-pairs-closed-p nil start end)))
  :enable start-induction)

(defruledl bidi-pairs-closed-inside-p-of-segments-outside-lemma
  (implies (and (code-point-list-listp segments)
                (bidi-guarded-segments-from-p segments 0 pairs ver)
                (bidi-pairs-sound-p pairs classes roles))
           (bidi-pairs-closed-inside-p pairs (segments-outside segments ver)))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-closed-inside-p
           bidi-pairs-sound-p
           bidi-pair-sound-p))

(defrulel bidi-pairs-closed-inside-p-of-segments-outside
  (implies (and (code-point-list-listp segments)
                (bidi-guarded-segments-from-p segments
                                              0
                                              (bidi-bracket-pairs classes
                                                                  roles)
                                              ver))
           (bidi-pairs-closed-inside-p (bidi-bracket-pairs classes roles)
                                       (segments-outside segments ver)))
  :use (:instance bidi-pairs-closed-inside-p-of-segments-outside-lemma
                  (pairs (bidi-bracket-pairs classes roles))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The cuts.

; A position outside has the level 0.

(local
 (define nth-two-induction ((index natp) x y)
   (if (or (zp index)
           (atom y))
       nil
     (nth-two-induction (- index 1) (cdr x) (cdr y)))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel nth-of-levels-when-bidi-outside-zero-p
  (implies (and (bidi-outside-zero-p outside levels)
                (nat-listp levels)
                (nth index outside)
                (< (nfix index) (len levels)))
           (equal (nth index levels)
                  0))
  :induct (nth-two-induction index outside levels)
  :expand ((bidi-outside-zero-p outside levels))
  :enable (nth-two-induction nth len nfix))

(defrulel nfix-of-len-minus-1
  (implies (consp x)
           (equal (nfix (+ -1 (len x)))
                  (+ -1 (len x))))
  :enable (nfix len))

(defrulel nth-of-len-minus-1-of-append
  (implies (consp x)
           (equal (nth (+ -1 (len x)) (append x y))
                  (nth (+ -1 (len x)) x))))

; A cut is clean if the position before it or the position after it
; is outside.  The list BEFORE has the marks of the positions
; before the cut, and the list AFTER has those from the cut on.

(defrulel bidi-clean-cut-p-when-bidi-outside-zero-p
  (implies (and (bidi-outside-zero-p (append before after) levels)
                (nat-listp levels)
                (or (not (consp before))
                    (nth (- (len before) 1) before)
                    (car after)
                    (<= (len levels) (len before))))
           (bidi-clean-cut-p (len before) levels))
  :enable (bidi-clean-cut-p nfix))

; If the text that is left turns left-to-right,
; its first character is outside.

(defrulel car-of-segments-outside-when-turns-left-to-right
  (implies (and (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-turns-left-to-right-p (acl2::flatten segments) ver)
                (consp (acl2::flatten segments)))
           (car (segments-outside segments ver)))
  :induct (list-induction segments)
  :expand ((acl2::flatten segments)
           (segments-outside segments ver)
           (segment-outside (car segments) ver nil)
           (append (car segments) (acl2::flatten (cdr segments)))
           (:free (a b) (bidi-turns-left-to-right-p (cons a b) ver)))
  :enable (list-induction
           bidi-plain-code-point-p
           right-to-left-code-point-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

; The relation between the state of the scan at a cut
; and the marks before the cut:
; if the state is not :INSIDE, there is no position before the cut
; or the last one is outside.

(local
 (define ends-outside-p (st before)
   :returns (yes/no booleanp)
   (or (not (consp before))
       (eq st :inside)
       (and (nth (- (len before) 1) before)
            t))
   :verify-guards nil
   :hooks nil))

(defrulel segment-outside-when-not-consp
  (implies (not (consp cps))
           (equal (segment-outside cps ver inside)
                  nil))
  :expand (segment-outside cps ver inside))

(defrulel segment-outside-under-iff
  (iff (segment-outside cps ver inside)
       (consp cps))
  :expand (segment-outside cps ver inside))

(defrulel nth-of-last-of-segment-outside-when-right-to-left-free-p
  (implies (and (right-to-left-free-p cps ver)
                (consp cps))
           (nth (+ -1 (len cps)) (segment-outside cps ver nil)))
  :use (:instance nth-of-segment-outside-when-right-to-left-free-p
                  (index (+ -1 (len cps))))
  :disable nth-of-segment-outside-when-right-to-left-free-p
  :enable (nfix len))

(defrulel ends-outside-p-after-segment
  (implies (and (scan-invariant st (append cps rest) ver)
                (bidi-plain-p cps ver)
                (or (right-to-left-free-p cps ver)
                    (and (bidi-turns-left-to-right-p rest ver)
                         (not (bidi-attaches-p rest ver))))
                (ends-outside-p st before))
           (ends-outside-p (bidi-scan-end (cp-classes cps ver)
                                          (segment-outside cps ver nil)
                                          st
                                          0)
                           (append before (segment-outside cps ver nil))))
  :cases ((not (consp cps))
          (right-to-left-free-p cps ver))
  :expand ((:free (o st) (bidi-scan-end nil o st 0)))
  :enable (ends-outside-p nfix))

; The cut at the start of the segments that are left.

(defrulel bidi-clean-cut-p-of-0
  (bidi-clean-cut-p 0 levels)
  :enable bidi-clean-cut-p)

(defrulel bidi-clean-cut-p-at-start-of-segments
  (implies (and (bidi-outside-zero-p (append before
                                             (segments-outside segments ver))
                                     levels)
                (scan-invariant st (acl2::flatten segments) ver)
                (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (nat-listp levels)
                (equal (len levels)
                       (+ (len before)
                          (len (acl2::flatten segments))))
                (ends-outside-p st before))
           (bidi-clean-cut-p (len before) levels))
  :cases ((consp (acl2::flatten segments)))
  :enable (scan-invariant
           ends-outside-p))

; From the segments that are left to those after the first of them.

(defrulel bidi-plain-p-of-flatten-of-cdr
  (implies (and (bidi-plain-p (acl2::flatten segments) ver)
                (consp segments))
           (and (bidi-plain-p (car segments) ver)
                (bidi-plain-p (acl2::flatten (cdr segments)) ver)))
  :expand (acl2::flatten segments))

(defrulel bidi-guarded-segments-from-p-of-cdr
  (implies (and (bidi-guarded-segments-from-p segments start pairs ver)
                (consp segments)
                (code-point-list-listp segments))
           (bidi-guarded-segments-from-p (cdr segments)
                                         (+ (nfix start)
                                            (len (car segments)))
                                         pairs
                                         ver))
  :expand (bidi-guarded-segments-from-p segments start pairs ver))

(defrulel scan-invariant-after-first-segment
  (implies (and (bidi-guarded-segments-from-p segments start pairs ver)
                (scan-invariant st (acl2::flatten segments) ver)
                (consp segments)
                (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver))
           (scan-invariant
            (bidi-scan-end (cp-classes (car segments) ver)
                           (segment-outside (car segments) ver nil)
                           st
                           0)
            (acl2::flatten (cdr segments))
            ver))
  :expand ((acl2::flatten segments)
           (bidi-guarded-segments-from-p segments start pairs ver)))

(defrulel ends-outside-p-after-first-segment
  (implies (and (bidi-guarded-segments-from-p segments start pairs ver)
                (scan-invariant st (acl2::flatten segments) ver)
                (consp segments)
                (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (ends-outside-p st before))
           (ends-outside-p
            (bidi-scan-end (cp-classes (car segments) ver)
                           (segment-outside (car segments) ver nil)
                           st
                           0)
            (append before
                    (segment-outside (car segments) ver nil))))
  :expand ((acl2::flatten segments)
           (bidi-guarded-segments-from-p segments start pairs ver)))

(defrulel bidi-outside-zero-p-of-append-of-first-segment
  (implies (and (bidi-outside-zero-p (append before
                                             (segments-outside segments ver))
                                     levels)
                (consp segments))
           (bidi-outside-zero-p (append before
                                        (segment-outside (car segments) ver nil)
                                        (segments-outside (cdr segments) ver))
                                levels))
  :expand (segments-outside segments ver))

(defrulel len-of-flatten-when-consp
  (implies (consp segments)
           (equal (len (acl2::flatten segments))
                  (+ (len (car segments))
                     (len (acl2::flatten (cdr segments))))))
  :expand (acl2::flatten segments))

; All the cuts.

(defrulel bidi-clean-cuts-p-when-not-consp
  (implies (not (consp segments))
           (bidi-clean-cuts-p segments start levels))
  :expand (bidi-clean-cuts-p segments start levels))

(local
 (define cuts-induction (segments st (start natp) before ver)
   (if (endp segments)
       (list st start before)
     (cuts-induction (cdr segments)
                     (bidi-scan-end (cp-classes (car segments) ver)
                                    (segment-outside (car segments) ver nil)
                                    st
                                    0)
                     (+ (nfix start) (len (car segments)))
                     (append before
                             (segment-outside (car segments) ver nil))
                     ver))
   :verify-guards nil
   :hooks nil))

(defruledl bidi-clean-cuts-p-of-segments-lemma
  (implies (and (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-guarded-segments-from-p segments start pairs ver)
                (scan-invariant st (acl2::flatten segments) ver)
                (bidi-outside-zero-p (append before
                                             (segments-outside segments ver))
                                     levels)
                (nat-listp levels)
                (equal (len levels)
                       (+ (len before)
                          (len (acl2::flatten segments))))
                (ends-outside-p st before))
           (bidi-clean-cuts-p segments (len before) levels))
  :induct (cuts-induction segments st start before ver)
  :expand ((bidi-clean-cuts-p segments (len before) levels))
  :enable cuts-induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem, for segments that are lists of code points.

(defruledl bidi-confined-p-when-bidi-guarded-segments-p-lemma
  (implies (and (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-guarded-segments-p segments ver))
           (bidi-confined-p segments ver))
  :enable (bidi-confined-p
           bidi-guarded-segments-p
           scan-invariant
           ends-outside-p)
  :use (:instance bidi-clean-cuts-p-of-segments-lemma
                  (st :free)
                  (start 0)
                  (before nil)
                  (pairs (bidi-bracket-pairs
                          (cp-classes (acl2::flatten segments) ver)
                          (bidi-char-list-brackets
                           (code-points-to-bidi-chars
                            (acl2::flatten segments)
                            ver))))
                  (levels (bidi-paragraph-all-levels
                           (code-points-to-bidi-chars
                            (acl2::flatten segments)
                            ver)
                           0))))

(defrulel bidi-plain-p-of-code-point-list-fix
  (equal (bidi-plain-p (code-point-list-fix cps) ver)
         (bidi-plain-p cps ver))
  :induct (list-induction cps)
  :enable (list-induction code-point-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-guarded-segments-theorem
  :parents (bidi-guarded-segments)
  :short "A plain text whose segments are guarded is confined."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conditions on the segments
     (see @(tsee bidi-guarded-segments-p))
     are on the bidirectional classes of the characters
     and on the bracket pairs of the text.
     By the first theorem they are enough,
     for a plain text (see @(tsee bidi-plain-p))
     in a paragraph whose embedding level is 0,
     for every cut between two segments to be clean
     (see @(tsee bidi-confined-p)).
     The second theorem puts the first together
     with the theorem about confined texts
     (see @(see bidi-confined-theorem)):
     the display of such a text begins with the characters
     of its first @('k') segments, in some order, for every @('k').")
   (xdoc::p
    "The proof follows the algorithm rule by rule.
     Call a position of the text <i>inside</i>
     if it is, in its segment, the first character
     of class @('R'), @('AL') or @('AN') or a character after that one,
     and <i>outside</i> otherwise.
     So a segment with no such character is all outside.
     The proof shows that every position outside gets the level 0,
     and that at each cut between two segments
     the position before the cut or the position after it is outside.")
   (xdoc::p
    "A plain text at the paragraph embedding level 0
     is one isolating run sequence at the level 0,
     with @('L') on both sides [UAX #9, rules X1 to X10].
     The invariant of the proof is a condition on the classes
     of the positions outside.
     It goes along the text in one of three states.
     At the start of the text, and after an @('L') outside,
     a position outside may have any class other than
     @('R'), @('AL') and @('AN').
     After a position inside, the positions outside
     up to the next @('L') may not have the classes
     @('R'), @('AL'), @('EN') and @('AN'),
     so that rules N1 and N2 resolve them all to @('L');
     and the first of them may not have the class @('ET') or @('NSM'),
     which rules W5 and W1 join to the character before.
     The first two conditions on the segments say just that.")
   (xdoc::p
    "Each of rules W1 to W7 keeps the invariant,
     with fewer classes allowed after rules W1, W6 and W7.
     Rule N0 keeps it too.
     The rule gives the class @('R') to the brackets of a pair
     only if the direction before the opening bracket is @('R')
     and there is an @('R'), and no @('L'), between the two brackets;
     for an opening bracket outside that cannot be.
     And by the third condition a pair whose opening bracket is inside
     has its closing bracket inside.
     After rules N1 and N2 every position outside has the class @('L'),
     so rules I1 and I2 leave it at the level 0,
     and rule L1 only lowers levels to 0.")
   (xdoc::p
    "The proof uses that every paired bracket has the class @('ON')
     (see @(see bidi-brackets-are-neutral)):
     so the bracket pairs that rule N0 finds, after rules W1 to W7,
     are the bracket pairs of the text, which the third condition is about.")
   (xdoc::p
    "The steps of the proof are in four books
     that the book of this theorem includes locally:
     @('bidi-guarded-plain') (a plain text is one sequence),
     @('bidi-guarded-weak') (the invariant, and rules W1 to W7),
     @('bidi-guarded-brackets') (facts about the bracket pairs)
     and @('bidi-guarded-neutral') (rules N0 to N2, I1 and I2).
     Their definitions are for the proof only;
     they are explained in comments
     and have no topics in this documentation."))

  (defrule bidi-confined-p-when-bidi-guarded-segments-p
    (implies (and (bidi-plain-p (acl2::flatten segments) ver)
                  (bidi-guarded-segments-p segments ver))
             (bidi-confined-p segments ver))
    :use (:instance bidi-confined-p-when-bidi-guarded-segments-p-lemma
                    (segments (code-point-list-list-fix segments))))

  (defrule perm-of-take-of-bidi-arrange-paragraph-when-bidi-guarded-segments-p
    (implies (and (equal (paragraph-direction-kind direction)
                         :left-to-right)
                  (bidi-plain-p (acl2::flatten segments) ver)
                  (bidi-guarded-segments-p segments ver)
                  (natp k)
                  (<= k (len segments)))
             (acl2::perm
              (bidi-shown-char-list-code-points
               (take (len (acl2::flatten (take k segments)))
                     (bidi-arrange-paragraph (acl2::flatten segments)
                                             direction
                                             ver)))
              (code-point-list-fix (acl2::flatten (take k segments)))))))
