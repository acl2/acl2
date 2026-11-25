; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-guarded-theorem")

(local (include-book "bidi-guarded-neutral"))

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-self-contained-segments
  :parents (bidi-confinement)
  :short "Conditions on the segments of a text,
          which can be checked without running the algorithm,
          under which each segment is displayed as it is alone."
  :long
  (xdoc::topstring
   (xdoc::p
    "A plain text whose segments are guarded
     (see @(see bidi-guarded-segments)) is confined:
     its display keeps the characters of each segment together.
     But the characters of a segment need not be,
     in the display of the text,
     in the order in which the segment is displayed alone.
     For example, write @('B') and @('C') for two right-to-left letters,
     and take the text @('a (B) C') in the two segments
     @('a (') and @('B) C').
     In the text the two brackets are a pair, and rule N0 [UAX #9]
     gives both the direction of the paragraph, from left to right:
     the characters of the second segment are displayed
     in the order in which they are stored.
     Alone, the second segment has a bracket without a partner,
     and is displayed from right to left as a whole.")
   (xdoc::p
    "The segments are <i>self-contained</i> if they are guarded and,
     in addition:")
   (xdoc::ul
    (xdoc::li
     "No bracket pair of the text [UAX #9, BD16]
      has its closing bracket inside a right-to-left segment
      and its opening bracket before the segment
      (see @(tsee bidi-bracket-pairs-opened-p)).
      As for guarded segments, a segment is right-to-left
      if it has a character of class @('R'), @('AL') or @('AN').
      With the third condition on guarded segments,
      this says that a bracket of a right-to-left segment
      is paired, if at all, with a bracket of the same segment.")
    (xdoc::li
     "The search for the bracket pairs of the text does not give up
      (see @(tsee bidi-bracket-pairs-overflow-p)).
      If it gave up, the text would have no bracket pair,
      while a segment alone could have some."))
   (xdoc::p
    "The predicate is @(tsee bidi-self-contained-segments-p).
     For a plain text (see @(tsee bidi-plain-p))
     in a paragraph from left to right,
     the theorems of this book say that, if it holds,
     each character has in the text the level
     that it has when its segment is alone,
     as a paragraph from left to right of its own;
     and that the display of the text is the display of the first segment,
     followed by the display of the second segment, and so on
     (see @(see bidi-self-contained-segments-theorem)).")
   (xdoc::p
    "The file @('tests/bidi-self-contained.lisp') has the example above,
     which fails only the condition on the closing brackets.
     It also checks the two theorems by running the algorithm
     on every text of one to four characters over sixteen characters,
     with every way of cutting the text."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;

(define bidi-bracket-pairs-opened-p ((pairs bracket-pair-listp)
                                     (start natp)
                                     (end natp))
  :returns (yes/no booleanp)
  :short "Check that every bracket pair of a list
          that closes in a part of a text opens in that part."
  :long
  (xdoc::topstring
   (xdoc::p
    "The part goes from the position @('start'), included,
     to the position @('end'), excluded.
     A bracket pair is the position of an opening bracket
     and the position of the closing bracket that goes with it
     [UAX #9, BD16]; see @(tsee bidi-bracket-pairs).
     The opening bracket of a pair is before its closing bracket,
     so the check is that no pair that closes in the part
     opens before the position @('start').
     See also @(tsee bidi-bracket-pairs-closed-p)."))
  (b* (((when (endp pairs)) t)
       ((bracket-pair pair) (car pairs)))
    (and (or (< pair.close (lnfix start))
             (<= (lnfix end) pair.close)
             (<= (lnfix start) pair.open))
         (bidi-bracket-pairs-opened-p (cdr pairs) start end)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-bracket-pairs-opened-p
    :hints (("Goal"
             :induct (bidi-bracket-pairs-opened-p pairs start end)
             :expand ((bidi-bracket-pairs-opened-p pairs start end)
                      (bidi-bracket-pairs-opened-p
                       (bracket-pair-list-fix pairs)
                       start
                       end)
                      (bidi-bracket-pairs-opened-p pairs (nfix start) end)
                      (bidi-bracket-pairs-opened-p pairs
                                                   start
                                                   (nfix end)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-segments-opened-from-p ((segments code-point-list-listp)
                                     (start natp)
                                     (pairs bracket-pair-listp)
                                     (ver versionp))
  :returns (yes/no booleanp)
  :short "Check, for some of the segments of a text,
          that every bracket pair that closes in a right-to-left segment
          opens in that segment,
          given the bracket pairs of the text,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is a list of segments that follow each other
     to the end of the text,
     and the second is the number of characters of the text
     before the first of them,
     as for @(tsee bidi-guarded-segments-from-p).
     In a plain text, a segment is right-to-left
     exactly when it does not satisfy @(tsee right-to-left-free-p)."))
  (b* (((when (endp segments)) t)
       (segment (code-point-list-fix (car segments)))
       (start (lnfix start))
       (end (+ start (len segment))))
    (and (or (right-to-left-free-p segment ver)
             (bidi-bracket-pairs-opened-p pairs start end))
         (bidi-segments-opened-from-p (cdr segments) end pairs ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-segments-opened-from-p
    :hints (("Goal"
             :induct (bidi-segments-opened-from-p segments start pairs ver)
             :expand ((bidi-segments-opened-from-p segments start pairs ver)
                      (bidi-segments-opened-from-p
                       (code-point-list-list-fix segments)
                       start
                       pairs
                       ver)
                      (bidi-segments-opened-from-p segments
                                                   (nfix start)
                                                   pairs
                                                   ver)
                      (bidi-segments-opened-from-p
                       segments
                       start
                       (bracket-pair-list-fix pairs)
                       ver)
                      (bidi-segments-opened-from-p segments
                                                   start
                                                   pairs
                                                   (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-self-contained-segments-p ((segments code-point-list-listp)
                                        (ver versionp))
  :returns (yes/no booleanp)
  :short "Check the conditions on the segments of a text
          under which each segment of a plain text
          is displayed as it is alone,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see bidi-self-contained-segments).
     The text is the segments one after the other,
     and the bracket pairs are those of the whole text."))
  (b* ((chars (code-points-to-bidi-chars (acl2::flatten segments) ver))
       (classes (bidi-char-list-classes chars))
       (roles (bidi-char-list-brackets chars)))
    (and (bidi-guarded-segments-p segments ver)
         (not (bidi-bracket-pairs-overflow-p classes roles))
         (bidi-segments-opened-from-p segments
                                      0
                                      (bidi-bracket-pairs classes roles)
                                      ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defrulel nat-listp-of-append-of-nat-lists
  (implies (and (nat-listp x)
                (nat-listp y))
           (nat-listp (append x y)))
  :induct (len x)
  :enable (len nat-listp))

(define bidi-levels-of-each-segment ((segments code-point-list-listp)
                                     (ver versionp))
  :returns (levels nat-listp)
  :short "The levels of the characters of some segments,
          each segment being a paragraph from left to right of its own,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the levels of the characters of the first segment
     (see @(tsee bidi-paragraph-all-levels)),
     followed by those of the second segment, and so on."))
  (if (endp segments)
      nil
    (append (bidi-paragraph-all-levels
             (code-points-to-bidi-chars (car segments) ver)
             0)
            (bidi-levels-of-each-segment (cdr segments) ver)))
  :guard-hints (("Goal"
                 :use (:instance nat-listp-of-bidi-paragraph-all-levels
                                 (chars (code-points-to-bidi-chars
                                         (car segments)
                                         ver))
                                 (paragraph-level 0))
                 :in-theory (disable nat-listp-of-bidi-paragraph-all-levels)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-display-of-each-segment ((segments code-point-list-listp)
                                      (direction paragraph-direction-p)
                                      (ver versionp))
  :returns (displayed code-point-listp)
  :short "The display of some segments, one after the other,
          each segment being a text of its own,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the display of the first segment
     (see @(tsee bidi-display)),
     followed by the display of the second segment, and so on."))
  (if (endp segments)
      nil
    (append (bidi-display (car segments) direction ver)
            (bidi-display-of-each-segment (cdr segments) direction ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here to the last section, the events are local.
; The last section has the two theorems and the plan of their proof.

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

; The classes and the bracket roles of the characters
; of a list of code points.

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

(local
 (define cp-roles ((cps code-point-listp) (ver versionp))
   :returns (roles bidi-bracket-role-listp)
   (if (endp cps)
       nil
     (cons (code-point-bidi-bracket-role (car cps) ver)
           (cp-roles (cdr cps) ver)))
   :hooks nil
   ///
   (defret len-of-cp-roles
     (equal (len roles)
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

(defrulel bidi-char-list-brackets-of-code-points-to-bidi-chars
  (equal (bidi-char-list-brackets (code-points-to-bidi-chars cps ver))
         (cp-roles cps ver))
  :induct (list-induction cps)
  :enable (list-induction
           cp-roles
           bidi-char-list-brackets
           code-points-to-bidi-chars
           code-point-bidi-char))

(defrulel cp-classes-when-not-consp
  (implies (not (consp cps))
           (equal (cp-classes cps ver)
                  nil))
  :expand (cp-classes cps ver))

(defrulel consp-of-cp-classes
  (equal (consp (cp-classes cps ver))
         (consp cps))
  :expand (cp-classes cps ver))

(defrulel cp-classes-under-iff
  (iff (cp-classes cps ver)
       (consp cps))
  :expand (cp-classes cps ver))

(defrulel cp-roles-when-not-consp
  (implies (not (consp cps))
           (equal (cp-roles cps ver)
                  nil))
  :expand (cp-roles cps ver))

(defrulel cp-classes-of-append
  (equal (cp-classes (append x y) ver)
         (append (cp-classes x ver)
                 (cp-classes y ver)))
  :induct (list-induction x)
  :enable (list-induction cp-classes))

(defrulel cp-roles-of-append
  (equal (cp-roles (append x y) ver)
         (append (cp-roles x ver)
                 (cp-roles y ver)))
  :induct (list-induction x)
  :enable (list-induction cp-roles))

(defrulel bidi-plain-class-listp-of-cp-classes
  (implies (bidi-plain-p cps ver)
           (bidi-plain-class-listp (cp-classes cps ver)))
  :induct (list-induction cps)
  :enable (list-induction
           cp-classes
           bidi-plain-code-point-p
           bidi-plain-class-p))

; Every paired bracket has the class ON.

(defrulel bidi-roles-neutral-p-of-cp-roles
  (bidi-roles-neutral-p (cp-roles cps ver)
                        (cp-classes cps ver))
  :induct (list-induction cps)
  :enable (list-induction
           cp-classes
           cp-roles
           bidi-roles-neutral-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The three parts of a segment:
; the characters before the first one of class R, AL or AN (the prefix);
; from that character to the last character that is not white space
; (the window); and the white space at the end (the tail).
; A segment with no character of class R, AL or AN is all prefix.

(local
 (define start-cp-p ((cp code-point-p) (ver versionp))
   :returns (yes/no booleanp)
   (bidi-window-start-kind-p
    (bidi-class-kind (code-point-bidi-class cp ver)))
   :hooks nil))

(local
 (define white-cp-p ((cp code-point-p) (ver versionp))
   :returns (yes/no booleanp)
   (equal (bidi-class-kind (code-point-bidi-class cp ver))
          :white-space)
   :hooks nil))

(local
 (define no-start-p ((cps code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (endp cps)
       (and (not (start-cp-p (car cps) ver))
            (no-start-p (cdr cps) ver)))
   :hooks nil))

(local
 (define white-all-p ((cps code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (endp cps)
       (and (white-cp-p (car cps) ver)
            (white-all-p (cdr cps) ver)))
   :hooks nil))

(local
 (define seg-prefix ((cps code-point-listp) (ver versionp))
   :returns (prefix true-listp)
   (cond ((endp cps) nil)
         ((start-cp-p (car cps) ver) nil)
         (t (cons (car cps)
                  (seg-prefix (cdr cps) ver))))
   :hooks nil))

(local
 (define seg-inside ((cps code-point-listp) (ver versionp))
   (cond ((endp cps) nil)
         ((start-cp-p (car cps) ver) cps)
         (t (seg-inside (cdr cps) ver)))
   :hooks nil))

(local
 (define trim-white ((cps code-point-listp) (ver versionp))
   :returns (trimmed true-listp)
   (cond ((endp cps) nil)
         ((white-all-p cps ver) nil)
         (t (cons (car cps)
                  (trim-white (cdr cps) ver))))
   :hooks nil))

(local
 (define white-tail ((cps code-point-listp) (ver versionp))
   (cond ((endp cps) nil)
         ((white-all-p cps ver) cps)
         (t (white-tail (cdr cps) ver)))
   :hooks nil))

(local
 (define seg-window ((cps code-point-listp) (ver versionp))
   :returns (window true-listp)
   (trim-white (seg-inside cps ver) ver)
   :verify-guards nil
   :hooks nil))

(local
 (define seg-tail ((cps code-point-listp) (ver versionp))
   (white-tail (seg-inside cps ver) ver)
   :verify-guards nil
   :hooks nil))

(defrulel append-of-seg-prefix-and-seg-inside
  (implies (true-listp cps)
           (equal (append (seg-prefix cps ver) (seg-inside cps ver))
                  cps))
  :induct (list-induction cps)
  :enable (list-induction seg-prefix seg-inside))

(defrulel append-of-trim-white-and-white-tail
  (implies (true-listp cps)
           (equal (append (trim-white cps ver) (white-tail cps ver))
                  cps))
  :induct (list-induction cps)
  :enable (list-induction trim-white white-tail))

(defrulel true-listp-of-seg-inside
  (implies (true-listp cps)
           (true-listp (seg-inside cps ver)))
  :induct (list-induction cps)
  :enable (list-induction seg-inside))

(defrulel true-listp-of-white-tail
  (implies (true-listp cps)
           (true-listp (white-tail cps ver)))
  :induct (list-induction cps)
  :enable (list-induction white-tail))

; The parts put together again, alone and before something else.

(defrulel append-of-the-parts-of-a-segment
  (implies (true-listp cps)
           (equal (append (seg-prefix cps ver)
                          (append (seg-window cps ver)
                                  (seg-tail cps ver)))
                  cps))
  :enable (seg-window seg-tail))

(defrulel append-of-the-parts-of-a-segment-and-more
  (implies (true-listp cps)
           (equal (append (seg-prefix cps ver)
                          (append (seg-window cps ver)
                                  (append (seg-tail cps ver)
                                          more)))
                  (append cps more)))
  :use append-of-the-parts-of-a-segment
  :disable append-of-the-parts-of-a-segment)

(defrulel no-start-p-of-seg-prefix
  (no-start-p (seg-prefix cps ver) ver)
  :induct (list-induction cps)
  :enable (list-induction seg-prefix no-start-p))

(defrulel start-cp-p-of-car-of-seg-inside
  (implies (consp (seg-inside cps ver))
           (start-cp-p (car (seg-inside cps ver)) ver))
  :induct (list-induction cps)
  :enable (list-induction seg-inside))

(defrulel white-all-p-of-white-tail
  (white-all-p (white-tail cps ver) ver)
  :induct (list-induction cps)
  :enable (list-induction white-tail white-all-p))

(defrulel white-all-p-of-seg-tail
  (white-all-p (seg-tail cps ver) ver)
  :enable seg-tail)

(defrulel trim-white-when-starts-with-start-cp-p
  (implies (and (consp cps)
                (start-cp-p (car cps) ver))
           (and (consp (trim-white cps ver))
                (equal (car (trim-white cps ver))
                       (car cps))))
  :expand ((trim-white cps ver)
           (white-all-p cps ver))
  :enable (start-cp-p
           white-cp-p
           bidi-window-start-kind-p))

(defrulel seg-window-when-consp-of-seg-inside
  (implies (consp (seg-inside cps ver))
           (and (consp (seg-window cps ver))
                (start-cp-p (car (seg-window cps ver)) ver)))
  :enable seg-window)

(defrulel seg-window-and-seg-tail-when-not-consp-of-seg-inside
  (implies (not (consp (seg-inside cps ver)))
           (and (equal (seg-window cps ver) nil)
                (not (consp (seg-tail cps ver)))))
  :enable (seg-window seg-tail trim-white white-tail))

(defrulel seg-prefix-when-not-consp-of-seg-inside
  (implies (and (not (consp (seg-inside cps ver)))
                (true-listp cps))
           (equal (seg-prefix cps ver)
                  cps))
  :induct (list-induction cps)
  :enable (list-induction seg-prefix seg-inside))

(defrulel no-start-p-when-not-consp-of-seg-inside
  (implies (not (consp (seg-inside cps ver)))
           (no-start-p cps ver))
  :induct (list-induction cps)
  :enable (list-induction no-start-p seg-inside))

; The parts of a plain segment are plain.

(defrulel bidi-plain-p-of-seg-prefix
  (implies (bidi-plain-p cps ver)
           (bidi-plain-p (seg-prefix cps ver) ver))
  :induct (list-induction cps)
  :enable (list-induction seg-prefix))

(defrulel bidi-plain-p-of-seg-inside
  (implies (bidi-plain-p cps ver)
           (bidi-plain-p (seg-inside cps ver) ver))
  :induct (list-induction cps)
  :enable (list-induction seg-inside))

(defrulel bidi-plain-p-of-trim-white
  (implies (bidi-plain-p cps ver)
           (bidi-plain-p (trim-white cps ver) ver))
  :induct (list-induction cps)
  :enable (list-induction trim-white))

(defrulel bidi-plain-p-of-white-tail
  (implies (bidi-plain-p cps ver)
           (bidi-plain-p (white-tail cps ver) ver))
  :induct (list-induction cps)
  :enable (list-induction white-tail))

(defrulel bidi-plain-p-of-seg-window
  (implies (bidi-plain-p cps ver)
           (bidi-plain-p (seg-window cps ver) ver))
  :enable seg-window)

(defrulel bidi-plain-p-of-seg-tail
  (implies (bidi-plain-p cps ver)
           (bidi-plain-p (seg-tail cps ver) ver))
  :enable seg-tail)

; A segment with a character of class R, AL or AN is not right-to-left-free.

(defrulel not-right-to-left-free-p-when-consp-of-seg-inside
  (implies (consp (seg-inside cps ver))
           (not (right-to-left-free-p cps ver)))
  :induct (list-induction cps)
  :enable (list-induction
           seg-inside
           start-cp-p
           bidi-window-start-kind-p
           right-to-left-code-point-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The marks (see the book bidi-guarded-weak.lisp):
; the prefix and the tail of a segment are outside, and its window is inside.
; These are not the marks of the book bidi-guarded-theorem.lisp,
; in which the tail is inside too:
; with the tail outside, rule L1 does to a segment in the text
; what it does to the segment alone.

(local
 (define run-marks (x value)
   (if (consp x)
       (cons value
             (run-marks (cdr x) value))
     nil)
   :hooks nil
   ///
   (defrule len-of-run-marks
     (equal (len (run-marks x value))
            (len x))
     :induct t
     :enable len)
   (defrule true-listp-of-run-marks
     (true-listp (run-marks x value))
     :rule-classes (:rewrite :type-prescription)
     :induct t)))

(defrulel run-marks-when-not-consp
  (implies (not (consp x))
           (equal (run-marks x value)
                  nil))
  :expand (run-marks x value))

(defrulel nth-of-run-marks
  (equal (nth i (run-marks x value))
         (if (< (nfix i) (len x))
             value
           nil))
  :induct (nth i x)
  :expand (run-marks x value)
  :enable (nth len nfix))

(local
 (define seg-marks ((cps code-point-listp) (ver versionp))
   :returns (marks true-listp)
   (append (run-marks (seg-prefix cps ver) t)
           (append (run-marks (seg-window cps ver) nil)
                   (run-marks (seg-tail cps ver) t)))
   :verify-guards nil
   :hooks nil))

(local
 (define segs-marks ((segments code-point-list-listp) (ver versionp))
   :returns (marks true-listp)
   (if (endp segments)
       nil
     (append (seg-marks (car segments) ver)
             (segs-marks (cdr segments) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel len-of-seg-prefix-and-seg-inside
  (equal (+ (len (seg-prefix cps ver))
            (len (seg-inside cps ver)))
         (len cps))
  :rule-classes (:rewrite :linear)
  :induct (list-induction cps)
  :enable (list-induction seg-prefix seg-inside len))

(defrulel len-of-trim-white-and-white-tail
  (equal (+ (len (trim-white cps ver))
            (len (white-tail cps ver)))
         (len cps))
  :rule-classes (:rewrite :linear)
  :induct (list-induction cps)
  :enable (list-induction trim-white white-tail len))

(defrulel len-of-seg-marks
  (equal (len (seg-marks cps ver))
         (len cps))
  :enable (seg-marks seg-window seg-tail))

(defrulel len-of-segs-marks
  (equal (len (segs-marks segments ver))
         (len (acl2::flatten segments)))
  :induct (list-induction segments)
  :enable (list-induction segs-marks acl2::flatten))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The scan of the text (see the book bidi-guarded-weak.lisp).

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

; The scan of two lists one after the other.

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

(defrulel bidi-scan-end-of-append
  (implies (and (equal (len outside1) (len classes1))
                st)
           (equal (bidi-scan-end (append classes1 classes2)
                                 (append outside1 outside2)
                                 st
                                 phase)
                  (and (bidi-scan-end classes1 outside1 st phase)
                       (bidi-scan-end classes2
                                      outside2
                                      (bidi-scan-end classes1 outside1 st phase)
                                      phase))))
  :induct (scan-induction classes1 outside1 st phase)
  :expand ((append classes1 classes2)
           (append outside1 outside2)
           (:free (a b o st) (bidi-scan-end (cons a b) o st phase))
           (bidi-scan-end classes1 outside1 st phase))
  :enable (scan-induction len))

(defrulel bidi-scan-ok-when-bidi-scan-end
  (implies (bidi-scan-end classes outside st phase)
           (bidi-scan-ok classes outside st phase))
  :induct (scan-induction classes outside st phase)
  :expand ((bidi-scan-ok classes outside st phase)
           (bidi-scan-end classes outside st phase))
  :enable scan-induction)

(defrulel bidi-scan-end-when-not-consp
  (implies (not (consp classes))
           (equal (bidi-scan-end classes outside st phase)
                  st))
  :expand (bidi-scan-end classes outside st phase))

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

(defrulel scan-invariant-forward-to-state
  (implies (scan-invariant st rest ver)
           st)
  :rule-classes :forward-chaining
  :enable scan-invariant)

; The scan of a prefix.

(local
 (define prefix-induction (cps st ver)
   (if (endp cps)
       st
     (prefix-induction (cdr cps)
                       (bidi-scan-step st
                                       t
                                       (code-point-bidi-class (car cps) ver)
                                       0)
                       ver))
   :verify-guards nil
   :hooks nil))

(defrulel scan-invariant-of-bidi-scan-end-of-prefix
  (implies (and (bidi-plain-p p ver)
                (no-start-p p ver)
                (scan-invariant st (append p rest) ver))
           (scan-invariant (bidi-scan-end (cp-classes p ver)
                                          (run-marks p t)
                                          st
                                          0)
                           rest
                           ver))
  :induct (prefix-induction p st ver)
  :expand ((cp-classes p ver)
           (run-marks p t)
           (append p rest)
           (no-start-p p ver)
           (:free (a b o st) (bidi-scan-end (cons a b) o st 0))
           (:free (a b) (bidi-turns-left-to-right-p (cons a b) ver)))
  :enable (prefix-induction
           scan-invariant
           bidi-scan-step
           bidi-scan-free-kind-p
           bidi-scan-zone-first-kind-p
           bidi-scan-zone-kind-p
           bidi-attaches-p
           bidi-plain-code-point-p
           start-cp-p
           bidi-window-start-kind-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

; The scan of a window.

(local
 (define window-induction (cps st)
   (if (endp cps)
       st
     (window-induction (cdr cps) :inside))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-end-of-window
  (implies (or (eq st :free)
               (eq st :inside))
           (equal (bidi-scan-end (cp-classes w ver)
                                 (run-marks w nil)
                                 st
                                 0)
                  (if (consp w)
                      :inside
                    st)))
  :induct (window-induction w st)
  :expand ((cp-classes w ver)
           (run-marks w nil)
           (:free (a b o st) (bidi-scan-end (cons a b) o st 0)))
  :enable (window-induction
           bidi-scan-step))

; The scan of a tail.

(local
 (define tail-induction (cps st)
   (if (endp cps)
       st
     (tail-induction (cdr cps) :zone))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-end-of-tail
  (implies (and (white-all-p z ver)
                (or (eq st :inside)
                    (eq st :zone)))
           (equal (bidi-scan-end (cp-classes z ver)
                                 (run-marks z t)
                                 st
                                 0)
                  (if (consp z)
                      :zone
                    st)))
  :induct (tail-induction z st)
  :expand ((cp-classes z ver)
           (run-marks z t)
           (white-all-p z ver)
           (:free (a b o st) (bidi-scan-end (cons a b) o st 0)))
  :enable (tail-induction
           white-cp-p
           bidi-scan-step
           bidi-scan-zone-first-kind-p
           bidi-scan-zone-kind-p))

; A window is reached in the state :FREE.

(defrulel scan-invariant-when-starts-with-start-cp-p
  (implies (and (scan-invariant st cps ver)
                (consp cps)
                (start-cp-p (car cps) ver))
           (equal st :free))
  :rule-classes nil
  :expand (bidi-turns-left-to-right-p cps ver)
  :enable (scan-invariant
           start-cp-p
           bidi-window-start-kind-p))

(defrulel bidi-scan-end-of-window-when-scan-invariant
  (implies (and (scan-invariant st (append w more) ver)
                (consp w)
                (start-cp-p (car w) ver))
           (equal (bidi-scan-end (cp-classes w ver)
                                 (run-marks w nil)
                                 st
                                 0)
                  :inside))
  :rule-classes nil
  :use (:instance scan-invariant-when-starts-with-start-cp-p
                  (cps (append w more))))

; The scan of a window and a tail.

(defrulel scan-invariant-of-bidi-scan-end-of-window-and-tail
  (implies (and (scan-invariant st (append w (append z rest)) ver)
                (consp w)
                (start-cp-p (car w) ver)
                (white-all-p z ver)
                (bidi-turns-left-to-right-p rest ver)
                (not (bidi-attaches-p rest ver)))
           (scan-invariant (bidi-scan-end (cp-classes z ver)
                                          (run-marks z t)
                                          (bidi-scan-end (cp-classes w ver)
                                                         (run-marks w nil)
                                                         st
                                                         0)
                                          0)
                           rest
                           ver))
  :use (:instance scan-invariant-when-starts-with-start-cp-p
                  (cps (append w (append z rest))))
  :enable scan-invariant)

; The scan of the three parts of a segment.

(defruledl bidi-scan-end-of-prefix-is-a-state
  (implies (and (bidi-plain-p p ver)
                (no-start-p p ver)
                (scan-invariant st (append p rest) ver))
           (bidi-scan-end (cp-classes p ver) (run-marks p t) st 0))
  :use scan-invariant-of-bidi-scan-end-of-prefix
  :disable scan-invariant-of-bidi-scan-end-of-prefix)

(defruledl scan-invariant-of-bidi-scan-end-of-parts
  (b* ((seg (append p (append w z))))
    (implies (and (bidi-plain-p p ver)
                  (no-start-p p ver)
                  (scan-invariant st (append seg rest) ver)
                  (or (and (not (consp w))
                           (not (consp z)))
                      (and (consp w)
                           (start-cp-p (car w) ver)
                           (white-all-p z ver)
                           (bidi-turns-left-to-right-p rest ver)
                           (not (bidi-attaches-p rest ver)))))
             (scan-invariant
              (bidi-scan-end (cp-classes seg ver)
                             (append (run-marks p t)
                                     (append (run-marks w nil)
                                             (run-marks z t)))
                             st
                             0)
              rest
              ver)))
  :use (scan-invariant-of-bidi-scan-end-of-prefix
        (:instance bidi-scan-end-of-prefix-is-a-state
                   (rest (append w (append z rest))))
        (:instance bidi-scan-end-of-window-when-scan-invariant
                   (st (bidi-scan-end (cp-classes p ver)
                                      (run-marks p t)
                                      st
                                      0))
                   (more (append z rest))))
  :expand ((scan-invariant :inside rest ver)
           (scan-invariant :zone rest ver)))

; The scan of a segment.

(defrulel scan-invariant-of-bidi-scan-end-of-segment
  (implies (and (code-point-listp seg)
                (bidi-plain-p seg ver)
                (scan-invariant st (append seg rest) ver)
                (or (right-to-left-free-p seg ver)
                    (and (bidi-turns-left-to-right-p rest ver)
                         (not (bidi-attaches-p rest ver)))))
           (scan-invariant (bidi-scan-end (cp-classes seg ver)
                                          (seg-marks seg ver)
                                          st
                                          0)
                           rest
                           ver))
  :cases ((consp (seg-inside seg ver)))
  :use (:instance scan-invariant-of-bidi-scan-end-of-parts
                  (p (seg-prefix seg ver))
                  (w (seg-window seg ver))
                  (z (seg-tail seg ver)))
  :enable seg-marks)

(defrulel bidi-scan-end-of-segment-is-a-state
  (implies (and (scan-invariant st (append seg rest) ver)
                (code-point-listp seg)
                (bidi-plain-p seg ver)
                (or (right-to-left-free-p seg ver)
                    (and (bidi-turns-left-to-right-p rest ver)
                         (not (bidi-attaches-p rest ver)))))
           (bidi-scan-end (cp-classes seg ver) (seg-marks seg ver) st 0))
  :use scan-invariant-of-bidi-scan-end-of-segment
  :disable scan-invariant-of-bidi-scan-end-of-segment)

; The scan of the text.

(local
 (define segments-induction (segments st (start natp) ver)
   (if (endp segments)
       (list st start)
     (segments-induction (cdr segments)
                         (bidi-scan-end (cp-classes (car segments) ver)
                                        (seg-marks (car segments) ver)
                                        st
                                        0)
                         (+ (nfix start) (len (car segments)))
                         ver))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-scan-ok-of-segments
  (implies (and (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-guarded-segments-from-p segments start pairs ver)
                (scan-invariant st (acl2::flatten segments) ver))
           (bidi-scan-ok (cp-classes (acl2::flatten segments) ver)
                         (segs-marks segments ver)
                         st
                         0))
  :induct (segments-induction segments st start ver)
  :expand ((acl2::flatten segments)
           (segs-marks segments ver)
           (bidi-guarded-segments-from-p segments start pairs ver)
           (:free (o st) (bidi-scan-ok nil o st 0)))
  :enable segments-induction)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The marks and the classes of a segment, position by position.

(defrulel len-of-seg-tail
  (equal (len (seg-tail cps ver))
         (- (len cps)
            (+ (len (seg-prefix cps ver))
               (len (seg-window cps ver)))))
  :enable (seg-window seg-tail))

(defrulel len-of-seg-prefix-and-seg-window-bound
  (<= (+ (len (seg-prefix cps ver))
         (len (seg-window cps ver)))
      (len cps))
  :rule-classes :linear
  :enable seg-window)

(defrulel len-of-seg-prefix-below-len-when-consp-of-seg-inside
  (implies (consp (seg-inside cps ver))
           (< (len (seg-prefix cps ver))
              (len cps)))
  :rule-classes :linear
  :expand (len (seg-inside cps ver)))

(defrulel consp-of-seg-tail
  (equal (consp (seg-tail cps ver))
         (< (+ (len (seg-prefix cps ver))
               (len (seg-window cps ver)))
            (len cps)))
  :use len-of-seg-tail
  :disable len-of-seg-tail
  :expand (len (seg-tail cps ver)))

(defrulel <-of-sums-with-two-common-terms
  (implies (and (rationalp i)
                (rationalp l)
                (rationalp p)
                (rationalp w))
           (equal (< (+ i (- p) (- w))
                     (+ l (- p) (- w)))
                  (< i l)))
  :cases ((< i l)))

(defrulel nth-of-seg-marks
  (implies (natp i)
           (equal (nth i (seg-marks cps ver))
                  (cond ((< i (len (seg-prefix cps ver))) t)
                        ((< i (+ (len (seg-prefix cps ver))
                                 (len (seg-window cps ver))))
                         nil)
                        (t (< i (len cps))))))
  :enable (seg-marks nfix))

(defrulel cp-classes-of-the-parts-of-a-segment
  (implies (true-listp cps)
           (equal (cp-classes cps ver)
                  (append (cp-classes (seg-prefix cps ver) ver)
                          (append (cp-classes (seg-window cps ver) ver)
                                  (cp-classes (seg-tail cps ver) ver)))))
  :rule-classes nil
  :use ((:instance cp-classes-of-append
                   (x (seg-prefix cps ver))
                   (y (append (seg-window cps ver) (seg-tail cps ver))))
        (:instance cp-classes-of-append
                   (x (seg-window cps ver))
                   (y (seg-tail cps ver))))
  :disable cp-classes-of-append)

(defrulel bidi-class-kind-of-nth-of-cp-classes-when-white-all-p
  (implies (and (white-all-p cps ver)
                (< (nfix i) (len cps)))
           (equal (bidi-class-kind (nth i (cp-classes cps ver)))
                  :white-space))
  :induct (nth i cps)
  :expand ((cp-classes cps ver)
           (white-all-p cps ver))
  :enable (nth len nfix white-cp-p))

(defrulel bidi-class-kind-of-nth-of-cp-classes-in-tail
  (implies (and (true-listp cps)
                (natp i)
                (<= (+ (len (seg-prefix cps ver))
                       (len (seg-window cps ver)))
                    i)
                (< i (len cps)))
           (equal (bidi-class-kind (nth i (cp-classes cps ver)))
                  :white-space))
  :use cp-classes-of-the-parts-of-a-segment
  :enable nfix)

(defrulel bidi-window-start-kind-p-of-nth-of-cp-classes-at-window
  (implies (and (true-listp cps)
                (consp (seg-inside cps ver)))
           (bidi-window-start-kind-p
            (bidi-class-kind (nth (len (seg-prefix cps ver))
                                  (cp-classes cps ver)))))
  :use (cp-classes-of-the-parts-of-a-segment
        seg-window-when-consp-of-seg-inside)
  :expand (cp-classes (seg-window cps ver) ver)
  :enable start-cp-p
  :disable seg-window-when-consp-of-seg-inside)

; A position with a bracket role has the class ON.

(local
 (define nth-two-induction ((index natp) x y)
   (if (or (zp index)
           (atom x)
           (atom y))
       nil
     (nth-two-induction (- index 1) (cdr x) (cdr y)))
   :verify-guards nil
   :hooks nil))

(defruledl bidi-class-kind-of-nth-when-role
  (implies (and (bidi-roles-neutral-p roles classes)
                (not (equal (bidi-bracket-role-kind (nth index roles)) :none))
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

(defrulel index-below-len-when-role-is-not-none
  (implies (not (equal (bidi-bracket-role-kind (nth index roles)) :none))
           (< (nfix index) (len roles)))
  :rule-classes nil
  :induct (nth index roles)
  :enable (nth len nfix))

(defrulel bidi-class-kind-of-nth-of-cp-classes-when-role
  (implies (not (equal (bidi-bracket-role-kind (nth index (cp-roles cps ver)))
                       :none))
           (equal (bidi-class-kind (nth index (cp-classes cps ver)))
                  :other-neutral))
  :use ((:instance bidi-class-kind-of-nth-when-role
                   (roles (cp-roles cps ver))
                   (classes (cp-classes cps ver)))
        (:instance index-below-len-when-role-is-not-none
                   (roles (cp-roles cps ver)))))

; The first position of the window of a segment has no bracket role,
; and the positions of its tail have none.

(defrulel bidi-class-kind-of-nth-of-cp-classes-at-window
  (implies (and (true-listp cps)
                (consp (seg-inside cps ver)))
           (not (equal (bidi-class-kind (nth (len (seg-prefix cps ver))
                                             (cp-classes cps ver)))
                       :other-neutral)))
  :use bidi-window-start-kind-p-of-nth-of-cp-classes-at-window
  :disable bidi-window-start-kind-p-of-nth-of-cp-classes-at-window
  :enable bidi-window-start-kind-p)

(defrulel bidi-bracket-role-kind-of-nth-of-cp-roles-at-window
  (implies (and (true-listp cps)
                (consp (seg-inside cps ver)))
           (equal (bidi-bracket-role-kind (nth (len (seg-prefix cps ver))
                                               (cp-roles cps ver)))
                  :none))
  :use (:instance bidi-class-kind-of-nth-of-cp-classes-when-role
                  (index (len (seg-prefix cps ver))))
  :disable bidi-class-kind-of-nth-of-cp-classes-when-role)

(defrulel bidi-bracket-role-kind-of-nth-of-cp-roles-in-tail
  (implies (and (true-listp cps)
                (natp i)
                (<= (+ (len (seg-prefix cps ver))
                       (len (seg-window cps ver)))
                    i)
                (< i (len cps)))
           (equal (bidi-bracket-role-kind (nth i (cp-roles cps ver)))
                  :none))
  :use ((:instance bidi-class-kind-of-nth-of-cp-classes-when-role
                   (index i))
        bidi-class-kind-of-nth-of-cp-classes-in-tail)
  :disable (bidi-class-kind-of-nth-of-cp-classes-when-role
            bidi-class-kind-of-nth-of-cp-classes-in-tail))

(defrulel seg-window-when-right-to-left-free-p
  (implies (right-to-left-free-p cps ver)
           (equal (seg-window cps ver)
                  nil))
  :cases ((consp (seg-inside cps ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The bracket pairs of the text: a pair whose opening bracket is inside
; has its closing bracket inside.
; The opening bracket is in the window of a segment;
; by the third condition on the segments the closing bracket
; is in that segment, and it is not in the tail,
; whose characters are white space.

(local
 (define start-induction (segments (start natp))
   (if (endp segments)
       start
     (start-induction (cdr segments)
                      (+ (nfix start) (len (car segments)))))
   :verify-guards nil
   :hooks nil))

(defruledl nth-of-segs-marks-of-close-lemma
  (b* ((open (bracket-pair->open pair))
       (close (bracket-pair->close pair)))
    (implies (and (code-point-list-listp segments)
                  (bidi-guarded-segments-from-p segments start (list pair) ver)
                  (natp start)
                  (<= start open)
                  (< open close)
                  (equal (bidi-bracket-role-kind
                          (nth (- close start)
                               (cp-roles (acl2::flatten segments) ver)))
                         :close)
                  (not (nth (- open start) (segs-marks segments ver))))
             (not (nth (- close start) (segs-marks segments ver)))))
  :induct (start-induction segments start)
  :expand ((segs-marks segments ver)
           (acl2::flatten segments)
           (bidi-guarded-segments-from-p segments start (list pair) ver)
           (:free (start end)
                  (bidi-bracket-pairs-closed-p (list pair) start end))
           (:free (start end)
                  (bidi-bracket-pairs-closed-p nil start end)))
  :enable (start-induction nfix))

(defrulel nth-of-segs-marks-of-close
  (b* ((open (bracket-pair->open pair))
       (close (bracket-pair->close pair)))
    (implies (and (code-point-list-listp segments)
                  (bidi-guarded-segments-from-p segments 0 (list pair) ver)
                  (< open close)
                  (equal (bidi-bracket-role-kind
                          (nth close (cp-roles (acl2::flatten segments) ver)))
                         :close)
                  (not (nth open (segs-marks segments ver))))
             (not (nth close (segs-marks segments ver)))))
  :use (:instance nth-of-segs-marks-of-close-lemma (start 0)))

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

(defruledl bidi-pairs-closed-inside-p-of-segs-marks-lemma
  (implies (and (code-point-list-listp segments)
                (bidi-guarded-segments-from-p segments 0 pairs ver)
                (bidi-pairs-sound-p pairs
                                    classes
                                    (cp-roles (acl2::flatten segments) ver)))
           (bidi-pairs-closed-inside-p pairs (segs-marks segments ver)))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-closed-inside-p
           bidi-pairs-sound-p
           bidi-pair-sound-p))

(defrulel bidi-pairs-closed-inside-p-of-segs-marks
  (implies (and (code-point-list-listp segments)
                (bidi-guarded-segments-from-p
                 segments
                 0
                 (bidi-bracket-pairs classes
                                     (cp-roles (acl2::flatten segments) ver))
                 ver))
           (bidi-pairs-closed-inside-p
            (bidi-bracket-pairs classes
                                (cp-roles (acl2::flatten segments) ver))
            (segs-marks segments ver)))
  :use (:instance bidi-pairs-closed-inside-p-of-segs-marks-lemma
                  (pairs (bidi-bracket-pairs
                          classes
                          (cp-roles (acl2::flatten segments) ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The window of a segment, in a text made of what is before the segment,
; the segment, and what is after it.

; The bracket pairs fit the window (see the book bidi-guarded-neutral.lisp),
; if every pair that opens in the segment closes in it
; and every pair that closes in the segment opens in it.

(defrulel index-below-len-when-role-is-close
  (implies (equal (bidi-bracket-role-kind (nth index roles)) :close)
           (< (nfix index) (len roles)))
  :rule-classes :forward-chaining
  :use index-below-len-when-role-is-not-none)

(defruledl bidi-window-pairs-p-of-window-of-segment
  (b* ((text (append pre (append seg post)))
       (start (len pre)))
    (implies (and (code-point-listp seg)
                  (equal (len mp) (len pre))
                  (consp (seg-inside seg ver))
                  (bidi-pairs-sound-p pairs
                                      (cp-classes text ver)
                                      (cp-roles text ver))
                  (bidi-bracket-pairs-closed-p pairs start (+ start (len seg)))
                  (bidi-bracket-pairs-opened-p pairs
                                               start
                                               (+ start (len seg))))
             (bidi-window-pairs-p pairs
                                  (+ start (len (seg-prefix seg ver)))
                                  (len (seg-window seg ver))
                                  (append mp
                                          (append (seg-marks seg ver) mq)))))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-window-pairs-p
           bidi-window-pair-p
           bidi-pairs-sound-p
           bidi-pair-sound-p
           bidi-bracket-pairs-closed-p
           bidi-bracket-pairs-opened-p
           nfix))

; The pairs of a segment alone open and close in the segment.

(defrulel bidi-bracket-pairs-closed-p-when-bidi-pairs-sound-p
  (implies (and (bidi-pairs-sound-p pairs classes roles)
                (<= (len roles) (nfix end)))
           (bidi-bracket-pairs-closed-p pairs start end))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-bracket-pairs-closed-p
           bidi-pairs-sound-p
           bidi-pair-sound-p
           nfix))

(defrulel bidi-bracket-pairs-opened-p-from-0
  (bidi-bracket-pairs-opened-p pairs 0 end)
  :induct (list-induction pairs)
  :enable (list-induction bidi-bracket-pairs-opened-p))

(defrulel bidi-pairs-none-entering-p-when-bidi-bracket-pairs-opened-p
  (implies (bidi-bracket-pairs-opened-p pairs start end)
           (bidi-pairs-none-entering-p pairs start end))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-bracket-pairs-opened-p
           bidi-pairs-none-entering-p))

; The marks at the two ends of the window.
; If the segment has no prefix, the position before it, if there is one,
; is outside; and if the segment has no tail, the position after it is.

(local
 (define window-before-ok (pre seg mp ver)
   :returns (yes/no booleanp)
   (or (consp (seg-prefix seg ver))
       (not (consp pre))
       (and (nth (- (len pre) 1) mp) t))
   :verify-guards nil
   :hooks nil))

(local
 (define window-after-ok (seg post mq ver)
   :returns (yes/no booleanp)
   (or (consp (seg-tail seg ver))
       (not (consp post))
       (and (car mq) t))
   :verify-guards nil
   :hooks nil))

(defruledl bidi-window-marks-p-of-window-of-segment
  (b* ((start (len pre)))
    (implies (and (code-point-listp seg)
                  (equal (len mp) (len pre))
                  (equal (len mq) (len post))
                  (consp (seg-inside seg ver))
                  (window-before-ok pre seg mp ver)
                  (window-after-ok seg post mq ver)
                  (equal length (+ (len pre) (len seg) (len post))))
             (bidi-window-marks-p (+ start (len (seg-prefix seg ver)))
                                  (len (seg-window seg ver))
                                  (append mp (append (seg-marks seg ver) mq))
                                  length)))
  :enable (bidi-window-marks-p
           window-before-ok
           window-after-ok
           nfix
           len)
  :use (:instance seg-window-when-consp-of-seg-inside (cps seg))
  :disable seg-window-when-consp-of-seg-inside)

; The classes of the window.

(defrulel take-of-nthcdr-of-append-of-append
  (implies (true-listp b)
           (equal (take (len b)
                        (nthcdr (len a) (append a (append b c))))
                  b))
  :induct (list-induction a)
  :enable (list-induction len))

(defrulel take-of-nthcdr-of-cp-classes-of-segment
  (implies (true-listp cps)
           (equal (take (len (seg-window cps ver))
                        (nthcdr (len (seg-prefix cps ver))
                                (cp-classes cps ver)))
                  (cp-classes (seg-window cps ver) ver)))
  :use (cp-classes-of-the-parts-of-a-segment
        (:instance take-of-nthcdr-of-append-of-append
                   (a (cp-classes (seg-prefix cps ver) ver))
                   (b (cp-classes (seg-window cps ver) ver))
                   (c (cp-classes (seg-tail cps ver) ver))))
  :disable take-of-nthcdr-of-append-of-append)

(local
 (define nthcdr-induction ((n natp) x)
   (if (or (zp n)
           (atom x))
       nil
     (nthcdr-induction (- n 1) (cdr x)))
   :verify-guards nil
   :hooks nil))

(defrulel nthcdr-of-append-when-past-first
  (implies (and (natp n)
                (<= (len a) n))
           (equal (nthcdr n (append a b))
                  (nthcdr (- n (len a)) b)))
  :induct (nthcdr-induction n a)
  :enable (nthcdr-induction nthcdr len))

(local
 (define take-nthcdr-induction ((m natp) (k natp) b)
   (cond ((atom b) (list m k))
         ((not (zp k)) (take-nthcdr-induction m (- k 1) (cdr b)))
         ((not (zp m)) (take-nthcdr-induction (- m 1) k (cdr b)))
         (t nil))
   :hooks nil))

(defrulel take-of-nthcdr-of-append-when-in-first
  (implies (and (natp k)
                (natp m)
                (<= (+ k m) (len b)))
           (equal (take m (nthcdr k (append b c)))
                  (take m (nthcdr k b))))
  :induct (take-nthcdr-induction m k b)
  :enable (take-nthcdr-induction take nthcdr len nfix))

(defruledl bidi-window-of-cp-classes-of-text
  (implies (code-point-listp seg)
           (equal (bidi-window (+ (len pre) (len (seg-prefix seg ver)))
                               (len (seg-window seg ver))
                               outside
                               (cp-classes (append pre (append seg post)) ver))
                  (cp-classes (seg-window seg ver) ver)))
  :enable (bidi-window nfix))

(defruledl bidi-window-start-kind-p-of-nth-of-cp-classes-of-text
  (implies (and (code-point-listp seg)
                (consp (seg-inside seg ver)))
           (bidi-window-start-kind-p
            (bidi-class-kind
             (nth (+ (len pre) (len (seg-prefix seg ver)))
                  (cp-classes (append pre (append seg post)) ver)))))
  :enable nfix)

; The levels of the window, before rule L1, in the text.

(defruledl window-of-levels-of-segment-in-text
  (b* ((text (append pre (append seg post)))
       (classes (cp-classes text ver))
       (roles (cp-roles text ver))
       (marks (append mp (append (seg-marks seg ver) mq)))
       (pairs (bidi-bracket-pairs classes roles))
       (start (len pre))
       (n (+ start (len (seg-prefix seg ver))))
       (m (len (seg-window seg ver))))
    (implies (and (code-point-listp seg)
                  (equal (len mp) (len pre))
                  (equal (len mq) (len post))
                  (consp (seg-inside seg ver))
                  (bidi-scan-ok classes marks :free 0)
                  (bidi-pairs-closed-inside-p pairs marks)
                  (bidi-bracket-pairs-closed-p pairs start (+ start (len seg)))
                  (bidi-bracket-pairs-opened-p pairs
                                               start
                                               (+ start (len seg)))
                  (window-before-ok pre seg mp ver)
                  (window-after-ok seg post mq ver))
             (equal (bidi-window n
                                 m
                                 marks
                                 (bidi-resolve-sequence
                                  classes
                                  roles
                                  (bidi-class-left-to-right)
                                  (bidi-class-left-to-right)
                                  0))
                    (bidi-window-levels (cp-classes (seg-window seg ver) ver)
                                        pairs
                                        n))))
  :use ((:instance bidi-window-of-bidi-resolve-sequence
                   (classes (cp-classes (append pre (append seg post)) ver))
                   (roles (cp-roles (append pre (append seg post)) ver))
                   (outside (append mp (append (seg-marks seg ver) mq)))
                   (n (+ (len pre) (len (seg-prefix seg ver))))
                   (m (len (seg-window seg ver)))
                   (sos (bidi-class-left-to-right))
                   (eos (bidi-class-left-to-right)))
        (:instance bidi-window-pairs-p-of-window-of-segment
                   (pairs (bidi-bracket-pairs
                           (cp-classes (append pre (append seg post)) ver)
                           (cp-roles (append pre (append seg post)) ver))))
        (:instance bidi-window-marks-p-of-window-of-segment
                   (length (+ (len pre) (len seg) (len post)))))
  :enable (bidi-window-of-cp-classes-of-text
           bidi-window-start-kind-p-of-nth-of-cp-classes-of-text)
  :disable (cp-classes-of-append
            cp-roles-of-append))

; The same for the segment alone.

(defrulel bidi-scan-ok-of-segment-alone
  (implies (and (code-point-listp seg)
                (bidi-plain-p seg ver))
           (bidi-scan-ok (cp-classes seg ver) (seg-marks seg ver) :free 0))
  :use (:instance bidi-scan-end-of-segment-is-a-state
                  (st :free)
                  (rest nil))
  :enable (scan-invariant
           bidi-turns-left-to-right-p
           bidi-attaches-p))

(defrulel bidi-bracket-pairs-closed-p-of-bidi-bracket-pairs
  (implies (<= (len roles) (nfix end))
           (bidi-bracket-pairs-closed-p (bidi-bracket-pairs classes roles)
                                        start
                                        end))
  :use (:instance bidi-bracket-pairs-closed-p-when-bidi-pairs-sound-p
                  (pairs (bidi-bracket-pairs classes roles))))

(defrulel bidi-pairs-closed-inside-p-of-seg-marks
  (implies (code-point-listp seg)
           (bidi-pairs-closed-inside-p
            (bidi-bracket-pairs classes (cp-roles seg ver))
            (seg-marks seg ver)))
  :use (:instance bidi-pairs-closed-inside-p-of-segs-marks
                  (segments (list seg)))
  :enable (segs-marks
           acl2::flatten
           bidi-guarded-segments-from-p
           bidi-turns-left-to-right-p
           bidi-attaches-p))

(defruledl window-of-levels-of-segment-alone
  (b* ((classes (cp-classes seg ver))
       (roles (cp-roles seg ver))
       (pairs (bidi-bracket-pairs classes roles))
       (n (len (seg-prefix seg ver)))
       (m (len (seg-window seg ver))))
    (implies (and (code-point-listp seg)
                  (bidi-plain-p seg ver)
                  (consp (seg-inside seg ver)))
             (equal (bidi-window n
                                 m
                                 (seg-marks seg ver)
                                 (bidi-resolve-sequence
                                  classes
                                  roles
                                  (bidi-class-left-to-right)
                                  (bidi-class-left-to-right)
                                  0))
                    (bidi-window-levels (cp-classes (seg-window seg ver) ver)
                                        pairs
                                        n))))
  :use (:instance window-of-levels-of-segment-in-text
                  (pre nil)
                  (post nil)
                  (mp nil)
                  (mq nil))
  :enable (window-before-ok
           window-after-ok))

; The two are equal: the pairs that close in the window are the same,
; up to the position of the segment in the text.

(defruledl window-levels-of-segment-in-text-and-alone
  (b* ((text (append pre (append seg post)))
       (pairs (bidi-bracket-pairs (cp-classes text ver) (cp-roles text ver)))
       (start (len pre)))
    (implies (and (code-point-listp seg)
                  (not (bidi-bracket-pairs-overflow-p (cp-classes text ver)
                                                      (cp-roles text ver)))
                  (bidi-bracket-pairs-opened-p pairs
                                               start
                                               (+ start (len seg))))
             (equal (bidi-window-levels (cp-classes (seg-window seg ver) ver)
                                        pairs
                                        (+ start (len (seg-prefix seg ver))))
                    (bidi-window-levels (cp-classes (seg-window seg ver) ver)
                                        (bidi-bracket-pairs
                                         (cp-classes seg ver)
                                         (cp-roles seg ver))
                                        (len (seg-prefix seg ver))))))
  :use ((:instance bidi-window-levels-of-same-pairs-in-window
                   (window (cp-classes (seg-window seg ver) ver))
                   (pairs1 (bidi-bracket-pairs
                            (cp-classes (append pre (append seg post)) ver)
                            (cp-roles (append pre (append seg post)) ver)))
                   (pairs2 (bidi-bracket-pairs (cp-classes seg ver)
                                               (cp-roles seg ver)))
                   (n (len (seg-prefix seg ver)))
                   (offset (len pre)))
        (:instance bidi-pairs-closing-in-of-bidi-bracket-pairs-of-append
                   (classes1 (cp-classes pre ver))
                   (classes2 (cp-classes seg ver))
                   (classes3 (cp-classes post ver))
                   (roles1 (cp-roles pre ver))
                   (roles2 (cp-roles seg ver))
                   (roles3 (cp-roles post ver))
                   (lo (+ (len pre) (len (seg-prefix seg ver))))
                   (hi (+ (len pre)
                          (len (seg-prefix seg ver))
                          (len (seg-window seg ver)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The levels of a segment, before rule L1, in the text and alone.
; In both, the positions outside have the level 0
; (book bidi-guarded-neutral.lisp), and the window has the same levels;
; so the two lists of levels are equal.

(local
 (define two-lists-induction (x y)
   (if (and (consp x)
            (consp y))
       (two-lists-induction (cdr x) (cdr y))
     nil)
   :hooks nil))

(local
 (define three-lists-induction (x y z)
   (if (and (consp y)
            (consp z))
       (three-lists-induction (cdr x) (cdr y) (cdr z))
     nil)
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

; The levels of the positions inside.

(local
 (define inside-part (marks levels)
   (cond ((atom levels) nil)
         ((car marks) (inside-part (cdr marks) (cdr levels)))
         (t (cons (car levels)
                  (inside-part (cdr marks) (cdr levels)))))
   :measure (acl2-count levels)
   :verify-guards nil
   :hooks nil))

(defrulel equal-when-outside-zero-and-same-inside-part
  (implies (and (bidi-outside-zero-p marks levels1)
                (bidi-outside-zero-p marks levels2)
                (nat-listp levels1)
                (nat-listp levels2)
                (equal (len levels1) (len levels2))
                (equal (inside-part marks levels1)
                       (inside-part marks levels2)))
           (equal levels1 levels2))
  :rule-classes nil
  :induct (three-lists-induction marks levels1 levels2)
  :expand ((bidi-outside-zero-p marks levels1)
           (bidi-outside-zero-p marks levels2)
           (inside-part marks levels1)
           (inside-part marks levels2))
  :enable (three-lists-induction len nat-listp nfix))

(defrulel inside-part-of-run-marks-of-t
  (implies (<= (len levels) (len c))
           (equal (inside-part (run-marks c t) levels)
                  nil))
  :induct (two-lists-induction c levels)
  :expand ((run-marks c t)
           (:free (marks) (inside-part marks levels)))
  :enable (two-lists-induction len))

(defrulel inside-part-of-append-of-run-marks-of-nil
  (implies (and (<= (len b) (len levels))
                (<= (len levels) (+ (len b) (len c)))
                (true-listp levels))
           (equal (inside-part (append (run-marks b nil) (run-marks c t))
                               levels)
                  (take (len b) levels)))
  :induct (two-lists-induction b levels)
  :expand ((run-marks b nil)
           (:free (a marks) (inside-part (cons a marks) levels)))
  :enable (two-lists-induction len))

(defrulel nthcdr-of-+-of-1
  (implies (natp n)
           (equal (nthcdr (+ 1 n) x)
                  (cdr (nthcdr n x))))
  :induct (nthcdr n x)
  :enable (nthcdr natp fix))

(defrulel inside-part-of-append-of-run-marks-of-t
  (implies (<= (len a) (len levels))
           (equal (inside-part (append (run-marks a t) more) levels)
                  (inside-part more (nthcdr (len a) levels))))
  :induct (two-lists-induction a levels)
  :expand ((run-marks a t)
           (:free (a marks) (inside-part (cons a marks) levels)))
  :enable (two-lists-induction len))

(defrulel len-of-nthcdr-when-in-range
  (implies (and (natp n)
                (<= n (len x)))
           (equal (len (nthcdr n x))
                  (- (len x) n)))
  :enable nfix)

(defrulel equal-when-outside-zero-and-same-window
  (b* ((n (len (seg-prefix cps ver)))
       (m (len (seg-window cps ver))))
    (implies (and (bidi-outside-zero-p (seg-marks cps ver) levels1)
                  (bidi-outside-zero-p (seg-marks cps ver) levels2)
                  (nat-listp levels1)
                  (nat-listp levels2)
                  (equal (len levels1) (len cps))
                  (equal (len levels2) (len cps))
                  (equal (bidi-window n m nil levels1)
                         (bidi-window n m nil levels2)))
             (equal levels1 levels2)))
  :rule-classes nil
  :use (:instance equal-when-outside-zero-and-same-inside-part
                  (marks (seg-marks cps ver)))
  :enable (seg-marks bidi-window))

; The positions outside of a part of the text have the level 0.

(defrulel bidi-outside-zero-p-of-nthcdr
  (implies (bidi-outside-zero-p (append marks1 more) levels)
           (bidi-outside-zero-p more (nthcdr (len marks1) levels)))
  :rule-classes nil
  :induct (two-lists-induction marks1 levels)
  :expand ((:free (a marks) (bidi-outside-zero-p (cons a marks) levels))
           (bidi-outside-zero-p more nil)
           (append marks1 more))
  :enable (two-lists-induction len))

(defrulel bidi-outside-zero-p-of-take
  (implies (and (bidi-outside-zero-p (append marks2 more) levels)
                (<= (len marks2) (len levels)))
           (bidi-outside-zero-p marks2 (take (len marks2) levels)))
  :rule-classes nil
  :induct (two-lists-induction marks2 levels)
  :expand ((:free (a marks) (bidi-outside-zero-p (cons a marks) levels))
           (:free (levels) (bidi-outside-zero-p marks2 levels))
           (append marks2 more))
  :enable (two-lists-induction take len))

(defrulel bidi-outside-zero-p-of-middle
  (implies (and (bidi-outside-zero-p (append marks1 (append marks2 marks3))
                                     levels)
                (<= (+ (len marks1) (len marks2)) (len levels)))
           (bidi-outside-zero-p marks2
                                (take (len marks2)
                                      (nthcdr (len marks1) levels))))
  :rule-classes nil
  :use ((:instance bidi-outside-zero-p-of-nthcdr
                   (more (append marks2 marks3)))
        (:instance bidi-outside-zero-p-of-take
                   (more marks3)
                   (levels (nthcdr (len marks1) levels))))
  :enable nfix)

(local
 (define take-nthcdr-take-induction ((m natp) (k natp) (l natp) x)
   (cond ((atom x) (list m k l))
         ((not (zp k))
          (take-nthcdr-take-induction m (- k 1) (- l 1) (cdr x)))
         ((not (zp m))
          (take-nthcdr-take-induction (- m 1) k (- l 1) (cdr x)))
         (t nil))
   :verify-guards nil
   :hooks nil))

(defrulel take-of-nthcdr-of-take
  (implies (and (natp k)
                (natp m)
                (natp l)
                (<= (+ k m) l)
                (<= l (len x)))
           (equal (take m (nthcdr k (take l x)))
                  (take m (nthcdr k x))))
  :induct (take-nthcdr-take-induction m k l x)
  :enable (take-nthcdr-take-induction take nthcdr len))

(defrulel nthcdr-when-too-many
  (implies (and (true-listp x)
                (natp n)
                (<= (len x) n))
           (equal (nthcdr n x)
                  nil))
  :induct (nthcdr-induction n x)
  :enable (nthcdr-induction nthcdr len))

(defrulel nat-listp-of-take-of-nthcdr
  (implies (and (nat-listp x)
                (natp k)
                (natp l)
                (<= (+ k l) (len x)))
           (nat-listp (take l (nthcdr k x))))
  :induct (take-nthcdr-induction l k x)
  :enable (take-nthcdr-induction take nthcdr len nat-listp))

(defruledl resolved-levels-of-segment-in-text
  (b* ((text (append pre (append seg post)))
       (classes (cp-classes text ver))
       (roles (cp-roles text ver))
       (marks (append mp (append (seg-marks seg ver) mq)))
       (pairs (bidi-bracket-pairs classes roles))
       (start (len pre))
       (left (bidi-class-left-to-right)))
    (implies (and (code-point-listp seg)
                  (bidi-plain-p seg ver)
                  (equal (len mp) (len pre))
                  (equal (len mq) (len post))
                  (bidi-scan-ok classes marks :free 0)
                  (bidi-pairs-closed-inside-p pairs marks)
                  (not (bidi-bracket-pairs-overflow-p classes roles))
                  (or (not (consp (seg-inside seg ver)))
                      (and (bidi-bracket-pairs-closed-p pairs
                                                        start
                                                        (+ start (len seg)))
                           (bidi-bracket-pairs-opened-p pairs
                                                        start
                                                        (+ start (len seg)))
                           (window-before-ok pre seg mp ver)
                           (window-after-ok seg post mq ver))))
             (equal (take (len seg)
                          (nthcdr start
                                  (bidi-resolve-sequence classes
                                                         roles
                                                         left
                                                         left
                                                         0)))
                    (bidi-resolve-sequence (cp-classes seg ver)
                                           (cp-roles seg ver)
                                           left
                                           left
                                           0))))
  :use ((:instance equal-when-outside-zero-and-same-window
                   (cps seg)
                   (levels1 (take (len seg)
                                  (nthcdr (len pre)
                                          (bidi-resolve-sequence
                                           (cp-classes
                                            (append pre (append seg post))
                                            ver)
                                           (cp-roles
                                            (append pre (append seg post))
                                            ver)
                                           (bidi-class-left-to-right)
                                           (bidi-class-left-to-right)
                                           0))))
                   (levels2 (bidi-resolve-sequence
                             (cp-classes seg ver)
                             (cp-roles seg ver)
                             (bidi-class-left-to-right)
                             (bidi-class-left-to-right)
                             0)))
        (:instance bidi-outside-zero-p-of-middle
                   (marks1 mp)
                   (marks2 (seg-marks seg ver))
                   (marks3 mq)
                   (levels (bidi-resolve-sequence
                            (cp-classes (append pre (append seg post)) ver)
                            (cp-roles (append pre (append seg post)) ver)
                            (bidi-class-left-to-right)
                            (bidi-class-left-to-right)
                            0)))
        window-of-levels-of-segment-in-text
        window-of-levels-of-segment-alone
        window-levels-of-segment-in-text-and-alone)
  :enable bidi-window
  :disable (cp-classes-of-append
            cp-roles-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L1 (see the book bidi-guarded-plain.lisp).
; The rule does to a segment in the text what it does to the segment alone,
; because the white space at the end of the segment is outside,
; and so has the level 0 already.

; Where the classes are white space up to the end, the mark is T.

(local
 (define white-tails-outside-p ((classes bidi-class-listp) marks)
   :returns (yes/no booleanp)
   (or (endp classes)
       (and (or (not (bidi-all-white-p classes))
                (and (car marks) t))
            (white-tails-outside-p (cdr classes) (cdr marks))))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-trailing-zero-p-when-white-tails-outside-p
  (implies (and (bidi-outside-zero-p marks levels)
                (white-tails-outside-p classes marks)
                (<= (len classes) (len levels)))
           (bidi-trailing-zero-p classes levels))
  :rule-classes nil
  :induct (three-lists-induction marks classes levels)
  :expand ((bidi-outside-zero-p marks levels)
           (white-tails-outside-p classes marks)
           (bidi-trailing-zero-p classes levels))
  :enable (three-lists-induction len nfix))

(defrulel bidi-all-white-p-of-cp-classes
  (equal (bidi-all-white-p (cp-classes cps ver))
         (white-all-p cps ver))
  :induct (list-induction cps)
  :expand ((cp-classes cps ver)
           (white-all-p cps ver)
           (:free (a b) (bidi-all-white-p (cons a b)))
           (bidi-all-white-p nil))
  :enable (list-induction white-cp-p))

(defrulel bidi-all-white-p-of-append
  (equal (bidi-all-white-p (append x y))
         (and (bidi-all-white-p x)
              (bidi-all-white-p y)))
  :induct (list-induction x)
  :enable (list-induction bidi-all-white-p))

; No part of a window, up to its end, is all white space.

(local
 (define not-white-tail-p ((cps code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (endp cps)
       (and (not (white-all-p cps ver))
            (not-white-tail-p (cdr cps) ver)))
   :hooks nil))

(defrulel white-all-p-when-not-consp-of-trim-white
  (implies (not (consp (trim-white cps ver)))
           (white-all-p cps ver))
  :expand ((trim-white cps ver)
           (white-all-p cps ver)))

(defrulel not-white-all-p-of-trim-white
  (implies (consp (trim-white cps ver))
           (not (white-all-p (trim-white cps ver) ver)))
  :induct (list-induction cps)
  :expand ((trim-white cps ver)
           (:free (a b) (white-all-p (cons a b) ver)))
  :enable (list-induction white-all-p))

(defrulel not-white-tail-p-of-trim-white
  (not-white-tail-p (trim-white cps ver) ver)
  :induct (list-induction cps)
  :expand ((trim-white cps ver)
           (:free (a b) (not-white-tail-p (cons a b) ver))
           (not-white-tail-p nil ver))
  :enable list-induction
  :hints ('(:use not-white-all-p-of-trim-white)))

(defrulel white-tails-outside-p-of-prefix
  (equal (white-tails-outside-p (append (cp-classes p ver) rest)
                                (append (run-marks p t) more))
         (white-tails-outside-p rest more))
  :induct (list-induction p)
  :expand ((cp-classes p ver)
           (run-marks p t)
           (:free (a b c d) (white-tails-outside-p (cons a b) (cons c d))))
  :enable list-induction)

(defrulel white-tails-outside-p-of-window
  (implies (not-white-tail-p w ver)
           (equal (white-tails-outside-p (append (cp-classes w ver) rest)
                                         (append (run-marks w nil) more))
                  (white-tails-outside-p rest more)))
  :induct (list-induction w)
  :expand ((cp-classes w ver)
           (run-marks w nil)
           (not-white-tail-p w ver)
           (white-all-p w ver)
           (:free (a b c d) (white-tails-outside-p (cons a b) (cons c d)))
           (:free (a b) (bidi-all-white-p (cons a b))))
  :enable (list-induction white-cp-p))

(defrulel white-tails-outside-p-of-tail
  (white-tails-outside-p (cp-classes z ver) (run-marks z t))
  :induct (list-induction z)
  :expand ((cp-classes z ver)
           (run-marks z t)
           (:free (a b c d) (white-tails-outside-p (cons a b) (cons c d)))
           (white-tails-outside-p nil nil))
  :enable list-induction)

(defrulel white-tails-outside-p-of-parts
  (implies (not-white-tail-p w ver)
           (white-tails-outside-p
            (append (cp-classes p ver)
                    (append (cp-classes w ver)
                            (cp-classes z ver)))
            (append (run-marks p t)
                    (append (run-marks w nil)
                            (run-marks z t)))))
  :rule-classes nil)

(defrulel white-tails-outside-p-of-segment
  (implies (true-listp seg)
           (white-tails-outside-p (cp-classes seg ver) (seg-marks seg ver)))
  :use (cp-classes-of-the-parts-of-a-segment
        (:instance cp-classes-of-the-parts-of-a-segment (cps seg))
        (:instance white-tails-outside-p-of-parts
                   (p (seg-prefix seg ver))
                   (w (seg-window seg ver))
                   (z (seg-tail seg ver))))
  :enable (seg-marks seg-window))

(defrulel bidi-trailing-zero-p-of-segment
  (implies (and (true-listp seg)
                (bidi-outside-zero-p (seg-marks seg ver) levels)
                (<= (len seg) (len levels)))
           (bidi-trailing-zero-p (cp-classes seg ver) levels))
  :use (:instance bidi-trailing-zero-p-when-white-tails-outside-p
                  (marks (seg-marks seg ver))
                  (classes (cp-classes seg ver))))

(defrulel take-of-nthcdr-of-append-of-append-when-middle
  (implies (and (equal n (len a))
                (equal m (len b))
                (true-listp b))
           (equal (take m (nthcdr n (append a (append b c))))
                  b)))

(defruledl take-of-nthcdr-of-cp-classes-of-text
  (equal (take (len seg)
               (nthcdr (len pre)
                       (cp-classes (append pre (append seg post)) ver)))
         (cp-classes seg ver)))

(defrulel take-of-nthcdr-of-bidi-reset-plain
  (implies (and (equal (len levels) (len classes))
                (natp k)
                (natp l)
                (<= (+ k l) (len classes))
                (equal (take l (nthcdr k classes)) part-classes)
                (equal (take l (nthcdr k levels)) part-levels)
                (bidi-trailing-zero-p part-classes part-levels))
           (equal (take l
                        (nthcdr k
                                (mv-nth 0 (bidi-reset-plain classes levels))))
                  (mv-nth 0 (bidi-reset-plain part-classes part-levels))))
  :rule-classes nil
  :enable (nthcdr-of-bidi-reset-plain
           take-of-bidi-reset-plain
           nfix))

; The levels of a segment in the text are its levels alone.

(defruledl levels-of-segment-in-text
  (b* ((text (append pre (append seg post)))
       (classes (cp-classes text ver))
       (roles (cp-roles text ver))
       (marks (append mp (append (seg-marks seg ver) mq)))
       (pairs (bidi-bracket-pairs classes roles))
       (start (len pre)))
    (implies (and (code-point-listp seg)
                  (bidi-plain-p text ver)
                  (equal (len mp) (len pre))
                  (equal (len mq) (len post))
                  (bidi-scan-ok classes marks :free 0)
                  (bidi-pairs-closed-inside-p pairs marks)
                  (not (bidi-bracket-pairs-overflow-p classes roles))
                  (or (not (consp (seg-inside seg ver)))
                      (and (bidi-bracket-pairs-closed-p pairs
                                                        start
                                                        (+ start (len seg)))
                           (bidi-bracket-pairs-opened-p pairs
                                                        start
                                                        (+ start (len seg)))
                           (window-before-ok pre seg mp ver)
                           (window-after-ok seg post mq ver))))
             (equal (take (len seg)
                          (nthcdr start
                                  (bidi-paragraph-all-levels
                                   (code-points-to-bidi-chars text ver)
                                   0)))
                    (bidi-paragraph-all-levels
                     (code-points-to-bidi-chars seg ver)
                     0))))
  :use (resolved-levels-of-segment-in-text
        (:instance take-of-nthcdr-of-bidi-reset-plain
                   (classes (cp-classes (append pre (append seg post)) ver))
                   (levels (bidi-resolve-sequence
                            (cp-classes (append pre (append seg post)) ver)
                            (cp-roles (append pre (append seg post)) ver)
                            (bidi-class-left-to-right)
                            (bidi-class-left-to-right)
                            0))
                   (k (len pre))
                   (l (len seg))
                   (part-classes (cp-classes seg ver))
                   (part-levels (bidi-resolve-sequence
                                 (cp-classes seg ver)
                                 (cp-roles seg ver)
                                 (bidi-class-left-to-right)
                                 (bidi-class-left-to-right)
                                 0))))
  :enable (bidi-paragraph-all-levels-when-plain
           take-of-nthcdr-of-cp-classes-of-text)
  :disable (cp-classes-of-append
            cp-roles-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The levels of the text, segment after segment.

; The two ends of the window of a segment.
; If the window starts the segment, the scan reaches it in the state :FREE,
; and so the position before is outside.
; If the window ends the segment, the text that is left turns left-to-right,
; and so does not start with a window.

(defrulel last-mark-when-bidi-scan-end-is-free
  (implies (and (equal (bidi-scan-end classes outside st phase) :free)
                (consp classes))
           (nth (- (len classes) 1) outside))
  :rule-classes nil
  :induct (scan-induction classes outside st phase)
  :expand ((:free (st) (bidi-scan-end classes outside st phase)))
  :enable (scan-induction bidi-scan-step nth len))

(defrulel seg-inside-when-not-consp-of-seg-prefix
  (implies (and (not (consp (seg-prefix cps ver)))
                (true-listp cps))
           (equal (seg-inside cps ver)
                  cps))
  :expand ((seg-prefix cps ver)
           (seg-inside cps ver)
           (seg-inside nil ver)))

(defrulel window-before-ok-when-scan-invariant
  (implies (and (scan-invariant (bidi-scan-end (cp-classes pre ver) mp :free 0)
                                (append seg post)
                                ver)
                (true-listp seg)
                (consp (seg-inside seg ver)))
           (window-before-ok pre seg mp ver))
  :enable window-before-ok
  :use ((:instance scan-invariant-when-starts-with-start-cp-p
                   (st (bidi-scan-end (cp-classes pre ver) mp :free 0))
                   (cps (append seg post)))
        (:instance last-mark-when-bidi-scan-end-is-free
                   (classes (cp-classes pre ver))
                   (outside mp)
                   (st :free)
                   (phase 0))
        (:instance start-cp-p-of-car-of-seg-inside (cps seg)))
  :disable start-cp-p-of-car-of-seg-inside)

(defrulel car-of-segs-marks-when-turns-left-to-right
  (implies (and (bidi-turns-left-to-right-p (acl2::flatten segments) ver)
                (consp (acl2::flatten segments)))
           (car (segs-marks segments ver)))
  :induct (list-induction segments)
  :expand ((acl2::flatten segments)
           (segs-marks segments ver)
           (seg-prefix (car segments) ver)
           (:free (a b) (bidi-turns-left-to-right-p (cons a b) ver))
           (bidi-turns-left-to-right-p
            (append (car segments) (acl2::flatten (cdr segments)))
            ver))
  :enable (list-induction
           seg-marks
           seg-window
           seg-tail
           seg-inside
           trim-white
           white-tail
           start-cp-p
           bidi-window-start-kind-p
           run-marks))

(defrulel window-after-ok-when-turns-left-to-right
  (implies (bidi-turns-left-to-right-p (acl2::flatten rest) ver)
           (window-after-ok seg (acl2::flatten rest) (segs-marks rest ver) ver))
  :enable window-after-ok
  :disable consp-of-seg-tail)

; The levels from a segment on.

(defrulel nthcdr-in-two-parts
  (implies (and (natp k)
                (natp l)
                (<= (+ k l) (len x)))
           (equal (nthcdr k x)
                  (append (take l (nthcdr k x))
                          (nthcdr (+ k l) x))))
  :rule-classes nil
  :use (:instance acl2::append-of-take-and-nthcdr
                  (n l)
                  (x (nthcdr k x)))
  :disable acl2::append-of-take-and-nthcdr
  :enable nfix)

(defrulel segs-marks-of-append
  (equal (segs-marks (append x y) ver)
         (append (segs-marks x ver)
                 (segs-marks y ver)))
  :induct (list-induction x)
  :enable (list-induction segs-marks))

(defruledl levels-from-segment-on
  (b* ((pre (acl2::flatten done))
       (post (acl2::flatten rest))
       (text (append pre (append seg post)))
       (classes (cp-classes text ver))
       (roles (cp-roles text ver))
       (marks (append (segs-marks done ver)
                      (append (seg-marks seg ver)
                              (segs-marks rest ver))))
       (pairs (bidi-bracket-pairs classes roles))
       (start (len pre))
       (st (bidi-scan-end (cp-classes pre ver) (segs-marks done ver) :free 0))
       (levels (bidi-paragraph-all-levels (code-points-to-bidi-chars text ver)
                                          0)))
    (implies (and (code-point-listp seg)
                  (bidi-plain-p text ver)
                  (bidi-scan-ok classes marks :free 0)
                  (bidi-pairs-closed-inside-p pairs marks)
                  (not (bidi-bracket-pairs-overflow-p classes roles))
                  (scan-invariant st (append seg post) ver)
                  (or (right-to-left-free-p seg ver)
                      (and (bidi-turns-left-to-right-p post ver)
                           (not (bidi-attaches-p post ver))
                           (bidi-bracket-pairs-closed-p pairs
                                                        start
                                                        (+ start (len seg)))
                           (bidi-bracket-pairs-opened-p pairs
                                                        start
                                                        (+ start (len seg))))))
             (equal (nthcdr start levels)
                    (append (bidi-paragraph-all-levels
                             (code-points-to-bidi-chars seg ver)
                             0)
                            (nthcdr (+ start (len seg)) levels)))))
  :use ((:instance levels-of-segment-in-text
                   (pre (acl2::flatten done))
                   (post (acl2::flatten rest))
                   (mp (segs-marks done ver))
                   (mq (segs-marks rest ver)))
        (:instance nthcdr-in-two-parts
                   (x (bidi-paragraph-all-levels
                       (code-points-to-bidi-chars
                        (append (acl2::flatten done)
                                (append seg (acl2::flatten rest)))
                        ver)
                       0))
                   (k (len (acl2::flatten done)))
                   (l (len seg)))
        (:instance window-before-ok-when-scan-invariant
                   (pre (acl2::flatten done))
                   (post (acl2::flatten rest))
                   (mp (segs-marks done ver))))
  :disable (cp-classes-of-append
            cp-roles-of-append
            window-before-ok-when-scan-invariant))

(local
 (define done-todo-induction (done todo)
   (if (endp todo)
       done
     (done-todo-induction (append done (list (car todo)))
                          (cdr todo)))
   :verify-guards nil
   :hooks nil))

(defrulel true-listp-of-bidi-paragraph-all-levels
  (true-listp (bidi-paragraph-all-levels chars paragraph-level))
  :use nat-listp-of-bidi-paragraph-all-levels
  :disable nat-listp-of-bidi-paragraph-all-levels)

(defruledl levels-of-segments-lemma
  (b* ((text (acl2::flatten (append done todo)))
       (classes (cp-classes text ver))
       (roles (cp-roles text ver))
       (marks (segs-marks (append done todo) ver))
       (pairs (bidi-bracket-pairs classes roles))
       (start (len (acl2::flatten done)))
       (st (bidi-scan-end (cp-classes (acl2::flatten done) ver)
                          (segs-marks done ver)
                          :free
                          0)))
    (implies (and (code-point-list-listp done)
                  (code-point-list-listp todo)
                  (bidi-plain-p text ver)
                  (bidi-scan-ok classes marks :free 0)
                  (bidi-pairs-closed-inside-p pairs marks)
                  (not (bidi-bracket-pairs-overflow-p classes roles))
                  (bidi-guarded-segments-from-p todo start pairs ver)
                  (bidi-segments-opened-from-p todo start pairs ver)
                  (scan-invariant st (acl2::flatten todo) ver))
             (equal (nthcdr start
                            (bidi-paragraph-all-levels
                             (code-points-to-bidi-chars text ver)
                             0))
                    (bidi-levels-of-each-segment todo ver))))
  :induct (done-todo-induction done todo)
  :expand ((acl2::flatten todo)
           (segs-marks todo ver)
           (bidi-levels-of-each-segment todo ver)
           (bidi-levels-of-each-segment nil ver)
           (:free (start pairs)
                  (bidi-guarded-segments-from-p todo start pairs ver))
           (:free (start pairs)
                  (bidi-segments-opened-from-p todo start pairs ver)))
  :enable (done-todo-induction
           levels-from-segment-on
           segs-marks
           acl2::flatten))

(defruledl bidi-paragraph-all-levels-when-self-contained-lemma
  (implies (and (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-self-contained-segments-p segments ver))
           (equal (bidi-paragraph-all-levels
                   (code-points-to-bidi-chars (acl2::flatten segments) ver)
                   0)
                  (bidi-levels-of-each-segment segments ver)))
  :use (:instance levels-of-segments-lemma
                  (done nil)
                  (todo segments))
  :enable (bidi-self-contained-segments-p
           bidi-guarded-segments-p
           scan-invariant
           segs-marks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The display of the text, segment after segment.
; The cuts between the segments are clean (book bidi-guarded-theorem.lisp),
; so the characters of each segment are put in the order of display
; as they would be with the levels of the segment alone
; (book bidi-confinement.lisp), and those levels are the levels in the text.

; A plain text is one paragraph.

(defrulel bidi-paragraph-length-when-plain
  (implies (bidi-plain-p cps ver)
           (equal (bidi-paragraph-length (code-points-to-bidi-chars cps ver))
                  (len cps)))
  :induct (list-induction cps)
  :expand ((code-points-to-bidi-chars cps ver)
           (:free (a b) (bidi-paragraph-length (cons a b)))
           (bidi-paragraph-length nil))
  :enable (list-induction
           len
           code-point-bidi-char
           bidi-plain-code-point-p))

; The characters of the segments in the order of display,
; each segment with its own levels.

(local
 (define arrange-each ((segments code-point-list-listp) (ver versionp))
   :returns (shown bidi-shown-char-listp)
   (if (endp segments)
       nil
     (append (bidi-arrange-with-levels
              (car segments)
              (bidi-paragraph-all-levels
               (code-points-to-bidi-chars (car segments) ver)
               0)
              ver)
             (arrange-each (cdr segments) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-mirror-chars-of-append
  (equal (bidi-mirror-chars (append x y) ver)
         (append (bidi-mirror-chars x ver)
                 (bidi-mirror-chars y ver)))
  :induct (list-induction x)
  :enable (list-induction bidi-mirror-chars))

(defrulel bidi-display-of-each-segment-in-terms-of-arrange-each
  (implies (and (equal (paragraph-direction-kind direction) :left-to-right)
                (code-point-list-listp segments)
                (bidi-plain-p (acl2::flatten segments) ver))
           (equal (bidi-display-of-each-segment segments direction ver)
                  (bidi-mirror-chars (arrange-each segments ver) ver)))
  :induct (list-induction segments)
  :expand ((acl2::flatten segments)
           (bidi-display-of-each-segment segments direction ver)
           (bidi-display-of-each-segment nil direction ver)
           (arrange-each segments ver)
           (arrange-each nil ver))
  :enable (list-induction
           bidi-display
           bidi-arrange-paragraph
           bidi-paragraph-embedding-level
           bidi-mirror-chars))

; The cut after each segment is clean, in the levels from that segment on.

(local
 (define each-cut-clean-p ((segments code-point-list-listp) (ver versionp))
   :returns (yes/no booleanp)
   (or (endp segments)
       (and (bidi-clean-cut-p (len (car segments))
                              (bidi-levels-of-each-segment segments ver))
            (each-cut-clean-p (cdr segments) ver)))
   :verify-guards nil
   :hooks nil))

(defrulel len-of-bidi-levels-of-each-segment
  (equal (len (bidi-levels-of-each-segment segments ver))
         (len (acl2::flatten segments)))
  :induct (list-induction segments)
  :enable (list-induction
           bidi-levels-of-each-segment
           acl2::flatten))

(defrulel bidi-arrange-with-levels-of-nil
  (equal (bidi-arrange-with-levels nil nil ver)
         nil)
  :enable (bidi-arrange-with-levels
           bidi-shown-chars-at
           bidi-move-marks))

(defruledl bidi-arrange-with-levels-of-flatten
  (implies (and (code-point-list-listp segments)
                (each-cut-clean-p segments ver))
           (equal (bidi-arrange-with-levels
                   (acl2::flatten segments)
                   (bidi-levels-of-each-segment segments ver)
                   ver)
                  (arrange-each segments ver)))
  :induct (list-induction segments)
  :expand ((acl2::flatten segments)
           (bidi-levels-of-each-segment segments ver)
           (bidi-levels-of-each-segment nil ver)
           (arrange-each segments ver)
           (arrange-each nil ver)
           (each-cut-clean-p segments ver))
  :enable list-induction)

(defrulel bidi-clean-cut-p-at-the-end
  (implies (and (natp n)
                (<= (len levels) n))
           (bidi-clean-cut-p n levels))
  :enable (bidi-clean-cut-p nfix))

(defrulel bidi-clean-cut-p-of-append-of-prefix
  (implies (and (natp n)
                (bidi-clean-cut-p (+ (len prefix) n)
                                  (append prefix levels)))
           (bidi-clean-cut-p n levels))
  :rule-classes nil
  :enable (bidi-clean-cut-p nfix))

(local
 (define prefix-levels-induction (segments prefix ver)
   (if (endp segments)
       prefix
     (prefix-levels-induction
      (cdr segments)
      (append prefix
              (bidi-paragraph-all-levels
               (code-points-to-bidi-chars (car segments) ver)
               0))
      ver))
   :verify-guards nil
   :hooks nil))

(defruledl each-cut-clean-p-when-bidi-clean-cuts-p
  (implies (bidi-clean-cuts-p segments
                              (len prefix)
                              (append prefix
                                      (bidi-levels-of-each-segment segments
                                                                   ver)))
           (each-cut-clean-p segments ver))
  :induct (prefix-levels-induction segments prefix ver)
  :expand ((bidi-levels-of-each-segment segments ver)
           (bidi-levels-of-each-segment (cdr segments) ver)
           (each-cut-clean-p segments ver)
           (:free (start levels) (bidi-clean-cuts-p segments start levels))
           (:free (start levels)
                  (bidi-clean-cuts-p (cdr segments) start levels)))
  :enable prefix-levels-induction
  :hints ('(:use (:instance
                  bidi-clean-cut-p-of-append-of-prefix
                  (n (len (car segments)))
                  (levels (bidi-levels-of-each-segment segments ver))))))

(defruledl bidi-display-when-self-contained-lemma
  (implies (and (code-point-list-listp segments)
                (equal (paragraph-direction-kind direction) :left-to-right)
                (bidi-plain-p (acl2::flatten segments) ver)
                (bidi-self-contained-segments-p segments ver))
           (equal (bidi-display (acl2::flatten segments) direction ver)
                  (bidi-display-of-each-segment segments direction ver)))
  :enable (bidi-display
           bidi-arrange-paragraph
           bidi-paragraph-embedding-level
           bidi-confined-p
           bidi-self-contained-segments-p
           bidi-paragraph-all-levels-when-self-contained-lemma
           bidi-arrange-with-levels-of-flatten)
  :use ((:instance each-cut-clean-p-when-bidi-clean-cuts-p (prefix nil))
        bidi-confined-p-when-bidi-guarded-segments-p)
  :disable bidi-confined-p-when-bidi-guarded-segments-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel bidi-plain-p-of-code-point-list-fix
  (equal (bidi-plain-p (code-point-list-fix cps) ver)
         (bidi-plain-p cps ver))
  :induct (list-induction cps)
  :enable (list-induction code-point-list-fix))

(defsection bidi-self-contained-segments-theorem
  :parents (bidi-self-contained-segments)
  :short "In a plain text whose segments are self-contained,
          each segment is displayed as it is alone."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conditions on the segments
     (see @(tsee bidi-self-contained-segments-p))
     are on the bidirectional classes of the characters
     and on the bracket pairs of the text.
     By the first theorem, for a plain text (see @(tsee bidi-plain-p))
     in a paragraph whose embedding level is 0,
     every character has the level that it has
     when its segment is a paragraph of its own
     (see @(tsee bidi-levels-of-each-segment)).
     By the second theorem, the display of the text
     in a paragraph from left to right
     is the displays of its segments one after the other
     (see @(tsee bidi-display-of-each-segment)).")
   (xdoc::p
    "The proof of the first theorem follows the algorithm rule by rule,
     like the proof for guarded segments
     (see @(see bidi-guarded-segments-theorem)),
     and uses that proof.
     In each right-to-left segment, call <i>window</i> the positions
     from the first character of class @('R'), @('AL') or @('AN')
     to the last character that is not white space (class @('WS')).
     The positions of the windows are inside,
     and all the others are outside:
     so, differently from the proof for guarded segments,
     the white space at the end of a segment is outside.
     The invariant of that proof holds for these marks,
     in the text and in each segment alone,
     so the positions outside get the level 0 in both.")
   (xdoc::p
    "It is left to show that a window gets the same levels in both.
     Each rule does in a window what it does to the window alone,
     as a sequence with @('L') on both sides:
     the result in the window does not depend on what is around it.")
   (xdoc::ul
    (xdoc::li
     "Rules W1, W4 and W5 look at the class before or after a character.
      The first class of a window is @('R'), @('AL') or @('AN'),
      which those rules do not change;
      and the class after a window is not that of a number,
      nor @('ET') or @('NSM'), by the conditions on the segments.")
    (xdoc::li
     "Rules W2 and W7 look back for a strong class.
      Before a window the last one is @('L'), or there is none:
      the invariant says so.")
    (xdoc::li
     "Rule N0 treats the bracket pairs.
      A pair that closes in a window opens in the same segment,
      by the condition on the closing brackets.
      If it opens in the window, the rule finds what it looks for
      in the window, whose first class has a direction.
      If it opens before the window,
      the first position of the window is between its brackets,
      and the rule gives the pair the class @('L'),
      as in the proof for guarded segments.
      The pairs that close in a segment of the text
      are the pairs of the segment alone, at other positions:
      a closing bracket of the segment that found its opening bracket
      before the segment would make a pair that the conditions exclude,
      so the search goes on in the segment as it does alone.
      This uses that the search does not give up.")
    (xdoc::li
     "Rules N1 and N2 look for the direction on each side
      of a run of neutral characters.
      The first class of a window is not neutral,
      and after a window the direction is @('L'):
      the invariant says so in the text,
      and the segment alone ends there or goes on with white space.")
    (xdoc::li
     "Rules I1 and I2 work on each character by itself.")
    (xdoc::li
     "Rule L1 gives the level 0 to the white space
      at the end of a paragraph.
      In a segment alone that is the white space
      at the end of the segment,
      which is outside and has the level 0 in the text too."))
   (xdoc::p
    "For the second theorem, the cuts between the segments are clean,
     because the segments are guarded
     (see @(see bidi-guarded-segments-theorem));
     so rules L2 to L4 put the characters of each segment
     in the order of display as they would with the levels
     of the segment alone (see @(see bidi-clean-cut-display)),
     and those are the levels in the text by the first theorem.")
   (xdoc::p
    "The steps of the proof about the rules are in the four books
     that the proof for guarded segments uses,
     which this book includes locally:
     @('bidi-guarded-plain') (rule L1 on a part of a paragraph),
     @('bidi-guarded-weak') (windows, and rules W1 to W7),
     @('bidi-guarded-brackets') (the bracket pairs of a part of a sequence)
     and @('bidi-guarded-neutral') (rules N0 to N2, I1 and I2 in a window).
     Their definitions are for the proofs only;
     they are explained in comments
     and have no topics in this documentation."))

  (defrule bidi-paragraph-all-levels-when-bidi-self-contained-segments-p
    (implies (and (bidi-plain-p (acl2::flatten segments) ver)
                  (bidi-self-contained-segments-p segments ver))
             (equal (bidi-paragraph-all-levels
                     (code-points-to-bidi-chars (acl2::flatten segments) ver)
                     0)
                    (bidi-levels-of-each-segment segments ver)))
    :use (:instance bidi-paragraph-all-levels-when-self-contained-lemma
                    (segments (code-point-list-list-fix segments))))

  (defrule bidi-display-when-bidi-self-contained-segments-p
    (implies (and (equal (paragraph-direction-kind direction) :left-to-right)
                  (bidi-plain-p (acl2::flatten segments) ver)
                  (bidi-self-contained-segments-p segments ver))
             (equal (bidi-display (acl2::flatten segments) direction ver)
                    (bidi-display-of-each-segment segments direction ver)))
    :use (:instance bidi-display-when-self-contained-lemma
                    (segments (code-point-list-list-fix segments)))))
