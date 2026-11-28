; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-display")
(include-book "right-to-left-free")

(include-book "std/lists/flatten" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-confinement
  :parents (bidirectional-algorithm)
  :short "Confinement: when the Unicode Bidirectional Algorithm
          rearranges a text only inside the segments
          into which the text is cut."
  :long
  (xdoc::topstring
   (xdoc::p
    "A text is often made of parts that should stay apart on the display:
     the words and symbols of a formula, the fields of a record.
     The Unicode Bidirectional Algorithm [UAX #9] does not know these parts.
     It can display a character of one part in the middle of another,
     or two parts in the opposite order.
     Here a text is cut into segments, which are lists of code points,
     and it is <i>confined</i> if that does not happen.
     The library knows segments and nothing about what they stand for.")
   (xdoc::p
    "Everything here is for a text that is one paragraph
     displayed from left to right:
     the paragraph embedding level is 0.
     A cut is the place between two characters of the text.
     A cut is clean if the character before it or the character after it
     has level 0 (see @(tsee bidi-clean-cut-p)).
     Rule L2 reverses runs of characters at levels above zero,
     and such a run cannot go across a clean cut.
     So the characters displayed to the left of where the cut falls
     are the characters stored before the cut, in another order;
     that is a theorem here.
     The text is confined when the cuts between its segments are all clean
     (see @(tsee bidi-confined-p)).
     Then the display is, from left to right,
     the characters of the first segment in some order,
     then the characters of the second segment in some order, and so on.")
   (xdoc::p
    "The levels are those of every character:
     a character that rule X9 removes has the level
     that @(tsee bidi-paragraph-all-levels) gives it.")
   (xdoc::p
    "Whether a text is confined depends on those levels,
     so on the whole algorithm.
     There are conditions on the segments
     that can be checked on the bidirectional classes alone
     and under which a text is confined:
     see @(see bidi-guarded-segments).
     That they are enough is a theorem:
     see @(see bidi-guarded-segments-theorem).")
   (xdoc::p
    "In a confined text the characters of a segment are displayed together,
     but not always in the order in which the segment is displayed alone.
     With two more conditions on the bracket pairs of the text they are,
     and that is a theorem too:
     see @(see bidi-self-contained-segments)."))
  :order-subtopics (bidi-clean-cut-p
                    bidi-clean-cut-theorem
                    bidi-clean-cut-display
                    bidi-clean-cuts-p
                    bidi-confined-p
                    bidi-confined-theorem
                    bidi-guarded-segments
                    bidi-self-contained-segments)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-clean-cut-p ((n natp) (levels nat-listp))
  :returns (yes/no booleanp)
  :short "Check if the cut after a number of characters is clean,
          given the levels of the characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The cut after @('n') characters is clean
     if the character before it or the character after it has level 0,
     or if there is no character on one of its sides.
     Then no run of characters at levels above zero goes across the cut."))
  (b* ((n (lnfix n))
       (levels (nat-list-fix levels)))
    (or (equal n 0)
        (>= n (len levels))
        (equal (nth (- n 1) levels) 0)
        (equal (nth n levels) 0)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L2 does not move an item across a clean cut.
; The items before the cut and the items after it are reordered separately.

(local
 (define item-list-starts-low ((items bidi-display-item-listp))
   :returns (yes/no booleanp)
   (or (endp items)
       (equal (bidi-display-item->level (car items)) 0))
   :hooks nil))

(local
 (define item-list-ends-low ((items bidi-display-item-listp))
   :returns (yes/no booleanp)
   (cond ((endp items) t)
         ((endp (cdr items))
          (equal (bidi-display-item->level (car items)) 0))
         (t (item-list-ends-low (cdr items))))
   :hooks nil))

(defrulel item-list-ends-low-of-append
  (equal (item-list-ends-low (append x y))
         (if (consp y)
             (item-list-ends-low y)
           (item-list-ends-low x)))
  :induct (len x)
  :enable (item-list-ends-low append len))

(defrulel item-list-ends-low-of-cons
  (equal (item-list-ends-low (cons a x))
         (if (consp x)
             (item-list-ends-low x)
           (equal (bidi-display-item->level a) 0)))
  :enable item-list-ends-low)

(defrulel len-of-bidi-reverse-runs
  (equal (len (bidi-reverse-runs items level run))
         (+ (len items) (len run)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs len fix))

(defrulel consp-of-bidi-reverse-runs
  (equal (consp (bidi-reverse-runs items level run))
         (or (consp items) (consp run)))
  :induct (bidi-reverse-runs items level run)
  :enable bidi-reverse-runs)

(defrulel bidi-reverse-runs-of-append-when-starts-low
  (implies (and (posp level)
                (item-list-starts-low b))
           (equal (bidi-reverse-runs (append a b) level run)
                  (append (bidi-reverse-runs a level run)
                          (bidi-reverse-runs b level nil))))
  :induct (bidi-reverse-runs a level run)
  :enable (bidi-reverse-runs item-list-starts-low append posp nfix)
  :expand ((bidi-reverse-runs b level run)
           (bidi-reverse-runs b level nil)))

(defrulel bidi-reverse-runs-of-append-when-ends-low
  (implies (and (posp level)
                (consp a)
                (item-list-ends-low a))
           (equal (bidi-reverse-runs (append a b) level run)
                  (append (bidi-reverse-runs a level run)
                          (bidi-reverse-runs b level nil))))
  :induct (bidi-reverse-runs a level run)
  :enable (bidi-reverse-runs item-list-ends-low append posp nfix)
  :expand ((bidi-reverse-runs b level run)
           (bidi-reverse-runs b level nil)))

(defrulel item-list-starts-low-of-bidi-reverse-runs
  (implies (and (posp level)
                (item-list-starts-low items))
           (item-list-starts-low (bidi-reverse-runs items level nil)))
  :enable (bidi-reverse-runs item-list-starts-low posp nfix)
  :expand ((bidi-reverse-runs items level nil)))

(defrulel item-list-ends-low-of-bidi-reverse-runs
  (implies (and (posp level)
                (consp items)
                (item-list-ends-low items))
           (item-list-ends-low (bidi-reverse-runs items level run)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs item-list-ends-low posp nfix))

(defrulel bidi-reverse-runs-when-not-consp
  (implies (not (consp items))
           (equal (bidi-reverse-runs items level run)
                  (bidi-display-item-list-fix run)))
  :enable bidi-reverse-runs)

(defrulel item-list-starts-low-of-bidi-display-item-list-fix
  (equal (item-list-starts-low (bidi-display-item-list-fix items))
         (item-list-starts-low items))
  :enable (item-list-starts-low bidi-display-item-list-fix))

(defrulel item-list-ends-low-of-bidi-display-item-list-fix
  (equal (item-list-ends-low (bidi-display-item-list-fix items))
         (item-list-ends-low items))
  :induct (len items)
  :enable (item-list-ends-low bidi-display-item-list-fix len))

(local
 (defun reorder-two-induction (a b level lowest)
   (declare (xargs :measure (nfix level)
                   :hints (("Goal"
                            :in-theory (enable nfix fix natp o-p o-finp o<)))))
   (if (or (zp level)
           (< level (nfix lowest)))
       (list a b)
     (reorder-two-induction (bidi-reverse-runs a level nil)
                            (bidi-reverse-runs b level nil)
                            (- level 1)
                            lowest))))

(defrulel bidi-reorder-items-of-append-when-low
  (implies (and (posp lowest)
                (or (item-list-ends-low a)
                    (item-list-starts-low b)))
           (equal (bidi-reorder-items (append a b) level lowest)
                  (append (bidi-reorder-items a level lowest)
                          (bidi-reorder-items b level lowest))))
  :induct (reorder-two-induction a b level lowest)
  :enable (bidi-reorder-items posp nfix natp)
  :expand ((:free (items) (bidi-reorder-items items level lowest)))
  :hints ('(:cases ((consp a)))))

(defrulel item-list-starts-low-of-bidi-reorder-items
  (implies (and (posp lowest)
                (item-list-starts-low items))
           (item-list-starts-low (bidi-reorder-items items level lowest)))
  :induct (bidi-reorder-items items level lowest)
  :enable (bidi-reorder-items posp nfix natp)
  :expand ((bidi-reorder-items items level lowest)))

(defrulel item-list-ends-low-of-bidi-reorder-items
  (implies (and (posp lowest)
                (item-list-ends-low items))
           (item-list-ends-low (bidi-reorder-items items level lowest)))
  :induct (bidi-reorder-items items level lowest)
  :enable (bidi-reorder-items posp nfix natp)
  :expand ((bidi-reorder-items items level lowest))
  :hints ('(:cases ((consp items)))))

(defrulel bidi-reorder-items-when-not-consp
  (implies (not (consp items))
           (equal (bidi-reorder-items items level lowest)
                  nil))
  :induct (bidi-reorder-items items level lowest)
  :enable bidi-reorder-items)

(defrulel len-of-bidi-reorder-items
  (equal (len (bidi-reorder-items items level lowest))
         (len items))
  :induct (bidi-reorder-items items level lowest)
  :enable (bidi-reorder-items fix))

;;;;;;;;;;;;;;;;;;;;

; The items of a list of levels.

(defrulel fix-of-len
  (equal (fix (len x))
         (len x))
  :enable fix)

(defrulel nfix-of-+-of-1-and-nfix
  (equal (nfix (+ 1 (nfix x)))
         (+ 1 (nfix x)))
  :enable nfix)

(defrulel bidi-display-items-of-append
  (equal (bidi-display-items (append l1 l2) position)
         (append (bidi-display-items l1 position)
                 (bidi-display-items l2 (+ (nfix position) (len l1)))))
  :induct (bidi-display-items l1 position)
  :enable (bidi-display-items append len fix))

(defrulel len-of-bidi-display-items-when-nat-listp
  (implies (nat-listp levels)
           (equal (len (bidi-display-items levels position))
                  (len levels)))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items len nat-listp natp))

(defrulel bidi-display-items-when-not-consp
  (implies (not (consp levels))
           (equal (bidi-display-items levels position)
                  nil))
  :enable bidi-display-items)

(defrulel consp-of-bidi-display-items-when-nat-listp
  (implies (nat-listp levels)
           (equal (consp (bidi-display-items levels position))
                  (consp levels)))
  :enable (nat-listp natp)
  :expand ((bidi-display-items levels position)))

(defrulel bidi-display-items-under-iff-when-nat-listp
  (implies (nat-listp levels)
           (iff (bidi-display-items levels position)
                (consp levels)))
  :enable (nat-listp natp)
  :expand ((bidi-display-items levels position)))

(defrulel item-list-starts-low-of-bidi-display-items
  (implies (nat-listp levels)
           (equal (item-list-starts-low (bidi-display-items levels position))
                  (or (endp levels)
                      (equal (car levels) 0))))
  :enable (item-list-starts-low bidi-display-items nat-listp natp nfix)
  :expand ((bidi-display-items levels position)))

(defrulel item-list-ends-low-of-bidi-display-items
  (implies (nat-listp levels)
           (equal (item-list-ends-low (bidi-display-items levels position))
                  (equal (nat-list-last levels) 0)))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items nat-list-last nat-listp natp nfix))

(defrulel posp-of-bidi-lowest-odd-level
  (implies (bidi-lowest-odd-level items)
           (posp (bidi-lowest-odd-level items)))
  :induct (bidi-lowest-odd-level items)
  :enable (bidi-lowest-odd-level posp natp evenp min))

;;;;;;;;;;;;;;;;;;;;

; The order of display of two lists of levels joined at a clean cut.

(local
 (define arranged-items ((items bidi-display-item-listp)
                         (level natp)
                         (lowest? acl2::maybe-natp))
   :returns (new-items bidi-display-item-listp)
   (if lowest?
       (bidi-reorder-items items level (nfix lowest?))
     (bidi-display-item-list-fix items))
   :hooks nil))

(defrulel bidi-display-item-list-positions-of-append
  (equal (bidi-display-item-list-positions (append x y))
         (append (bidi-display-item-list-positions x)
                 (bidi-display-item-list-positions y)))
  :induct (len x)
  :enable (bidi-display-item-list-positions append len))

(defruledl bidi-order-of-levels-of-append-when-clean
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (or (equal (nat-list-last l1) 0)
                    (endp l2)
                    (equal (car l2) 0)))
           (equal (bidi-order-of-levels (append l1 l2))
                  (b* ((items (bidi-display-items (append l1 l2) 0))
                       (level (bidi-highest-level items))
                       (lowest? (bidi-lowest-odd-level items)))
                    (append (bidi-display-item-list-positions
                             (arranged-items (bidi-display-items l1 0)
                                             level
                                             lowest?))
                            (bidi-display-item-list-positions
                             (arranged-items (bidi-display-items l2 (len l1))
                                             level
                                             lowest?))))))
  :enable (bidi-order-of-levels arranged-items))

(defrulel len-of-arranged-items
  (equal (len (arranged-items items level lowest?))
         (len items))
  :enable arranged-items)

(defrulel perm-of-positions-of-arranged-items
  (acl2::perm (bidi-display-item-list-positions
               (arranged-items items level lowest?))
              (bidi-display-item-list-positions items))
  :enable arranged-items)

(defrulel item-list-starts-low-of-arranged-items
  (implies (item-list-starts-low items)
           (item-list-starts-low
            (arranged-items items level (bidi-lowest-odd-level x))))
  :enable arranged-items)

(defrulel item-list-ends-low-of-arranged-items
  (implies (item-list-ends-low items)
           (item-list-ends-low
            (arranged-items items level (bidi-lowest-odd-level x))))
  :enable arranged-items)

;;;;;;;;;;;;;;;;;;;;

; The level of an item is the level of the character at its position.
; Reordering keeps this, so the levels at the two ends of a reordered list
; of items are the levels of the characters displayed there.

(local
 (define item-matches ((item bidi-display-item-p)
                       (shown bidi-shown-char-listp))
   :returns (yes/no booleanp)
   (equal (bidi-display-item->level item)
          (bidi-shown-char->level
           (bidi-shown-char-at (bidi-display-item->position item) shown)))
   :hooks nil))

(local
 (define items-match ((items bidi-display-item-listp)
                      (shown bidi-shown-char-listp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (item-matches (car items) shown)
            (items-match (cdr items) shown)))
   :hooks nil))

(defrulel items-match-of-cons
  (equal (items-match (cons item items) shown)
         (and (item-matches item shown)
              (items-match items shown)))
  :enable items-match)

(defrulel items-match-when-not-consp
  (implies (not (consp items))
           (items-match items shown))
  :enable items-match)

(defrulel items-match-of-append
  (equal (items-match (append x y) shown)
         (and (items-match x shown)
              (items-match y shown)))
  :induct (len x)
  :enable (items-match append len))

(defrulel item-matches-of-bidi-display-item-fix
  (equal (item-matches (bidi-display-item-fix item) shown)
         (item-matches item shown))
  :enable item-matches)

(defrulel items-match-of-bidi-display-item-list-fix
  (equal (items-match (bidi-display-item-list-fix items) shown)
         (items-match items shown))
  :induct (len items)
  :enable (items-match bidi-display-item-list-fix len))

(defrulel items-match-of-bidi-reverse-runs
  (equal (items-match (bidi-reverse-runs items level run) shown)
         (and (items-match items shown)
              (items-match run shown)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs items-match))

(defrulel items-match-of-bidi-reorder-items
  (equal (items-match (bidi-reorder-items items level lowest) shown)
         (items-match items shown))
  :induct (bidi-reorder-items items level lowest)
  :enable bidi-reorder-items)

(defrulel items-match-of-arranged-items
  (equal (items-match (arranged-items items level lowest?) shown)
         (items-match items shown))
  :enable arranged-items)

(defrulel bidi-shown-char-at-of-append-of-len
  (equal (bidi-shown-char-at (len pre) (append pre shown))
         (bidi-shown-char-at 0 shown))
  :induct (len pre)
  :enable (bidi-shown-char-at append len nfix natp fix))

(local
 (defun items-match-induction (levels cps position pre)
   (if (or (atom levels)
           (atom cps))
       (list position pre)
     (items-match-induction
      (cdr levels)
      (cdr cps)
      (+ 1 (nfix position))
      (append pre
              (list (make-bidi-shown-char :code-point (car cps)
                                          :level (car levels))))))))

(defrulel items-match-of-bidi-display-items-general
  (implies (and (nat-listp levels)
                (equal (len levels) (len cps))
                (equal (nfix position) (len pre)))
           (items-match (bidi-display-items levels position)
                        (append pre (bidi-shown-chars cps levels))))
  :induct (items-match-induction levels cps position pre)
  :enable (bidi-display-items
           bidi-shown-chars
           item-matches
           bidi-shown-char-at
           nat-listp
           natp
           len
           fix))

(defrulel items-match-of-bidi-display-items-of-parts
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (equal (len cps) (+ (len l1) (len l2))))
           (and (items-match (bidi-display-items l1 0)
                             (bidi-shown-chars cps (append l1 l2)))
                (items-match (bidi-display-items l2 (len l1))
                             (bidi-shown-chars cps (append l1 l2)))))
  :use (:instance items-match-of-bidi-display-items-general
                  (levels (append l1 l2))
                  (position 0)
                  (pre nil))
  :disable items-match-of-bidi-display-items-general)

;;;;;;;;;;;;;;;;;;;;

; Rule L3 does not move a mark across a place of the display
; where the character on one side has level 0.

(local
 (define shown-starts-low ((shown bidi-shown-char-listp))
   :returns (yes/no booleanp)
   (or (endp shown)
       (equal (bidi-shown-char->level (car shown)) 0))
   :hooks nil))

(local
 (define shown-ends-low ((shown bidi-shown-char-listp))
   :returns (yes/no booleanp)
   (cond ((endp shown) t)
         ((endp (cdr shown))
          (equal (bidi-shown-char->level (car shown)) 0))
         (t (shown-ends-low (cdr shown))))
   :hooks nil))

(defrulel consp-of-bidi-shown-chars-at
  (equal (consp (bidi-shown-chars-at positions shown))
         (consp positions))
  :expand ((bidi-shown-chars-at positions shown)))

(defrulel bidi-shown-chars-at-under-iff
  (iff (bidi-shown-chars-at positions shown)
       (consp positions))
  :expand ((bidi-shown-chars-at positions shown)))

(defrulel consp-of-bidi-display-item-list-positions
  (equal (consp (bidi-display-item-list-positions items))
         (consp items))
  :expand ((bidi-display-item-list-positions items)))

(defrulel bidi-display-item-list-positions-under-iff
  (iff (bidi-display-item-list-positions items)
       (consp items))
  :expand ((bidi-display-item-list-positions items)))

(defrulel shown-starts-low-of-bidi-shown-chars-at
  (implies (and (item-list-starts-low items)
                (items-match items shown))
           (shown-starts-low
            (bidi-shown-chars-at (bidi-display-item-list-positions items)
                                 shown)))
  :enable (shown-starts-low
           item-list-starts-low
           items-match
           item-matches
           bidi-shown-chars-at
           bidi-display-item-list-positions))

(defrulel shown-ends-low-of-bidi-shown-chars-at
  (implies (and (item-list-ends-low items)
                (items-match items shown))
           (shown-ends-low
            (bidi-shown-chars-at (bidi-display-item-list-positions items)
                                 shown)))
  :induct (len items)
  :enable (shown-ends-low
           item-list-ends-low
           items-match
           item-matches
           bidi-shown-chars-at
           bidi-display-item-list-positions
           len))

(local
 (define shown-odd-p ((char bidi-shown-char-p))
   :returns (yes/no booleanp)
   (oddp (bidi-shown-char->level char))
   :hooks nil))

(local
 (std::deflist shown-list-odd-p (x)
   :guard (bidi-shown-char-listp x)
   (shown-odd-p x)))

(defrulel shown-odd-p-of-bidi-shown-char-fix
  (equal (shown-odd-p (bidi-shown-char-fix char))
         (shown-odd-p char))
  :enable shown-odd-p)

(defrulel shown-list-odd-p-of-bidi-shown-char-list-fix
  (equal (shown-list-odd-p (bidi-shown-char-list-fix x))
         (shown-list-odd-p x))
  :induct (len x)
  :enable (bidi-shown-char-list-fix len))

(defrulel bidi-move-marks-of-append-when-starts-low
  (implies (and (shown-list-odd-p pending)
                (true-listp pending)
                (shown-starts-low s2))
           (equal (bidi-move-marks (append s1 s2) pending ver)
                  (append (bidi-move-marks s1 pending ver)
                          (bidi-move-marks s2 nil ver))))
  :induct (bidi-move-marks s1 pending ver)
  :enable (bidi-move-marks shown-starts-low shown-odd-p append oddp)
  :expand ((bidi-move-marks s2 pending ver)
           (bidi-move-marks s2 nil ver)))

(defrulel bidi-move-marks-of-append-when-ends-low
  (implies (and (shown-list-odd-p pending)
                (true-listp pending)
                (consp s1)
                (shown-ends-low s1))
           (equal (bidi-move-marks (append s1 s2) pending ver)
                  (append (bidi-move-marks s1 pending ver)
                          (bidi-move-marks s2 nil ver))))
  :induct (bidi-move-marks s1 pending ver)
  :enable (bidi-move-marks shown-ends-low shown-odd-p append oddp)
  :expand ((bidi-move-marks s2 pending ver)
           (bidi-move-marks s2 nil ver)))

(defrulel bidi-move-marks-of-append-when-low
  (implies (or (shown-ends-low s1)
               (shown-starts-low s2))
           (equal (bidi-move-marks (append s1 s2) nil ver)
                  (append (bidi-move-marks s1 nil ver)
                          (bidi-move-marks s2 nil ver))))
  :cases ((consp s1))
  :enable bidi-move-marks)

;;;;;;;;;;;;;;;;;;;;

; The characters of a paragraph in the order of display, at a clean cut.

(defrulel bidi-shown-chars-at-of-append
  (equal (bidi-shown-chars-at (append p1 p2) shown)
         (append (bidi-shown-chars-at p1 shown)
                 (bidi-shown-chars-at p2 shown)))
  :induct (len p1)
  :enable (bidi-shown-chars-at append len))

(local
 (define arranged-shown ((part bidi-display-item-listp)
                         (levels nat-listp)
                         (cps code-point-listp))
   :returns (shown bidi-shown-char-listp)
   (b* ((items (bidi-display-items levels 0)))
     (bidi-shown-chars-at
      (bidi-display-item-list-positions
       (arranged-items part
                       (bidi-highest-level items)
                       (bidi-lowest-odd-level items)))
      (bidi-shown-chars cps levels)))
   :verify-guards nil
   :hooks nil))

(defruledl bidi-move-marks-of-arranged-when-clean
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (equal (len cps) (+ (len l1) (len l2)))
                (or (equal (nat-list-last l1) 0)
                    (equal (car l2) 0)))
           (equal (bidi-move-marks
                   (bidi-shown-chars-at (bidi-order-of-levels (append l1 l2))
                                        (bidi-shown-chars cps (append l1 l2)))
                   nil
                   ver)
                  (append
                   (bidi-move-marks
                    (arranged-shown (bidi-display-items l1 0)
                                    (append l1 l2)
                                    cps)
                    nil
                    ver)
                   (bidi-move-marks
                    (arranged-shown (bidi-display-items l2 (len l1))
                                    (append l1 l2)
                                    cps)
                    nil
                    ver))))
  :enable (bidi-order-of-levels-of-append-when-clean
           arranged-shown)
  :cases ((equal (nat-list-last l1) 0)))

(defrulel len-of-bidi-display-item-list-positions
  (equal (len (bidi-display-item-list-positions items))
         (len items))
  :induct (len items)
  :enable (bidi-display-item-list-positions len))

(defrulel len-of-bidi-move-marks-of-arranged-shown
  (equal (len (bidi-move-marks (arranged-shown part levels cps) nil ver))
         (len part))
  :enable arranged-shown)

(local
 (defun take-induction (n cps levels)
   (if (or (zp n)
           (atom cps)
           (atom levels))
       nil
     (take-induction (- n 1) (cdr cps) (cdr levels)))))

(defrulel bidi-shown-char-list-code-points-of-take-of-bidi-shown-chars
  (implies (and (natp n)
                (<= n (len cps))
                (equal (len levels) (len cps)))
           (equal (bidi-shown-char-list-code-points
                   (take n (bidi-shown-chars cps levels)))
                  (take n (code-point-list-fix cps))))
  :induct (take-induction n cps levels)
  :enable (bidi-shown-chars
           bidi-shown-char-list-code-points
           code-point-list-fix
           take
           len
           natp
           fix))

(defruledl perm-of-code-points-of-first-part
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (equal (len cps) (+ (len l1) (len l2))))
           (acl2::perm (bidi-shown-char-list-code-points
                        (bidi-move-marks
                         (arranged-shown (bidi-display-items l1 0)
                                         (append l1 l2)
                                         cps)
                         nil
                         ver))
                       (take (len l1) (code-point-list-fix cps))))
  :enable (arranged-shown
           bidi-display-item-list-positions-of-bidi-display-items
           bidi-shown-chars-at-of-bidi-positions-with-level-when-shorter))

(defrulel nat-list-last-of-take
  (implies (and (nat-listp levels)
                (posp n)
                (<= n (len levels)))
           (equal (nat-list-last (take n levels))
                  (nth (- n 1) levels)))
  :induct (take n levels)
  :enable (nat-list-last take nth len posp natp nat-listp fix nfix))

(defrulel nat-listp-of-take-when-nat-listp
  (implies (and (nat-listp x)
                (<= (nfix n) (len x)))
           (nat-listp (take n x)))
  :induct (take n x)
  :enable (take nat-listp len nfix natp fix))

(defrulel nat-listp-of-nthcdr-when-nat-listp
  (implies (nat-listp x)
           (nat-listp (nthcdr n x)))
  :induct (nthcdr n x)
  :enable (nthcdr nat-listp))

(defruledl perm-of-take-of-arranged-when-clean
  (implies (and (nat-listp levels)
                (equal (len levels) (len cps))
                (posp n)
                (< n (len cps))
                (or (equal (nth (- n 1) levels) 0)
                    (equal (nth n levels) 0)))
           (acl2::perm
            (bidi-shown-char-list-code-points
             (take n
                   (bidi-move-marks
                    (bidi-shown-chars-at (bidi-order-of-levels levels)
                                         (bidi-shown-chars cps levels))
                    nil
                    ver)))
            (take n (code-point-list-fix cps))))
  :use ((:instance bidi-move-marks-of-arranged-when-clean
                   (l1 (take n levels))
                   (l2 (nthcdr n levels)))
        (:instance perm-of-code-points-of-first-part
                   (l1 (take n levels))
                   (l2 (nthcdr n levels))))
  :enable (posp natp nfix fix))

(defruledl perm-of-take-of-bidi-arrange-paragraph-in-the-middle
  (implies (and (equal (paragraph-direction-kind direction) :left-to-right)
                (posp n)
                (< n (len cps))
                (or (equal (nth (- n 1)
                                (bidi-paragraph-all-levels
                                 (code-points-to-bidi-chars cps ver)
                                 0))
                           0)
                    (equal (nth n
                                (bidi-paragraph-all-levels
                                 (code-points-to-bidi-chars cps ver)
                                 0))
                           0)))
           (acl2::perm
            (bidi-shown-char-list-code-points
             (take n (bidi-arrange-paragraph cps direction ver)))
            (take n (code-point-list-fix cps))))
  :enable (bidi-arrange-paragraph
           bidi-arrange-with-levels
           bidi-paragraph-embedding-level
           perm-of-take-of-arranged-when-clean))

(defrulel perm-of-take-of-bidi-arrange-paragraph-at-the-end
  (acl2::perm
   (bidi-shown-char-list-code-points
    (take (len cps) (bidi-arrange-paragraph cps direction ver)))
   (code-point-list-fix cps)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-clean-cut-theorem
  :short "At a clean cut, the characters displayed on the left
          are the characters stored before the cut, in another order."
  :long
  (xdoc::topstring
   (xdoc::p
    "The text is one paragraph from left to right,
     and its cut after @('n') characters is clean
     (see @(tsee bidi-clean-cut-p)).
     Then the first @('n') characters of the paragraph
     in the order of display (see @(tsee bidi-arrange-paragraph))
     have the code points of the first @('n') characters of the text,
     in another order:
     the two lists are related by @('perm'),
     the relation of the ACL2 library @('[books]/kestrel/lists-light').
     So the characters after the cut are displayed after them,
     and no character is displayed on the other side of the cut.")
   (xdoc::p
    "This is before rule L4 [UAX #9],
     which replaces some characters by their mirror images
     without moving them (see @(tsee bidi-display))."))

  (defrule perm-of-take-of-bidi-arrange-paragraph-when-bidi-clean-cut-p
    (implies (and (equal (paragraph-direction-kind direction)
                         :left-to-right)
                  (bidi-clean-cut-p
                   n
                   (bidi-paragraph-all-levels
                    (code-points-to-bidi-chars cps ver)
                    0))
                  (natp n)
                  (<= n (len cps)))
             (acl2::perm
              (bidi-shown-char-list-code-points
               (take n (bidi-arrange-paragraph cps direction ver)))
              (take n (code-point-list-fix cps))))
    :enable (bidi-clean-cut-p
             perm-of-take-of-bidi-arrange-paragraph-in-the-middle
             posp
             natp
             nfix)
    :cases ((equal n 0)
            (equal n (len cps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The two parts of a paragraph joined at a clean cut
; are each put in the order of display as they would be alone.
;
; By what is above, rule L2 reorders the items of each part separately,
; but from the highest level of the whole paragraph
; down to its lowest odd level.
; It remains to see that the items of a part are reordered the same way
; from their own highest level down to their own lowest odd level.
; Above their highest level, no run is reversed.
; Below their lowest odd level, the levels go two by two,
; an even level and then the odd level under it, which no item has:
; the runs for the two levels are the same, and are reversed twice.

(defrulel fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :enable fix)

; Every item has a level under a bound.

(local
 (define items-below-level ((items bidi-display-item-listp) (level natp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (< (bidi-display-item->level (car items)) (lnfix level))
            (items-below-level (cdr items) level)))
   :hooks nil))

(defrulel bidi-reverse-runs-when-items-below-level
  (implies (items-below-level items level)
           (equal (bidi-reverse-runs items level run)
                  (append (bidi-display-item-list-fix run)
                          (bidi-display-item-list-fix items))))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs
           items-below-level
           bidi-display-item-list-fix))

(defrulel items-below-level-when-above-highest
  (implies (and (natp level)
                (< (bidi-highest-level items) level))
           (items-below-level items level))
  :induct (len items)
  :enable (items-below-level bidi-highest-level len max nfix))

(defrulel bidi-highest-level-of-bidi-display-item-list-fix
  (equal (bidi-highest-level (bidi-display-item-list-fix items))
         (bidi-highest-level items)))

(defruledl bidi-reorder-items-of-level-above
  (implies (and (natp level)
                (< (bidi-highest-level items) level))
           (equal (bidi-reorder-items items level lowest)
                  (bidi-reorder-items items (- level 1) lowest)))
  :expand ((bidi-reorder-items items level lowest)
           (bidi-reorder-items items (+ -1 level) lowest))
  :enable (nfix natp))

(local
 (defun count-down-induction (n)
   (if (zp n)
       nil
     (count-down-induction (- n 1)))))

(defruledl bidi-reorder-items-of-levels-above
  (implies (and (natp level)
                (natp more)
                (<= (bidi-highest-level items) level))
           (equal (bidi-reorder-items items (+ level more) lowest)
                  (bidi-reorder-items items level lowest)))
  :induct (count-down-induction more)
  :enable (count-down-induction
           bidi-reorder-items-of-level-above
           natp
           fix))

(defruledl bidi-reorder-items-from-above
  (implies (and (natp level)
                (<= (bidi-highest-level items) level))
           (equal (bidi-reorder-items items level lowest)
                  (bidi-reorder-items items
                                      (bidi-highest-level items)
                                      lowest)))
  :use (:instance bidi-reorder-items-of-levels-above
                  (level (bidi-highest-level items))
                  (more (- level (bidi-highest-level items))))
  :enable natp)

; No item has a given level.

(local
 (define items-miss-level ((items bidi-display-item-listp) (level natp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (not (equal (bidi-display-item->level (car items))
                        (lnfix level)))
            (items-miss-level (cdr items) level)))
   :hooks nil))

(defrulel items-miss-level-of-append
  (equal (items-miss-level (append x y) level)
         (and (items-miss-level x level)
              (items-miss-level y level)))
  :induct (len x)
  :enable (items-miss-level append len))

(defrulel items-miss-level-of-bidi-display-item-list-fix
  (equal (items-miss-level (bidi-display-item-list-fix items) level)
         (items-miss-level items level))
  :induct (len items)
  :enable (items-miss-level bidi-display-item-list-fix len))

(defrulel items-miss-level-of-cons
  (equal (items-miss-level (cons item items) level)
         (and (not (equal (bidi-display-item->level item) (nfix level)))
              (items-miss-level items level)))
  :enable items-miss-level)

(defrulel items-miss-level-of-nil
  (items-miss-level nil level)
  :enable items-miss-level)

(defrulel items-miss-level-of-bidi-reverse-runs
  (equal (items-miss-level (bidi-reverse-runs items level run) other)
         (and (items-miss-level items other)
              (items-miss-level run other)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs items-miss-level))

; If no item has the level under a level,
; the runs for the two levels are the same.

(defrulel bidi-reverse-runs-of-level-under-when-items-miss-level
  (implies (and (posp level)
                (items-miss-level items (- level 1)))
           (equal (bidi-reverse-runs items (- level 1) run)
                  (bidi-reverse-runs items level run)))
  :induct (bidi-reverse-runs items level run)
  :expand ((bidi-reverse-runs items level run)
           (bidi-reverse-runs items (+ -1 level) run))
  :enable ((:induction bidi-reverse-runs)
           items-miss-level posp nfix natp))

; Reversing the runs twice gives the list back.

(local
 (define items-at-least ((items bidi-display-item-listp) (level natp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (>= (bidi-display-item->level (car items)) (lnfix level))
            (items-at-least (cdr items) level)))
   :hooks nil))

(defrulel items-at-least-of-bidi-display-item-list-fix
  (equal (items-at-least (bidi-display-item-list-fix items) level)
         (items-at-least items level))
  :induct (len items)
  :enable (items-at-least bidi-display-item-list-fix len))

(defrulel bidi-reverse-runs-of-append-of-run-and-low
  (implies (and (items-at-least a level)
                (< (bidi-display-item->level x) (nfix level)))
           (equal (bidi-reverse-runs (append a (cons x y)) level run)
                  (append (rev (bidi-display-item-list-fix a))
                          (bidi-display-item-list-fix run)
                          (cons (bidi-display-item-fix x)
                                (bidi-reverse-runs y level nil)))))
  :induct (bidi-reverse-runs a level run)
  :expand ((:free (b) (bidi-reverse-runs (cons x y) level b)))
  :enable (bidi-reverse-runs
           items-at-least
           bidi-display-item-list-fix
           append
           rev))

(defrulel bidi-reverse-runs-when-items-at-least
  (implies (items-at-least a level)
           (equal (bidi-reverse-runs a level run)
                  (append (rev (bidi-display-item-list-fix a))
                          (bidi-display-item-list-fix run))))
  :induct (bidi-reverse-runs a level run)
  :enable (bidi-reverse-runs
           items-at-least
           bidi-display-item-list-fix
           rev))

(defrulel bidi-reverse-runs-of-bidi-reverse-runs
  (implies (items-at-least run level)
           (equal (bidi-reverse-runs (bidi-reverse-runs items level run)
                                     level
                                     nil)
                  (append (rev (bidi-display-item-list-fix run))
                          (bidi-display-item-list-fix items))))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs
           items-at-least
           bidi-display-item-list-fix
           rev))

(defrulel bidi-reverse-runs-twice-at-two-levels
  (implies (and (posp level)
                (items-miss-level items (- level 1)))
           (equal (bidi-reverse-runs (bidi-reverse-runs items level nil)
                                     (- level 1)
                                     nil)
                  (bidi-display-item-list-fix items)))
  :enable items-at-least)

; No item has an odd level under a bound.

(local
 (define items-miss-odd-below ((items bidi-display-item-listp) (bound natp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (not (and (oddp (bidi-display-item->level (car items)))
                      (< (bidi-display-item->level (car items))
                         (lnfix bound))))
            (items-miss-odd-below (cdr items) bound)))
   :hooks nil))

(defrulel items-miss-level-when-items-miss-odd-below
  (implies (and (items-miss-odd-below items bound)
                (natp level)
                (oddp level)
                (< level (nfix bound)))
           (items-miss-level items level))
  :induct (len items)
  :enable (items-miss-odd-below items-miss-level len nfix))

(defrulel items-miss-odd-below-when-lower
  (implies (and (items-miss-odd-below items bound)
                (<= (nfix lower) (nfix bound)))
           (items-miss-odd-below items lower))
  :induct (len items)
  :enable (items-miss-odd-below len nfix))

(defrulel items-miss-odd-below-of-append
  (equal (items-miss-odd-below (append x y) bound)
         (and (items-miss-odd-below x bound)
              (items-miss-odd-below y bound)))
  :induct (len x)
  :enable (items-miss-odd-below append len))

(defrulel items-miss-odd-below-of-bidi-display-item-list-fix
  (equal (items-miss-odd-below (bidi-display-item-list-fix items) bound)
         (items-miss-odd-below items bound))
  :induct (len items)
  :enable (items-miss-odd-below bidi-display-item-list-fix len))

(defrulel items-miss-odd-below-of-bidi-reverse-runs
  (equal (items-miss-odd-below (bidi-reverse-runs items level run) bound)
         (and (items-miss-odd-below items bound)
              (items-miss-odd-below run bound)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs items-miss-odd-below))

; From an even level down, two levels at a time.

(local
 (defun two-levels-induction (items level)
   (declare (xargs :measure (nfix level)
                   :hints (("Goal"
                            :in-theory (enable nfix fix natp o-p o-finp o<)))))
   (if (or (zp level)
           (zp (- level 1)))
       items
     (two-levels-induction items (- level 2)))))

(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))

(defrulel items-miss-odd-below-of-nil
  (items-miss-odd-below nil bound)
  :enable items-miss-odd-below)

(defrulel bidi-reorder-items-when-level-below-lowest
  (implies (< (nfix level) (nfix lowest))
           (equal (bidi-reorder-items items level lowest)
                  (bidi-display-item-list-fix items)))
  :expand (bidi-reorder-items items level lowest))

(defrulel bidi-reorder-items-of-level-0
  (equal (bidi-reorder-items items 0 lowest)
         (bidi-display-item-list-fix items))
  :expand (bidi-reorder-items items 0 lowest))

(defruledl bidi-reorder-items-when-no-odd-level-below
  (implies (and (natp level)
                (evenp level)
                (posp lowest)
                (oddp lowest)
                (items-miss-odd-below items (+ 1 level)))
           (equal (bidi-reorder-items items level lowest)
                  (bidi-display-item-list-fix items)))
  :induct (two-levels-induction items level)
  :expand ((bidi-reorder-items items level lowest)
           (bidi-reorder-items (bidi-reverse-runs items level nil)
                               (+ -1 level)
                               lowest))
  :enable (oddp nfix natp posp))

; From the lowest odd level of the items down to a lower odd level.

(defruledl bidi-reorder-items-to-lower-odd-level
  (implies (and (natp level)
                (posp lower)
                (oddp lower)
                (posp lowest)
                (oddp lowest)
                (<= lower lowest)
                (<= lowest level)
                (items-miss-odd-below items lowest))
           (equal (bidi-reorder-items items level lower)
                  (bidi-reorder-items items level lowest)))
  :induct (bidi-reorder-items items level lowest)
  :expand ((:free (lowest) (bidi-reorder-items items level lowest)))
  :enable ((:induction bidi-reorder-items)
           bidi-reorder-items-when-no-odd-level-below
           oddp nfix natp posp))

; The lowest odd level of the items.

(defrulel oddp-of-bidi-lowest-odd-level
  (implies (bidi-lowest-odd-level items)
           (oddp (bidi-lowest-odd-level items)))
  :induct (len items)
  :enable (bidi-lowest-odd-level len min oddp))

(defrulel items-miss-odd-below-of-bidi-lowest-odd-level
  (implies (or (not (bidi-lowest-odd-level items))
               (<= (nfix bound) (bidi-lowest-odd-level items)))
           (items-miss-odd-below items bound))
  :induct (len items)
  :enable (bidi-lowest-odd-level items-miss-odd-below len min oddp nfix))

(defrulel bidi-lowest-odd-level-upper-bound
  (implies (bidi-lowest-odd-level items)
           (<= (bidi-lowest-odd-level items)
               (bidi-highest-level items)))
  :rule-classes :linear
  :induct (len items)
  :enable (bidi-lowest-odd-level bidi-highest-level len min max))

(defrulel evenp-of-bidi-highest-level-when-no-odd-level
  (implies (not (bidi-lowest-odd-level items))
           (evenp (bidi-highest-level items)))
  :induct (len items)
  :enable (bidi-lowest-odd-level bidi-highest-level len min max))

; The items of a part are reordered with the levels of the whole
; as they are with their own.

(defruledl arranged-items-with-other-levels
  (implies (and (natp level)
                (<= (bidi-highest-level items) level)
                (or (not lowest?)
                    (and (posp lowest?)
                         (oddp lowest?)))
                (or lowest?
                    (not (bidi-lowest-odd-level items)))
                (or (not lowest?)
                    (not (bidi-lowest-odd-level items))
                    (<= lowest? (bidi-lowest-odd-level items))))
           (equal (arranged-items items level lowest?)
                  (arranged-items items
                                  (bidi-highest-level items)
                                  (bidi-lowest-odd-level items))))
  :enable (arranged-items nfix)
  :use ((:instance bidi-reorder-items-from-above
                   (lowest lowest?))
        (:instance bidi-reorder-items-to-lower-odd-level
                   (level (bidi-highest-level items))
                   (lower lowest?)
                   (lowest (bidi-lowest-odd-level items)))
        (:instance bidi-reorder-items-when-no-odd-level-below
                   (level (bidi-highest-level items))
                   (lowest lowest?))))

(defrulel bidi-highest-level-of-append
  (equal (bidi-highest-level (append x y))
         (max (bidi-highest-level x)
              (bidi-highest-level y)))
  :induct (len x)
  :enable (bidi-highest-level append len max))

(defrulel bidi-lowest-odd-level-is-positive-or-nil
  (or (not (bidi-lowest-odd-level items))
      (and (integerp (bidi-lowest-odd-level items))
           (< 0 (bidi-lowest-odd-level items))))
  :rule-classes :type-prescription
  :use posp-of-bidi-lowest-odd-level
  :disable posp-of-bidi-lowest-odd-level
  :enable posp)

(defrulel bidi-lowest-odd-level-of-append
  (equal (bidi-lowest-odd-level (append x y))
         (cond ((not (bidi-lowest-odd-level x)) (bidi-lowest-odd-level y))
               ((not (bidi-lowest-odd-level y)) (bidi-lowest-odd-level x))
               (t (min (bidi-lowest-odd-level x)
                       (bidi-lowest-odd-level y)))))
  :induct (len x)
  :enable (bidi-lowest-odd-level append len min))

;;;;;;;;;;;;;;;;;;;;

; The items of the second part have positions
; that start at the length of the first part.

(local
 (define shift-items ((items bidi-display-item-listp) (offset natp))
   :returns (new-items bidi-display-item-listp)
   (if (endp items)
       nil
     (cons (make-bidi-display-item
            :position (+ (bidi-display-item->position (car items))
                         (lnfix offset))
            :level (bidi-display-item->level (car items)))
           (shift-items (cdr items) offset)))
   :hooks nil))

(defrulel shift-items-of-append
  (equal (shift-items (append x y) offset)
         (append (shift-items x offset)
                 (shift-items y offset)))
  :induct (len x)
  :enable (shift-items append len))

(defrulel shift-items-of-bidi-display-item-list-fix
  (equal (shift-items (bidi-display-item-list-fix items) offset)
         (shift-items items offset))
  :induct (len items)
  :enable (shift-items bidi-display-item-list-fix len))

(defruledl bidi-display-items-of-+
  (implies (and (natp position)
                (natp offset))
           (equal (bidi-display-items levels (+ position offset))
                  (shift-items (bidi-display-items levels position) offset)))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items shift-items natp nfix))

(defruledl bidi-display-items-in-terms-of-shift-items
  (implies (natp offset)
           (equal (bidi-display-items levels offset)
                  (shift-items (bidi-display-items levels 0) offset)))
  :use (:instance bidi-display-items-of-+ (position 0)))

(defrulel bidi-reverse-runs-of-shift-items
  (equal (bidi-reverse-runs (shift-items items offset)
                            level
                            (shift-items run offset))
         (shift-items (bidi-reverse-runs items level run) offset))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs shift-items nfix))

(defrulel bidi-reverse-runs-of-shift-items-and-nil
  (equal (bidi-reverse-runs (shift-items items offset) level nil)
         (shift-items (bidi-reverse-runs items level nil) offset))
  :use (:instance bidi-reverse-runs-of-shift-items (run nil))
  :disable bidi-reverse-runs-of-shift-items
  :enable shift-items)

(defrulel bidi-reorder-items-of-shift-items
  (equal (bidi-reorder-items (shift-items items offset) level lowest)
         (shift-items (bidi-reorder-items items level lowest) offset))
  :induct (bidi-reorder-items items level lowest)
  :enable bidi-reorder-items)

(defrulel arranged-items-of-shift-items
  (equal (arranged-items (shift-items items offset) level lowest?)
         (shift-items (arranged-items items level lowest?) offset))
  :enable arranged-items)

(defrulel bidi-display-item-list-positions-of-shift-items
  (equal (bidi-display-item-list-positions (shift-items items offset))
         (nat-list-add (bidi-display-item-list-positions items) offset))
  :induct (len items)
  :enable (shift-items
           bidi-display-item-list-positions
           nat-list-add
           len
           nfix))

(defrulel bidi-highest-level-of-shift-items
  (equal (bidi-highest-level (shift-items items offset))
         (bidi-highest-level items))
  :induct (len items)
  :enable (shift-items bidi-highest-level len nfix))

(defrulel bidi-lowest-odd-level-of-shift-items
  (equal (bidi-lowest-odd-level (shift-items items offset))
         (bidi-lowest-odd-level items))
  :induct (len items)
  :enable (shift-items bidi-lowest-odd-level len nfix))

; The characters with their levels, for the two parts.

(local
 (defun two-lists-induction (x y)
   (if (or (atom x)
           (atom y))
       nil
     (two-lists-induction (cdr x) (cdr y)))))

(defrulel bidi-shown-chars-of-append
  (implies (equal (len cps1) (len levels1))
           (equal (bidi-shown-chars (append cps1 cps2)
                                    (append levels1 levels2))
                  (append (bidi-shown-chars cps1 levels1)
                          (bidi-shown-chars cps2 levels2))))
  :induct (two-lists-induction cps1 levels1)
  :enable (bidi-shown-chars append len))

(defrulel nfix-of-len
  (equal (nfix (len x))
         (len x))
  :enable nfix)

(defrulel bidi-shown-char-at-of-+-of-len-of-append
  (equal (bidi-shown-char-at (+ (len pre) (nfix position))
                             (append pre shown))
         (bidi-shown-char-at position shown))
  :induct (len pre)
  :enable (bidi-shown-char-at append len nfix natp fix))

(defrulel bidi-shown-chars-at-of-nat-list-add-of-append
  (implies (equal (len pre) offset)
           (equal (bidi-shown-chars-at (nat-list-add positions offset)
                                       (append pre shown))
                  (bidi-shown-chars-at positions shown)))
  :induct (len positions)
  :enable (bidi-shown-chars-at nat-list-add len))

; The positions of the items of the first part
; are under the length of that part.

(local
 (define items-positions-below ((items bidi-display-item-listp)
                                (bound natp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (< (bidi-display-item->position (car items)) (lnfix bound))
            (items-positions-below (cdr items) bound)))
   :hooks nil))

(defrulel items-positions-below-of-append
  (equal (items-positions-below (append x y) bound)
         (and (items-positions-below x bound)
              (items-positions-below y bound)))
  :induct (len x)
  :enable (items-positions-below append len))

(defrulel items-positions-below-of-bidi-display-item-list-fix
  (equal (items-positions-below (bidi-display-item-list-fix items) bound)
         (items-positions-below items bound))
  :induct (len items)
  :enable (items-positions-below bidi-display-item-list-fix len))

(defrulel items-positions-below-of-nil
  (items-positions-below nil bound)
  :enable items-positions-below)

(defrulel items-positions-below-of-bidi-reverse-runs
  (equal (items-positions-below (bidi-reverse-runs items level run) bound)
         (and (items-positions-below items bound)
              (items-positions-below run bound)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs items-positions-below))

(defrulel items-positions-below-of-bidi-reorder-items
  (equal (items-positions-below (bidi-reorder-items items level lowest)
                                bound)
         (items-positions-below items bound))
  :induct (bidi-reorder-items items level lowest)
  :enable bidi-reorder-items)

(defrulel items-positions-below-of-arranged-items
  (equal (items-positions-below (arranged-items items level lowest?) bound)
         (items-positions-below items bound))
  :enable arranged-items)

(defrulel items-positions-below-of-bidi-display-items
  (implies (and (natp position)
                (<= (+ position (len levels)) (nfix bound)))
           (items-positions-below (bidi-display-items levels position)
                                  bound))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items items-positions-below len nfix natp))

(defrulel bidi-shown-char-at-of-append-when-below
  (implies (and (natp position)
                (< position (len shown)))
           (equal (bidi-shown-char-at position (append shown post))
                  (bidi-shown-char-at position shown)))
  :induct (bidi-shown-char-at position shown)
  :enable (bidi-shown-char-at append len nfix))

(defrulel bidi-shown-chars-at-of-positions-of-append-when-below
  (implies (items-positions-below items (len shown))
           (equal (bidi-shown-chars-at
                   (bidi-display-item-list-positions items)
                   (append shown post))
                  (bidi-shown-chars-at
                   (bidi-display-item-list-positions items)
                   shown)))
  :induct (len items)
  :enable (bidi-shown-chars-at
           bidi-display-item-list-positions
           items-positions-below
           len))

; The two parts.

(defruledl bidi-order-of-levels-in-terms-of-arranged-items
  (equal (bidi-order-of-levels levels)
         (b* ((items (bidi-display-items levels 0)))
           (bidi-display-item-list-positions
            (arranged-items items
                            (bidi-highest-level items)
                            (bidi-lowest-odd-level items)))))
  :enable (bidi-order-of-levels arranged-items))

(defruledl arranged-shown-of-first-part
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (equal (len c1) (len l1)))
           (equal (arranged-shown (bidi-display-items l1 0)
                                  (append l1 l2)
                                  (append c1 c2))
                  (bidi-shown-chars-at (bidi-order-of-levels l1)
                                       (bidi-shown-chars c1 l1))))
  :enable (arranged-shown
           bidi-order-of-levels-in-terms-of-arranged-items
           min
           max)
  :use (:instance arranged-items-with-other-levels
                  (items (bidi-display-items l1 0))
                  (level (bidi-highest-level
                          (bidi-display-items (append l1 l2) 0)))
                  (lowest? (bidi-lowest-odd-level
                            (bidi-display-items (append l1 l2) 0)))))

(defruledl arranged-shown-of-second-part
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (equal (len c1) (len l1))
                (equal offset (len l1)))
           (equal (arranged-shown (bidi-display-items l2 offset)
                                  (append l1 l2)
                                  (append c1 c2))
                  (bidi-shown-chars-at (bidi-order-of-levels l2)
                                       (bidi-shown-chars c2 l2))))
  :enable (arranged-shown
           bidi-order-of-levels-in-terms-of-arranged-items
           min
           max)
  :use ((:instance bidi-display-items-in-terms-of-shift-items
                   (levels l2)
                   (offset (len l1)))
        (:instance arranged-items-with-other-levels
                   (items (bidi-display-items l2 0))
                   (level (bidi-highest-level
                           (bidi-display-items (append l1 l2) 0)))
                   (lowest? (bidi-lowest-odd-level
                             (bidi-display-items (append l1 l2) 0))))))

(defrulel bidi-shown-chars-at-of-nil
  (equal (bidi-shown-chars-at nil shown)
         nil)
  :enable bidi-shown-chars-at)

(defrulel bidi-move-marks-of-nil-and-nil
  (equal (bidi-move-marks nil nil ver)
         nil)
  :enable bidi-move-marks)

(defrulel bidi-shown-chars-of-append-when-not-consp
  (implies (not (consp cps2))
           (equal (bidi-shown-chars (append cps1 cps2) levels)
                  (bidi-shown-chars cps1 levels)))
  :induct (two-lists-induction cps1 levels)
  :enable (bidi-shown-chars append))

(defruledl nth-of-len-minus-1-in-terms-of-nat-list-last
  (implies (and (nat-listp l1)
                (consp l1))
           (equal (nth (+ -1 (len l1)) l1)
                  (nat-list-last l1)))
  :induct (len l1)
  :enable (nat-list-last nth len nat-listp nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-clean-cut-display
  :short "The two parts of a paragraph joined at a clean cut
          are each displayed as they would be with their own levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "The paragraph is given by the code points and the levels
     of its two parts (see @(tsee bidi-arrange-with-levels)),
     and the cut between the two parts is clean
     (see @(tsee bidi-clean-cut-p)).
     Then the characters of the paragraph in the order of display
     are those of the first part in the order of display,
     followed by those of the second part in the order of display:
     rules L2 and L3 [UAX #9] move no character across the cut,
     and they do in each part what they would do
     if the part were a paragraph with the same levels.")
   (xdoc::p
    "The theorem of @(see bidi-clean-cut-theorem)
     says that the characters stay on their side of the cut;
     this one also says in which order they are.
     For rule L2 it has this to see:
     in the paragraph, the rule reverses runs of characters
     from the highest level of the paragraph down to its lowest odd level,
     which may be more levels than a part has.
     Above the highest level of a part, there is no run in the part.
     Under its lowest odd level, the levels go two by two,
     an even level and then the odd level under it,
     which no character of the part has:
     the same runs are reversed for the two levels,
     and so they are back as they were."))

  (defrule bidi-arrange-with-levels-of-append-when-bidi-clean-cut-p
    (implies (and (nat-listp levels1)
                  (nat-listp levels2)
                  (equal (len cps1) (len levels1))
                  (equal (len cps2) (len levels2))
                  (bidi-clean-cut-p (len levels1)
                                    (append levels1 levels2)))
             (equal (bidi-arrange-with-levels (append cps1 cps2)
                                              (append levels1 levels2)
                                              ver)
                    (append (bidi-arrange-with-levels cps1 levels1 ver)
                            (bidi-arrange-with-levels cps2 levels2 ver))))
    :cases ((not (consp levels1))
            (not (consp levels2)))
    :enable (bidi-arrange-with-levels
             bidi-clean-cut-p
             bidi-move-marks-of-arranged-when-clean
             arranged-shown-of-first-part
             arranged-shown-of-second-part
             nth-of-len-minus-1-in-terms-of-nat-list-last
             nfix)
    :disable bidi-shown-chars-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-clean-cuts-p ((segments code-point-list-listp)
                           (start natp)
                           (levels nat-listp))
  :returns (yes/no booleanp)
  :short "Check if the cuts between the segments of a text are clean,
          given the levels of the characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is a list of segments that follow each other,
     and the second is the number of characters of the text
     before the first of them: 0 for all the segments of a text.
     The cut before each segment must be clean
     (see @(tsee bidi-clean-cut-p))."))
  (b* (((when (endp segments)) t)
       (start (lnfix start)))
    (and (bidi-clean-cut-p start levels)
         (bidi-clean-cuts-p (cdr segments)
                            (+ start (len (car segments)))
                            levels)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-clean-cuts-p
    :hints (("Goal"
             :induct (bidi-clean-cuts-p segments start levels)
             :expand ((bidi-clean-cuts-p segments start levels)
                      (bidi-clean-cuts-p (code-point-list-list-fix segments)
                                         start
                                         levels)
                      (bidi-clean-cuts-p segments (nfix start) levels)
                      (bidi-clean-cuts-p segments
                                         start
                                         (nat-list-fix levels)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-confined-p ((segments code-point-list-listp)
                         (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a text cut into segments is confined,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The text is the segments one after the other.
     It is taken as one paragraph from left to right
     and its characters get their levels;
     the text is confined if the cuts between the segments are all clean.
     Then every run of characters at levels above zero,
     which is what rule L2 reverses, lies inside one segment.
     See @(see bidi-confinement)."))
  (bidi-clean-cuts-p segments
                     0
                     (bidi-paragraph-all-levels
                      (code-points-to-bidi-chars (acl2::flatten segments)
                                                 ver)
                      0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(local
 (defun segments-induction (k segments start)
   (if (or (zp k)
           (atom segments))
       (list start)
     (segments-induction (- k 1)
                         (cdr segments)
                         (+ (nfix start) (len (car segments)))))))

(defrulel flatten-of-take-of-cons
  (implies (posp k)
           (equal (acl2::flatten (take k (cons segment segments)))
                  (append segment
                          (acl2::flatten (take (- k 1) segments)))))
  :enable (acl2::flatten take posp))

(defrulel bidi-clean-cut-p-when-at-the-end
  (implies (and (natp n)
                (<= (len levels) n))
           (bidi-clean-cut-p n levels))
  :enable (bidi-clean-cut-p natp nfix))

(defruledl bidi-clean-cut-p-when-bidi-clean-cuts-p
  (implies (and (bidi-clean-cuts-p segments start levels)
                (natp k)
                (< k (len segments)))
           (bidi-clean-cut-p (+ (nfix start)
                                (len (acl2::flatten (take k segments))))
                             levels))
  :induct (segments-induction k segments start)
  :enable (bidi-clean-cuts-p acl2::flatten take len natp nfix fix))

(defrulel len-of-flatten-of-take-upper-bound
  (implies (and (natp k)
                (<= k (len segments)))
           (<= (len (acl2::flatten (take k segments)))
               (len (acl2::flatten segments))))
  :rule-classes :linear
  :induct (take k segments)
  :enable (acl2::flatten take len nfix natp fix))

(defrulel bidi-clean-cut-p-of-len-of-flatten-of-take
  (implies (and (bidi-clean-cuts-p segments 0 levels)
                (equal (len levels) (len (acl2::flatten segments)))
                (natp k)
                (<= k (len segments)))
           (bidi-clean-cut-p (len (acl2::flatten (take k segments)))
                             levels))
  :cases ((< k (len segments)))
  :use (:instance bidi-clean-cut-p-when-bidi-clean-cuts-p (start 0)))

(defrulel take-of-len-of-flatten-of-take
  (implies (and (natp k)
                (<= k (len segments)))
           (equal (take (len (acl2::flatten (take k segments)))
                        (code-point-list-fix (acl2::flatten segments)))
                  (code-point-list-fix (acl2::flatten (take k segments)))))
  :induct (take k segments)
  :enable (acl2::flatten take len nfix natp fix))

(defrulel bidi-arrange-paragraph-when-not-consp
  (implies (not (consp cps))
           (equal (bidi-arrange-paragraph cps direction ver)
                  nil))
  :use len-of-bidi-arrange-paragraph
  :disable len-of-bidi-arrange-paragraph
  :enable len)

(defsection bidi-confined-theorem
  :short "A confined text is displayed segment by segment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The text is one paragraph from left to right, cut into segments,
     and it is confined (see @(tsee bidi-confined-p)).
     Then for every number @('k'),
     the characters of the paragraph in the order of display
     (see @(tsee bidi-arrange-paragraph)) begin with
     the characters of the first @('k') segments, in another order,
     as many as those segments have.
     With @('k') and @('k+1'), this says that the characters of a segment
     are displayed together,
     after those of the segments before it
     and before those of the segments after it:
     the display is the first segment in some order,
     then the second in some order, and so on.")
   (xdoc::p
    "The order inside a segment is the one that
     the Unicode Bidirectional Algorithm gives it in this text.
     It can differ from the order that the segment would have alone,
     because a bracket inside the segment
     can be paired with a bracket outside it.
     See @(see bidi-self-contained-segments)
     for conditions under which the two orders are the same.")
   (xdoc::p
    "The second theorem says that for a text
     with no paragraph separator before its last character,
     the characters of the text in the order of display
     (see @(tsee bidi-arrange)) are those of its one paragraph."))

  (defrule perm-of-take-of-bidi-arrange-paragraph-when-bidi-confined-p
    (implies (and (equal (paragraph-direction-kind direction)
                         :left-to-right)
                  (bidi-confined-p segments ver)
                  (natp k)
                  (<= k (len segments)))
             (acl2::perm
              (bidi-shown-char-list-code-points
               (take (len (acl2::flatten (take k segments)))
                     (bidi-arrange-paragraph (acl2::flatten segments)
                                             direction
                                             ver)))
              (code-point-list-fix (acl2::flatten (take k segments)))))
    :enable bidi-confined-p)

  (defrule bidi-arrange-when-one-paragraph
    (implies (equal (bidi-paragraph-length
                     (code-points-to-bidi-chars cps ver))
                    (len cps))
             (equal (bidi-arrange cps direction ver)
                    (bidi-arrange-paragraph cps direction ver)))
    :enable (bidi-arrange nfix)
    :expand ((bidi-arrange cps direction ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-guarded-segments
  :parents (bidi-confinement)
  :short "Conditions on the segments of a text,
          which can be checked without running the algorithm,
          under which the text is confined."
  :long
  (xdoc::topstring
   (xdoc::p
    "Whether a text is confined (see @(tsee bidi-confined-p))
     depends on the levels of its characters,
     which the Unicode Bidirectional Algorithm [UAX #9] computes.
     The conditions here look only at the bidirectional classes
     of the characters and at the paired brackets.
     They are for a text that is plain (see @(tsee bidi-plain-p)):
     it has no explicit directional formatting character,
     no character that rule X9 removes,
     and no paragraph separator.")
   (xdoc::p
    "Call a segment right-to-left if it has a character of class
     @('R') (@('Right_To_Left')), @('AL') (@('Arabic_Letter'))
     or @('AN') (@('Arabic_Number')).
     The conditions are, for every right-to-left segment:")
   (xdoc::ol
    (xdoc::li
     "After the segment, the first character of class
      @('L') (@('Left_To_Right')), @('R'), @('AL'),
      @('EN') (@('European_Number')) or @('AN'), if there is one,
      is of class @('L').
      So the text returns to left-to-right
      before any other letter or number
      (see @(tsee bidi-turns-left-to-right-p)).")
    (xdoc::li
     "The character right after the segment, if there is one,
      is neither of class @('ET') (@('European_Terminator')),
      which rule W5 joins to a number before it,
      nor of class @('NSM') (@('Nonspacing_Mark')),
      which rule W1 joins to the character before it
      (see @(tsee bidi-attaches-p)).")
    (xdoc::li
     "No bracket pair of the text [UAX #9, BD16]
      has its opening bracket inside the segment
      and its closing bracket after the segment
      (see @(tsee bidi-bracket-pairs-closed-p))."))
   (xdoc::p
    "The predicate is @(tsee bidi-guarded-segments-p).
     A plain text whose segments satisfy it is confined:
     that is the theorem of the book @('bidi-guarded-theorem')
     (see @(see bidi-guarded-segments-theorem)).
     Each condition is needed:
     the file @('tests/bidi-confinement.lisp') has, for each of them,
     a text that fails only that condition and is not confined.
     The same file checks the theorem by running the algorithm
     on every text of one to four characters over sixteen characters,
     with every way of cutting the text:
     one character for each of the twelve classes
     that a plain text can have, and two kinds of paired brackets.")
   (xdoc::p
    "The conditions do not make each segment be displayed
     as it would be alone.
     Two more conditions on the bracket pairs of the text do:
     see @(see bidi-self-contained-segments)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;

(define bidi-plain-code-point-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is neither a paragraph separator,
          nor an explicit directional formatting character,
          nor a character that rule X9 removes,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if its bidirectional class
     is one of the twelve other than the following eleven
     [UAX #9, Table 4]:
     @('B') (@('Paragraph_Separator')),
     @('BN') (@('Boundary_Neutral')),
     and the nine classes of the explicit formatting characters,
     @('LRE'), @('RLE'), @('LRO'), @('RLO'), @('PDF'),
     @('LRI'), @('RLI'), @('FSI') and @('PDI')."))
  (b* ((class (code-point-bidi-class cp ver)))
    (not (or (equal (bidi-class-kind class) :paragraph-separator)
             (bidi-class-removed-p class)
             (bidi-class-isolate-formatting-p class))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-plain-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that a list of code points is plain,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-plain-code-point-p).
     A plain text is one paragraph,
     and the rules for explicit levels [UAX #9, rules X1 to X8]
     leave all its characters at the paragraph embedding level."))
  (bidi-plain-code-point-p x ver)
  ///
  (fty::deffixequiv bidi-plain-p
    :args ((x code-point-listp) (ver versionp))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-turns-left-to-right-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check that the first letter or number of a list of code points,
          if there is one, is a left-to-right letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A letter or number is here a code point of bidirectional class
     @('L'), @('R'), @('AL'), @('EN') or @('AN');
     a left-to-right letter is one of class @('L')."))
  (b* (((when (endp cps)) t)
       (cp (code-point-fix (car cps)))
       (kind (bidi-class-kind (code-point-bidi-class cp ver)))
       ((when (equal kind :left-to-right)) t)
       ((when (or (equal kind :right-to-left)
                  (equal kind :arabic-letter)
                  (equal kind :european-number)
                  (equal kind :arabic-number)))
        nil))
    (bidi-turns-left-to-right-p (cdr cps) ver))
  :hooks nil

  ///

  (fty::deffixequiv bidi-turns-left-to-right-p
    :hints (("Goal"
             :induct (bidi-turns-left-to-right-p cps ver)
             :expand ((bidi-turns-left-to-right-p cps ver)
                      (bidi-turns-left-to-right-p (code-point-list-fix cps)
                                                  ver)
                      (bidi-turns-left-to-right-p cps
                                                  (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-attaches-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the first code point of a list
          is of a class that can join it to the text before it,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classes are @('ET') and @('NSM'):
     a European terminator next to a European number
     becomes a part of the number [UAX #9, rule W5],
     and a nonspacing mark takes the class
     of the character before it [UAX #9, rule W1]."))
  (b* (((when (endp cps)) nil)
       (class (code-point-bidi-class (car cps) ver)))
    (or (equal (bidi-class-kind class) :european-terminator)
        (equal (bidi-class-kind class) :nonspacing-mark)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-bracket-pairs-closed-p ((pairs bracket-pair-listp)
                                     (start natp)
                                     (end natp))
  :returns (yes/no booleanp)
  :short "Check that every bracket pair of a list
          that opens in a part of a text closes in that part."
  :long
  (xdoc::topstring
   (xdoc::p
    "The part goes from the position @('start'), included,
     to the position @('end'), excluded.
     A bracket pair is the position of an opening bracket
     and the position of the closing bracket that goes with it
     [UAX #9, BD16]; see @(tsee bidi-bracket-pairs)."))
  (b* (((when (endp pairs)) t)
       ((bracket-pair pair) (car pairs)))
    (and (or (< pair.open (lnfix start))
             (<= (lnfix end) pair.open)
             (< pair.close (lnfix end)))
         (bidi-bracket-pairs-closed-p (cdr pairs) start end)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-bracket-pairs-closed-p
    :hints (("Goal"
             :induct (bidi-bracket-pairs-closed-p pairs start end)
             :expand ((bidi-bracket-pairs-closed-p pairs start end)
                      (bidi-bracket-pairs-closed-p
                       (bracket-pair-list-fix pairs)
                       start
                       end)
                      (bidi-bracket-pairs-closed-p pairs (nfix start) end)
                      (bidi-bracket-pairs-closed-p pairs
                                                   start
                                                   (nfix end)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-guarded-segments-from-p ((segments code-point-list-listp)
                                      (start natp)
                                      (pairs bracket-pair-listp)
                                      (ver versionp))
  :returns (yes/no booleanp)
  :short "Check the conditions on some of the segments of a text,
          given the bracket pairs of the text,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is a list of segments that follow each other
     to the end of the text,
     and the second is the number of characters of the text
     before the first of them.
     See @(see bidi-guarded-segments) for the conditions.
     In a plain text, a segment is right-to-left
     exactly when it does not satisfy @(tsee right-to-left-free-p)."))
  (b* (((when (endp segments)) t)
       (segment (code-point-list-fix (car segments)))
       (start (lnfix start))
       (end (+ start (len segment)))
       (rest (acl2::flatten (code-point-list-list-fix (cdr segments)))))
    (and (or (right-to-left-free-p segment ver)
             (and (bidi-turns-left-to-right-p rest ver)
                  (not (bidi-attaches-p rest ver))
                  (bidi-bracket-pairs-closed-p pairs start end)))
         (bidi-guarded-segments-from-p (cdr segments) end pairs ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-guarded-segments-from-p
    :hints (("Goal"
             :induct (bidi-guarded-segments-from-p segments start pairs ver)
             :expand ((bidi-guarded-segments-from-p segments start pairs ver)
                      (bidi-guarded-segments-from-p
                       (code-point-list-list-fix segments)
                       start
                       pairs
                       ver)
                      (bidi-guarded-segments-from-p segments
                                                    (nfix start)
                                                    pairs
                                                    ver)
                      (bidi-guarded-segments-from-p
                       segments
                       start
                       (bracket-pair-list-fix pairs)
                       ver)
                      (bidi-guarded-segments-from-p segments
                                                    start
                                                    pairs
                                                    (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-guarded-segments-p ((segments code-point-list-listp)
                                 (ver versionp))
  :returns (yes/no booleanp)
  :short "Check the conditions on the segments of a text
          under which a plain text is confined,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see bidi-guarded-segments).
     The text is the segments one after the other,
     and the bracket pairs are those of the whole text."))
  (b* ((chars (code-points-to-bidi-chars (acl2::flatten segments) ver)))
    (bidi-guarded-segments-from-p
     segments
     0
     (bidi-bracket-pairs (bidi-char-list-classes chars)
                         (bidi-char-list-brackets chars))
     ver))
  :hooks (:fix))
