; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rule-display")
(include-book "bidi-display")
(include-book "bidi-confinement")
(include-book "bidi-mark-class")

(local (include-book "bidi-left-to-right"))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable fix nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L2 on levels that are all 1 or 2.

(local
 (define one-or-two-p (x)
   :returns (yes/no booleanp)
   (or (equal x 1)
       (equal x 2))
   :hooks nil))

(local
 (std::deflist one-or-two-listp (x)
   :guard t
   (one-or-two-p x)))

(defrulel nat-listp-when-one-or-two-listp
  (implies (and (one-or-two-listp x)
                (true-listp x))
           (nat-listp x))
  :induct (len x)
  :enable (len one-or-two-p))

; The items of a list of such levels.

(local
 (define items-ok ((items bidi-display-item-listp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (one-or-two-p (bidi-display-item->level (car items)))
            (items-ok (cdr items))))
   :hooks nil))

(local
 (define items-all ((items bidi-display-item-listp) (level natp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (equal (bidi-display-item->level (car items)) level)
            (items-all (cdr items) level)))
   :hooks nil))

(local
 (define items-have ((items bidi-display-item-listp) (level natp))
   :returns (yes/no booleanp)
   (and (consp items)
        (or (equal (bidi-display-item->level (car items)) level)
            (items-have (cdr items) level)))
   :hooks nil))

(defrulel items-ok-of-bidi-display-items
  (implies (one-or-two-listp levels)
           (items-ok (bidi-display-items levels position)))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items items-ok one-or-two-p))

(defrulel items-ok-of-append
  (equal (items-ok (append x y))
         (and (items-ok x)
              (items-ok y)))
  :induct (len x)
  :enable (len items-ok append))

(defrulel items-ok-of-bidi-display-item-list-fix
  (equal (items-ok (bidi-display-item-list-fix items))
         (items-ok items))
  :induct (len items)
  :enable (len items-ok bidi-display-item-list-fix))

(defrulel items-ok-of-bidi-reverse-runs
  (implies (and (items-ok items)
                (items-ok run))
           (items-ok (bidi-reverse-runs items level run)))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs items-ok))

; Reversing the runs at level 1 or more reverses the list.

(defrulel bidi-reverse-runs-of-1-when-items-ok
  (implies (items-ok items)
           (equal (bidi-reverse-runs items 1 run)
                  (append (rev (bidi-display-item-list-fix items))
                          (bidi-display-item-list-fix run))))
  :induct (bidi-reverse-runs items 1 run)
  :enable (bidi-reverse-runs
           items-ok
           one-or-two-p
           rev
           bidi-display-item-list-fix))

; Reversing the runs at level 2 or more:
; nothing changes if every level is 1,
; and the list is reversed if every level is 2.

(defrulel bidi-reverse-runs-of-2-when-items-all-1
  (implies (items-all items 1)
           (equal (bidi-reverse-runs items 2 nil)
                  (bidi-display-item-list-fix items)))
  :induct (len items)
  :enable (len
           bidi-reverse-runs
           items-all
           bidi-display-item-list-fix))

(defrulel bidi-reverse-runs-of-2-when-items-all-2
  (implies (items-all items 2)
           (equal (bidi-reverse-runs items 2 run)
                  (append (rev (bidi-display-item-list-fix items))
                          (bidi-display-item-list-fix run))))
  :induct (bidi-reverse-runs items 2 run)
  :enable (bidi-reverse-runs
           items-all
           rev
           bidi-display-item-list-fix))

; The highest level and the lowest odd level.

(defrulel items-all-2-when-not-items-have-1
  (implies (and (items-ok items)
                (not (items-have items 1)))
           (items-all items 2))
  :induct (len items)
  :enable (len items-ok items-all items-have one-or-two-p))

(defrulel items-all-1-when-not-items-have-2
  (implies (and (items-ok items)
                (not (items-have items 2)))
           (items-all items 1))
  :induct (len items)
  :enable (len items-ok items-all items-have one-or-two-p))

(defrulel bidi-lowest-odd-level-when-items-ok
  (implies (items-ok items)
           (equal (bidi-lowest-odd-level items)
                  (if (items-have items 1)
                      1
                    nil)))
  :induct (len items)
  :enable (len
           bidi-lowest-odd-level
           items-ok
           items-have
           one-or-two-p
           min))

(defrulel bidi-highest-level-when-items-ok
  (implies (and (items-ok items)
                (consp items))
           (equal (bidi-highest-level items)
                  (if (items-have items 2)
                      2
                    1)))
  :induct (len items)
  :enable (len
           bidi-highest-level
           items-ok
           items-have
           one-or-two-p
           max))

(defrulel consp-when-items-have
  (implies (items-have items level)
           (consp items))
  :rule-classes :forward-chaining
  :enable items-have)

; So rule L2 reverses the runs at level 2 and then the whole list.

(defrulel bidi-reorder-items-from-2-when-items-ok
  (implies (items-ok items)
           (equal (bidi-reorder-items items 2 1)
                  (rev (bidi-reverse-runs items 2 nil))))
  :expand ((bidi-reorder-items items 2 1)
           (:free (items) (bidi-reorder-items items 1 1))
           (:free (items) (bidi-reorder-items items 0 1))))

(defrulel bidi-reorder-items-from-1-when-items-ok
  (implies (and (items-ok items)
                (not (items-have items 2)))
           (equal (bidi-reorder-items items 1 1)
                  (rev (bidi-reverse-runs items 2 nil))))
  :expand ((bidi-reorder-items items 1 1)
           (:free (items) (bidi-reorder-items items 0 1))))

(defrulel bidi-order-of-levels-when-one-or-two-listp
  (implies (one-or-two-listp levels)
           (equal (bidi-order-of-levels levels)
                  (bidi-display-item-list-positions
                   (rev (bidi-reverse-runs (bidi-display-items levels 0)
                                           2
                                           nil)))))
  :cases ((items-have (bidi-display-items levels 0) 1))
  :enable bidi-order-of-levels)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The same reversal on the characters.
; The function SRR is BIDI-REVERSE-RUNS on characters with their levels,
; instead of positions with the levels.

(local
 (define srr ((shown bidi-shown-char-listp)
              (level natp)
              (run bidi-shown-char-listp))
   :returns (new-shown bidi-shown-char-listp)
   (b* (((when (endp shown)) (bidi-shown-char-list-fix run))
        (char (bidi-shown-char-fix (car shown)))
        ((when (>= (bidi-shown-char->level char) (lnfix level)))
         (srr (cdr shown) level (cons char run))))
     (append (bidi-shown-char-list-fix run)
             (cons char
                   (srr (cdr shown) level nil))))
   :hooks (:fix)))

; Each item has the level of the character at its position.

(local
 (define items-consistent ((items bidi-display-item-listp)
                           (shown bidi-shown-char-listp))
   :returns (yes/no booleanp)
   (or (endp items)
       (and (equal (bidi-shown-char->level
                    (bidi-shown-char-at
                     (bidi-display-item->position (car items))
                     shown))
                   (bidi-display-item->level (car items)))
            (items-consistent (cdr items) shown)))
   :hooks nil))

(defrulel items-consistent-of-nil
  (items-consistent nil shown)
  :enable items-consistent)

(defrulel bidi-shown-chars-at-of-nil
  (equal (bidi-shown-chars-at nil shown)
         nil)
  :enable bidi-shown-chars-at)

(defrulel bidi-shown-chars-at-of-append
  (equal (bidi-shown-chars-at (append positions1 positions2) shown)
         (append (bidi-shown-chars-at positions1 shown)
                 (bidi-shown-chars-at positions2 shown)))
  :induct (len positions1)
  :enable (len bidi-shown-chars-at append))

(defrulel bidi-display-item-list-positions-of-append
  (equal (bidi-display-item-list-positions (append items1 items2))
         (append (bidi-display-item-list-positions items1)
                 (bidi-display-item-list-positions items2)))
  :induct (len items1)
  :enable (len bidi-display-item-list-positions append))

(defrulel bidi-display-item-list-positions-of-rev
  (equal (bidi-display-item-list-positions (rev items))
         (rev (bidi-display-item-list-positions items)))
  :induct (len items)
  :enable (len bidi-display-item-list-positions rev))

(defrulel bidi-shown-chars-at-of-rev
  (equal (bidi-shown-chars-at (rev positions) shown)
         (rev (bidi-shown-chars-at positions shown)))
  :induct (len positions)
  :enable (len bidi-shown-chars-at rev))

(defrulel bidi-display-item-list-positions-of-bidi-display-item-list-fix
  (equal (bidi-display-item-list-positions
          (bidi-display-item-list-fix items))
         (bidi-display-item-list-positions items))
  :induct (len items)
  :enable (len bidi-display-item-list-positions bidi-display-item-list-fix))

(defrulel characters-of-bidi-reverse-runs
  (implies (and (items-consistent items shown)
                (items-consistent run shown))
           (equal (bidi-shown-chars-at
                   (bidi-display-item-list-positions
                    (bidi-reverse-runs items level run))
                   shown)
                  (srr (bidi-shown-chars-at
                        (bidi-display-item-list-positions items)
                        shown)
                       level
                       (bidi-shown-chars-at
                        (bidi-display-item-list-positions run)
                        shown))))
  :induct (bidi-reverse-runs items level run)
  :enable (bidi-reverse-runs
           srr
           items-consistent
           bidi-shown-chars-at
           bidi-display-item-list-positions))

(defrulel items-consistent-of-bidi-display-items-when-posp
  (implies (and (posp position)
                (consp shown))
           (equal (items-consistent (bidi-display-items levels position)
                                    shown)
                  (items-consistent (bidi-display-items levels
                                                        (- position 1))
                                    (cdr shown))))
  :induct (bidi-display-items levels position)
  :enable (bidi-display-items
           items-consistent
           bidi-shown-char-at
           nfix
           posp))

(defrulel items-consistent-of-bidi-display-items
  (implies (and (nat-listp levels)
                (equal (len levels) (len cps)))
           (items-consistent (bidi-display-items levels 0)
                             (bidi-shown-chars cps levels)))
  :induct (bidi-shown-chars cps levels)
  :enable (bidi-shown-chars
           items-consistent
           bidi-shown-char-at
           len)
  :expand (bidi-display-items levels 0))

; The characters in the order of display, for levels that are all 1 or 2.

(defruledl bidi-arrange-with-levels-when-one-or-two-listp
  (implies (and (one-or-two-listp levels)
                (true-listp levels)
                (equal (len levels) (len cps)))
           (equal (bidi-arrange-with-levels cps levels ver)
                  (bidi-move-marks
                   (rev (srr (bidi-shown-chars cps levels) 2 nil))
                   nil
                   ver)))
  :enable (bidi-arrange-with-levels
           bidi-display-item-list-positions-of-bidi-display-items
           bidi-shown-chars-at-of-bidi-positions-with-level))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Characters that all have one level.

(local
 (define shown-all ((shown bidi-shown-char-listp) (level natp))
   :returns (yes/no booleanp)
   (or (endp shown)
       (and (equal (bidi-shown-char->level (car shown)) level)
            (shown-all (cdr shown) level)))
   :hooks nil))

(local
 (define list-and-count-induction (x n)
   (if (or (zp n)
           (atom x))
       nil
     (list-and-count-induction (cdr x) (- n 1)))
   :verify-guards nil
   :hooks nil))

(defrulel shown-all-of-bidi-shown-chars-of-repeat
  (implies (natp level)
           (shown-all (bidi-shown-chars cps (acl2::repeat n level)) level))
  :induct (list-and-count-induction cps n)
  :enable (list-and-count-induction
           bidi-shown-chars
           shown-all
           acl2::repeat))

(defrulel srr-of-append-when-shown-all-2
  (implies (shown-all x 2)
           (equal (srr (append x y) 2 run)
                  (srr y
                       2
                       (append (rev (bidi-shown-char-list-fix x))
                               (bidi-shown-char-list-fix run)))))
  :induct (srr x 2 run)
  :enable (srr shown-all rev bidi-shown-char-list-fix))

(defrulel srr-when-shown-all-2
  (implies (shown-all x 2)
           (equal (srr x 2 run)
                  (append (rev (bidi-shown-char-list-fix x))
                          (bidi-shown-char-list-fix run))))
  :induct (srr x 2 run)
  :enable (srr shown-all rev bidi-shown-char-list-fix))

(defrulel srr-of-append-when-shown-all-1
  (implies (shown-all x 1)
           (equal (srr (append x y) 2 nil)
                  (append (bidi-shown-char-list-fix x)
                          (srr y 2 nil))))
  :induct (len x)
  :enable (len srr shown-all bidi-shown-char-list-fix))

(defrulel srr-of-append-when-shown-all-1-and-consp
  (implies (and (shown-all x 1)
                (consp x))
           (equal (srr (append x y) 2 run)
                  (append (bidi-shown-char-list-fix run)
                          (bidi-shown-char-list-fix x)
                          (srr y 2 nil))))
  :expand ((srr (append x y) 2 run)
           (shown-all x 1)
           (bidi-shown-char-list-fix x)))

(defrulel srr-of-nil
  (equal (srr nil level run)
         (bidi-shown-char-list-fix run))
  :enable srr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L3.

(defrulel bidi-move-marks-of-nil
  (equal (bidi-move-marks nil pending ver)
         (bidi-shown-char-list-fix pending))
  :enable bidi-move-marks)

; A character at an even level is not moved.

(defrulel bidi-move-marks-of-append-when-shown-all-2
  (implies (shown-all x 2)
           (equal (bidi-move-marks (append x y) nil ver)
                  (append (bidi-shown-char-list-fix x)
                          (bidi-move-marks y nil ver))))
  :induct (len x)
  :enable (len shown-all bidi-shown-char-list-fix)
  :expand (:free (a b) (bidi-move-marks (cons a b) nil ver)))

; Combining marks at level 1, and a character at level 1 that is not one.

(local
 (define shown-mark-p ((char bidi-shown-char-p) (ver versionp))
   :returns (yes/no booleanp)
   (and (equal (bidi-shown-char->level char) 1)
        (bidi-combining-mark-p (bidi-shown-char->code-point char) ver))
   :hooks nil))

(local
 (std::deflist shown-marks-p (x ver)
   :guard (and (bidi-shown-char-listp x)
               (versionp ver))
   (shown-mark-p x ver)))

(local
 (define shown-base-p ((char bidi-shown-char-p) (ver versionp))
   :returns (yes/no booleanp)
   (and (equal (bidi-shown-char->level char) 1)
        (not (bidi-combining-mark-p (bidi-shown-char->code-point char) ver)))
   :hooks nil))

; The marks that come before their base character in the reversed order
; are put after it.

(defrulel bidi-move-marks-of-marks-and-base
  (implies (and (shown-marks-p marks ver)
                (shown-marks-p pending ver)
                (bidi-shown-char-listp marks)
                (bidi-shown-char-listp pending)
                (bidi-shown-char-p base)
                (shown-base-p base ver))
           (equal (bidi-move-marks (append marks (cons base rest)) pending ver)
                  (cons base
                        (append (rev marks)
                                pending
                                (bidi-move-marks rest nil ver)))))
  :induct (bidi-move-marks marks pending ver)
  :enable (bidi-move-marks
           shown-mark-p
           shown-base-p
           rev)
  :expand (:free (a b) (bidi-move-marks (cons a b) pending ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists.

(defrulel take-of-len-plus-of-append
  (implies (natp n)
           (and (equal (take (+ (len x) n) (append x y))
                       (append x (take n y)))
                (equal (take (+ n (len x)) (append x y))
                       (append x (take n y)))))
  :induct (len x)
  :enable (len take append))

(defrulel take-of-len-of-append
  (equal (take (len x) (append x y))
         (acl2::list-fix x))
  :induct (len x)
  :enable (len take append acl2::list-fix))

(defrulel nthcdr-of-len-plus-of-append
  (implies (natp n)
           (and (equal (nthcdr (+ (len x) n) (append x y))
                       (nthcdr n y))
                (equal (nthcdr (+ n (len x)) (append x y))
                       (nthcdr n y))))
  :induct (len x)
  :enable (len nthcdr append))

(defrulel nthcdr-of-len-of-append
  (equal (nthcdr (len x) (append x y))
         y)
  :induct (len x)
  :enable (len nthcdr append))

; Characters with their levels.

(defrulel bidi-shown-chars-when-not-consp
  (implies (or (not (consp cps))
               (not (consp levels)))
           (equal (bidi-shown-chars cps levels)
                  nil))
  :expand (bidi-shown-chars cps levels))

(defrulel bidi-shown-chars-of-append-of-levels
  (implies (<= (len levels1) (len cps))
           (equal (bidi-shown-chars cps (append levels1 levels2))
                  (append (bidi-shown-chars (take (len levels1) cps) levels1)
                          (bidi-shown-chars (nthcdr (len levels1) cps)
                                            levels2))))
  :induct (bidi-shown-chars cps levels1)
  :enable (bidi-shown-chars len take nthcdr append))

; Rule L4.

(defrulel bidi-mirror-chars-of-nil
  (equal (bidi-mirror-chars nil ver)
         nil)
  :enable bidi-mirror-chars)

(defrulel bidi-mirror-chars-of-append
  (equal (bidi-mirror-chars (append x y) ver)
         (append (bidi-mirror-chars x ver)
                 (bidi-mirror-chars y ver)))
  :induct (len x)
  :enable (len bidi-mirror-chars append))

(defrulel bidi-mirror-chars-of-bidi-shown-chars-of-repeat-of-2
  (implies (<= (len cps) (nfix n))
           (equal (bidi-mirror-chars (bidi-shown-chars cps (acl2::repeat n 2))
                                     ver)
                  (code-point-list-fix cps)))
  :induct (list-and-count-induction cps n)
  :enable (list-and-count-induction
           bidi-shown-chars
           bidi-mirror-chars
           bidi-mirror-char
           acl2::repeat
           code-point-list-fix
           len))

(defrulel bidi-mirror-chars-of-bidi-shown-chars-of-repeat-of-1
  (implies (<= (len cps) (nfix n))
           (equal (bidi-mirror-chars (bidi-shown-chars cps (acl2::repeat n 1))
                                     ver)
                  (bidi-mirror-code-points cps ver)))
  :induct (list-and-count-induction cps n)
  :enable (list-and-count-induction
           bidi-shown-chars
           bidi-mirror-chars
           bidi-mirror-char
           bidi-mirror-code-points
           bidi-mirror-code-point
           acl2::repeat
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A cluster for rule L3: a code point that is not a combining mark,
; and then combining marks.

(local
 (std::deflist combining-marks-p (x ver)
   :guard (and (code-point-listp x)
               (versionp ver))
   (bidi-combining-mark-p x ver)))

(local
 (define mark-cluster-p ((cluster code-point-listp) (ver versionp))
   :returns (yes/no booleanp)
   (and (consp cluster)
        (not (bidi-combining-mark-p (car cluster) ver))
        (combining-marks-p (cdr cluster) ver))
   :hooks nil))

(local
 (std::deflist mark-clusters-p (x ver)
   :guard (and (code-point-list-listp x)
               (versionp ver))
   (mark-cluster-p x ver)))

(defrulel shown-marks-p-of-bidi-shown-chars-of-repeat-of-1
  (implies (combining-marks-p cps ver)
           (shown-marks-p (bidi-shown-chars cps (acl2::repeat n 1)) ver))
  :induct (list-and-count-induction cps n)
  :enable (list-and-count-induction
           bidi-shown-chars
           shown-mark-p
           acl2::repeat))

; The characters of such a cluster at level 1, in the reversed order,
; are put back in their order.

(defrulel bidi-move-marks-of-reversed-cluster
  (implies (mark-cluster-p cluster ver)
           (equal (bidi-move-marks
                   (append (rev (bidi-shown-chars
                                 cluster
                                 (acl2::repeat (len cluster) 1)))
                           rest)
                   nil
                   ver)
                  (append (bidi-shown-chars cluster
                                            (acl2::repeat (len cluster) 1))
                          (bidi-move-marks rest nil ver))))
  :enable (mark-cluster-p
           shown-base-p
           len
           acl2::repeat)
  :expand (:free (levels) (bidi-shown-chars cluster levels)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The number at the start of a list of clusters, and the rest.

(defrulel append-of-bidi-leading-number-and-bidi-after-leading-number
  (equal (append (bidi-leading-number clusters arabic ver)
                 (bidi-after-leading-number clusters arabic ver))
         (code-point-list-list-fix clusters))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number bidi-after-leading-number))

(defrulel take-of-len-of-flatten-of-bidi-leading-number
  (implies (code-point-list-listp clusters)
           (equal (take (len (acl2::flatten
                              (bidi-leading-number clusters arabic ver)))
                        (acl2::flatten clusters))
                  (acl2::flatten (bidi-leading-number clusters arabic ver))))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number acl2::flatten))

(defrulel nthcdr-of-len-of-flatten-of-bidi-leading-number
  (implies (code-point-list-listp clusters)
           (equal (nthcdr (len (acl2::flatten
                                (bidi-leading-number clusters arabic ver)))
                          (acl2::flatten clusters))
                  (acl2::flatten
                   (bidi-after-leading-number clusters arabic ver))))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number
           bidi-after-leading-number
           acl2::flatten))

(defrulel flatten-of-bidi-leading-number-when-all
  (implies (and (code-point-list-listp clusters)
                (not (consp (bidi-after-leading-number clusters arabic ver))))
           (equal (acl2::flatten (bidi-leading-number clusters arabic ver))
                  (acl2::flatten clusters)))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number
           bidi-after-leading-number
           acl2::flatten))

(defrulel len-of-flatten-of-bidi-leading-number
  (implies (code-point-list-listp clusters)
           (<= (len (acl2::flatten
                     (bidi-leading-number clusters arabic ver)))
               (len (acl2::flatten clusters))))
  :rule-classes :linear
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number acl2::flatten))

(defrulel flatten-of-bidi-after-leading-number-when-consp
  (implies (consp (bidi-after-leading-number clusters arabic ver))
           (equal (acl2::flatten
                   (bidi-after-leading-number clusters arabic ver))
                  (append (car (bidi-after-leading-number clusters
                                                          arabic
                                                          ver))
                          (acl2::flatten
                           (cdr (bidi-after-leading-number clusters
                                                           arabic
                                                           ver))))))
  :expand (acl2::flatten (bidi-after-leading-number clusters arabic ver)))

(defrulel mark-clusters-p-of-bidi-after-leading-number
  (implies (and (code-point-list-listp clusters)
                (mark-clusters-p clusters ver))
           (mark-clusters-p (bidi-after-leading-number clusters arabic ver)
                            ver))
  :induct (bidi-after-leading-number clusters arabic ver)
  :enable (bidi-after-leading-number mark-cluster-p))

(defrulel consp-of-car-of-bidi-after-leading-number-when-mark-clusters-p
  (implies (and (code-point-list-listp clusters)
                (mark-clusters-p clusters ver)
                (consp (bidi-after-leading-number clusters arabic ver)))
           (consp (car (bidi-after-leading-number clusters arabic ver))))
  :use mark-clusters-p-of-bidi-after-leading-number
  :disable mark-clusters-p-of-bidi-after-leading-number
  :expand (mark-clusters-p (bidi-after-leading-number clusters arabic ver)
                           ver)
  :enable mark-cluster-p)

(defrulel posp-of-len-when-consp
  (implies (consp x)
           (posp (len x)))
  :rule-classes :type-prescription
  :enable len)

(defrulel consp-of-bidi-shown-chars-of-repeat
  (implies (and (consp cps)
                (posp n))
           (consp (bidi-shown-chars cps (acl2::repeat n level))))
  :expand ((:free (levels) (bidi-shown-chars cps levels))
           (acl2::repeat n level)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The middle part: from its levels, rules L2, L3 and L4 give its display.
; The induction goes along BIDI-SHOW-CLUSTERS,
; with the characters that are displayed after those of the list.

(local
 (define order-induction (clusters arabic tail ver)
   (b* ((number (bidi-leading-number clusters arabic ver))
        (rest (bidi-after-leading-number clusters arabic ver))
        ((when (endp rest)) (list tail))
        (cluster (code-point-list-fix (car rest))))
     (order-induction
      (cdr rest)
      (bidi-arabic-after-cluster-p cluster arabic ver)
      (append (rev (bidi-shown-chars cluster
                                     (acl2::repeat (len cluster) 1)))
              (append (bidi-shown-chars
                       (acl2::flatten number)
                       (acl2::repeat (len (acl2::flatten number)) 2))
                      tail))
      ver))
   :measure (len clusters)
   :hints (("Goal" :in-theory (enable o-p o-finp o<)))
   :verify-guards nil
   :hooks nil))

(defrulel display-of-middle-with-tail
  (implies (and (code-point-list-listp clusters)
                (mark-clusters-p clusters ver))
           (equal (bidi-mirror-chars
                   (bidi-move-marks
                    (append (rev (srr (bidi-shown-chars
                                       (acl2::flatten clusters)
                                       (bidi-middle-levels clusters
                                                           arabic
                                                           ver))
                                      2
                                      nil))
                            tail)
                    nil
                    ver)
                   ver)
                  (append (acl2::flatten
                           (bidi-show-clusters clusters arabic ver))
                          (bidi-mirror-chars
                           (bidi-move-marks tail nil ver)
                           ver))))
  :induct (order-induction clusters arabic tail ver)
  :enable (order-induction
           bidi-middle-levels
           bidi-show-clusters))

; The same without the tail.

(defruledl len-of-flatten-in-terms-of-bidi-leading-number
  (implies (and (syntaxp (acl2::variablep clusters))
                (bind-free '((arabic . arabic) (ver . ver)) (arabic ver))
                (code-point-list-listp clusters))
           (equal (len (acl2::flatten clusters))
                  (+ (len (acl2::flatten
                           (bidi-leading-number clusters arabic ver)))
                     (len (acl2::flatten
                           (bidi-after-leading-number clusters
                                                      arabic
                                                      ver))))))
  :induct (bidi-leading-number clusters arabic ver)
  :enable (bidi-leading-number
           bidi-after-leading-number
           acl2::flatten))

(defrulel len-of-bidi-middle-levels
  (implies (code-point-list-listp clusters)
           (equal (len (bidi-middle-levels clusters arabic ver))
                  (len (acl2::flatten clusters))))
  :induct (bidi-middle-levels clusters arabic ver)
  :enable (bidi-middle-levels
           len-of-flatten-in-terms-of-bidi-leading-number)
  :disable flatten-of-bidi-leading-number-when-all)

(defrulel one-or-two-listp-of-bidi-middle-levels
  (one-or-two-listp (bidi-middle-levels clusters arabic ver))
  :induct (bidi-middle-levels clusters arabic ver)
  :enable (bidi-middle-levels one-or-two-p))

(defrulel display-of-middle
  (implies (and (code-point-list-listp clusters)
                (mark-clusters-p clusters ver))
           (equal (bidi-mirror-chars
                   (bidi-arrange-with-levels
                    (acl2::flatten clusters)
                    (bidi-middle-levels clusters arabic ver)
                    ver)
                   ver)
                  (acl2::flatten (bidi-show-clusters clusters arabic ver))))
  :enable bidi-arrange-with-levels-when-one-or-two-listp
  :use (:instance display-of-middle-with-tail (tail nil))
  :disable display-of-middle-with-tail)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The clusters of a list of code points that has no code point of class L
; and does not start with a mark are clusters for rule L3.

(defrulel consp-of-bidi-clusters
  (equal (consp (bidi-clusters cps ver))
         (consp cps))
  :expand (bidi-clusters cps ver))

(defrulel bidi-clusters-when-not-consp
  (implies (not (consp cps))
           (equal (bidi-clusters cps ver)
                  nil))
  :expand (bidi-clusters cps ver))

(defrulel flatten-of-bidi-clusters
  (equal (acl2::flatten (bidi-clusters cps ver))
         (code-point-list-fix cps))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           acl2::flatten
           code-point-list-fix)
  :expand (acl2::flatten (bidi-clusters (cdr cps) ver)))

(defrulel bidi-clusters-shape-for-marks
  (implies (not (bidi-class-kind-present-p :left-to-right cps ver))
           (and (mark-clusters-p (cdr (bidi-clusters cps ver)) ver)
                (implies (consp cps)
                         (and (consp (car (bidi-clusters cps ver)))
                              (equal (car (car (bidi-clusters cps ver)))
                                     (code-point-fix (car cps)))
                              (combining-marks-p
                               (cdr (car (bidi-clusters cps ver)))
                               ver)))))
  :induct (bidi-clusters cps ver)
  :enable (bidi-clusters
           bidi-class-kind-present-p
           mark-cluster-p
           bidi-combining-mark-p-when-not-left-to-right))

(defrulel mark-clusters-p-of-bidi-clusters
  (implies (and (not (bidi-class-kind-present-p :left-to-right cps ver))
                (not (and (consp cps)
                          (bidi-mark-code-point-p (car cps) ver))))
           (mark-clusters-p (bidi-clusters cps ver) ver))
  :cases ((consp cps))
  :expand ((mark-clusters-p (bidi-clusters cps ver) ver)
           (bidi-class-kind-present-p :left-to-right cps ver))
  :enable (mark-cluster-p
           bidi-combining-mark-p-when-not-left-to-right))

(defrulel display-of-middle-code-points
  (implies (and (code-point-listp middle)
                (not (bidi-class-kind-present-p :left-to-right middle ver))
                (not (and (consp middle)
                          (bidi-mark-code-point-p (car middle) ver))))
           (equal (bidi-mirror-chars
                   (bidi-arrange-with-levels
                    middle
                    (bidi-middle-levels (bidi-clusters middle ver)
                                        arabic
                                        ver)
                    ver)
                   ver)
                  (acl2::flatten
                   (bidi-show-clusters (bidi-clusters middle ver)
                                       arabic
                                       ver))))
  :use (:instance display-of-middle
                  (clusters (bidi-clusters middle ver)))
  :disable display-of-middle)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The parts at level 0 are displayed as they are stored.

(defrulel nat-listp-of-repeat
  (implies (natp x)
           (nat-listp (acl2::repeat n x)))
  :induct (acl2::repeat n x)
  :enable acl2::repeat)

(defrulel bidi-move-marks-when-shown-all-0
  (implies (shown-all x 0)
           (equal (bidi-move-marks x nil ver)
                  (bidi-shown-char-list-fix x)))
  :induct (len x)
  :enable (len shown-all bidi-shown-char-list-fix)
  :expand (bidi-move-marks x nil ver))

(defrulel bidi-mirror-chars-of-bidi-shown-chars-of-repeat-of-0
  (implies (<= (len cps) (nfix n))
           (equal (bidi-mirror-chars (bidi-shown-chars cps (acl2::repeat n 0))
                                     ver)
                  (code-point-list-fix cps)))
  :induct (list-and-count-induction cps n)
  :enable (list-and-count-induction
           bidi-shown-chars
           bidi-mirror-chars
           bidi-mirror-char
           acl2::repeat
           code-point-list-fix
           len))

(defrulel bidi-arrange-with-levels-of-zeros
  (equal (bidi-arrange-with-levels cps (acl2::repeat (len cps) 0) ver)
         (bidi-shown-chars cps (acl2::repeat (len cps) 0)))
  :enable (bidi-arrange-with-levels
           bidi-shown-chars-at-of-bidi-positions-with-level))

; The cuts between the three parts are clean.

(defrulel bidi-clean-cut-p-after-zeros
  (implies (natp n)
           (bidi-clean-cut-p n (append (acl2::repeat n 0) levels)))
  :cases ((zp n))
  :enable bidi-clean-cut-p)

(defrulel bidi-clean-cut-p-before-zeros
  (implies (nat-listp levels)
           (bidi-clean-cut-p (len levels)
                             (append levels (acl2::repeat n 0))))
  :cases ((zp n))
  :enable bidi-clean-cut-p)

(defrulel bidi-arrange-with-levels-of-three-parts
  (implies (and (nat-listp levels)
                (equal (len levels) (len middle)))
           (equal (bidi-arrange-with-levels
                   (append before (append middle after))
                   (append (acl2::repeat (len before) 0)
                           (append levels
                                   (acl2::repeat (len after) 0)))
                   ver)
                  (append (bidi-shown-chars before
                                            (acl2::repeat (len before) 0))
                          (append (bidi-arrange-with-levels middle levels ver)
                                  (bidi-shown-chars
                                   after
                                   (acl2::repeat (len after) 0)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The three parts of a name.

(local
 (define split-induction (start end x)
   (if (zp start)
       (list end x)
     (split-induction (- start 1) (- end 1) (cdr x)))
   :verify-guards nil
   :hooks nil))

(defrulel append-of-take-and-nthcdr-of-take
  (implies (and (natp start)
                (natp end)
                (<= start end))
           (equal (append (take start x)
                          (append (nthcdr start (take end x)) y))
                  (append (take end x) y)))
  :induct (split-induction start end x)
  :enable (split-induction take nthcdr))

(defrulel append-of-take-and-nthcdr-when-true-listp
  (implies (and (true-listp x)
                (natp end)
                (<= end (len x)))
           (equal (append (take end x) (nthcdr end x))
                  x))
  :induct (nthcdr end x)
  :enable (take nthcdr len))

(defrulel bidi-right-to-left-letter-p-of-nth-of-bidi-name-start
  (implies (< (bidi-name-start name ver) (len name))
           (bidi-right-to-left-letter-p (nth (bidi-name-start name ver) name)
                                        ver))
  :induct (bidi-name-start name ver)
  :enable (bidi-name-start nth len))

(defrulel not-bidi-mark-code-point-p-when-bidi-right-to-left-letter-p
  (implies (bidi-right-to-left-letter-p cp ver)
           (not (bidi-mark-code-point-p cp ver)))
  :enable (bidi-right-to-left-letter-p bidi-mark-code-point-p))

(defrulel not-bidi-class-kind-present-p-of-nthcdr
  (implies (not (bidi-class-kind-present-p kind x ver))
           (not (bidi-class-kind-present-p kind (nthcdr n x) ver)))
  :induct (nthcdr n x)
  :enable (nthcdr bidi-class-kind-present-p))

(defrulel not-bidi-class-kind-present-p-of-take
  (implies (and (not (bidi-class-kind-present-p kind x ver))
                (<= (nfix n) (len x)))
           (not (bidi-class-kind-present-p kind (take n x) ver)))
  :induct (take n x)
  :enable (take bidi-class-kind-present-p len))

(defrulel display-from-levels-when-code-point-listp
  (implies (and (code-point-listp name)
                (not (bidi-class-kind-present-p :left-to-right name ver)))
           (equal (bidi-mirror-chars
                   (bidi-arrange-with-levels name
                                             (bidi-name-levels name ver)
                                             ver)
                   ver)
                  (bidi-name-display name ver)))
  :enable (bidi-name-levels
           bidi-name-display)
  :use (:instance bidi-arrange-with-levels-of-three-parts
                  (before (take (bidi-name-start name ver) name))
                  (middle (nthcdr (bidi-name-start name ver)
                                  (take (bidi-name-end name ver) name)))
                  (after (nthcdr (bidi-name-end name ver) name))
                  (levels (bidi-middle-levels
                           (bidi-clusters
                            (nthcdr (bidi-name-start name ver)
                                    (take (bidi-name-end name ver) name))
                            ver)
                           nil
                           ver)))
  :disable (bidi-arrange-with-levels-of-three-parts
            bidi-arrange-with-levels-of-append-when-bidi-clean-cut-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-display-order
  :parents (bidi-rule-display)
  :short "From the levels that @(tsee bidi-name-levels) gives,
          rules L2, L3 and L4 of the Unicode Bidirectional Algorithm
          give the display that @(tsee bidi-name-display) gives."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem is about the last three rules of the algorithm [UAX #9],
     as @(tsee bidi-arrange-with-levels) and @(tsee bidi-mirror-chars)
     model them; the levels are not those of the algorithm,
     but those of @(tsee bidi-name-levels).
     The condition is that the name has no code point of class @('L')
     (@('Left_To_Right')).
     It is there for rule L3, which goes by the general category
     of a character while the clusters of a name go by its class:
     the two agree on the characters that are not of class @('L')
     (see @(see bidi-combining-mark-class)).")
   (xdoc::p
    "The cuts before and after the middle part of the name are clean
     (see @(tsee bidi-clean-cut-p)),
     so the three parts are put in order separately
     (see @(see bidi-clean-cut-display)).
     The two outer parts are at level 0 and stay as they are.
     In the middle part every level is 1 or 2:
     rule L2 reverses each run of characters at level 2,
     which are the numbers, and then the whole part,
     so the numbers are back in their order
     and everything else is reversed;
     rule L3 puts the marks of each cluster at level 1
     back after the character that they follow;
     and rule L4 replaces the mirrored characters at level 1.
     That is what @(tsee bidi-show-clusters) does."))

  (defrule bidi-mirror-chars-of-bidi-arrange-with-levels-of-bidi-name-levels
    (implies (not (bidi-class-kind-present-p :left-to-right name ver))
             (equal (bidi-mirror-chars
                     (bidi-arrange-with-levels name
                                               (bidi-name-levels name ver)
                                               ver)
                     ver)
                    (bidi-name-display name ver)))
    :use (:instance display-from-levels-when-code-point-listp
                    (name (code-point-list-fix name)))))
