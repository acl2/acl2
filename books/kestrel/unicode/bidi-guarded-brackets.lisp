; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-neutral-types")
(include-book "bidi-guarded-weak")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book is a step of the proofs of the theorems of the books
; bidi-guarded-theorem.lisp and bidi-self-contained.lisp.
; Those books include this one locally,
; through the book bidi-guarded-neutral.lisp.
; See each of the two books for the outline of its proof.
;
; This book proves facts about the bracket pairs
; that BIDI-BRACKET-PAIRS finds [UAX #9, BD16]:
;
;   in each pair, the opening bracket is before the closing bracket;
;   the opening bracket has an opening role and the class ON,
;   and the closing bracket has a closing role;
;   no two pairs have the same opening bracket;
;   no two pairs cross, and the pairs are in the order
;   of their opening brackets (the proof of the book
;   bidi-rule-display-levels.lisp uses this);
;   the pairs found after rules W1 to W7 are those found before,
;   if every position that has a bracket role has the class ON.
;
; For the second proof, it also proves a fact about a part of a sequence:
; if the search for the pairs does not give up,
; and no pair closes in the part after opening before it,
; the pairs that close in the part are the pairs of the part alone,
; moved to the position of the part
; (see the section "The pairs of a part of a sequence" below).
;
; The definitions of this book are for the proofs only.
; The guards of those that look into a list at a position
; that may be beyond its end are not verified.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definitions that the other books of the proofs use.

; The positions of the opening brackets of the pairs.

(define bidi-pair-opens ((pairs bracket-pair-listp))
  :returns (opens nat-listp)
  (if (endp pairs)
      nil
    (cons (bracket-pair->open (car pairs))
          (bidi-pair-opens (cdr pairs))))
  :hooks nil)

; A pair is sound for a list of classes and a list of roles
; if its opening bracket is before its closing bracket,
; has an opening role and has the class ON,
; and its closing bracket has a closing role.

(define bidi-pair-sound-p ((pair bracket-pair-p)
                           (classes bidi-class-listp)
                           (roles bidi-bracket-role-listp))
  :returns (yes/no booleanp)
  (b* (((bracket-pair pair)))
    (and (< pair.open pair.close)
         (equal (bidi-bracket-role-kind (nth pair.open roles)) :open)
         (equal (bidi-bracket-role-kind (nth pair.close roles)) :close)
         (equal (bidi-class-kind (nth pair.open classes)) :other-neutral)))
  :verify-guards nil
  :hooks nil)

(define bidi-pairs-sound-p ((pairs bracket-pair-listp)
                            (classes bidi-class-listp)
                            (roles bidi-bracket-role-listp))
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (bidi-pair-sound-p (car pairs) classes roles)
           (bidi-pairs-sound-p (cdr pairs) classes roles)))
  :verify-guards nil
  :hooks nil)

; A pair, and a list of pairs, moved by a number of positions.

(define bidi-pair-shift ((pair bracket-pair-p) (offset natp))
  :returns (new-pair bracket-pair-p)
  (make-bracket-pair :open (+ (bracket-pair->open pair) (lnfix offset))
                     :close (+ (bracket-pair->close pair) (lnfix offset)))
  :hooks nil
  ///
  (defret bracket-pair->open-of-bidi-pair-shift
    (equal (bracket-pair->open new-pair)
           (+ (bracket-pair->open pair) (nfix offset)))
    :hints (("Goal" :in-theory (enable nfix))))
  (defret bracket-pair->close-of-bidi-pair-shift
    (equal (bracket-pair->close new-pair)
           (+ (bracket-pair->close pair) (nfix offset)))
    :hints (("Goal" :in-theory (enable nfix)))))

(define bidi-pairs-shift ((pairs bracket-pair-listp) (offset natp))
  :returns (new-pairs bracket-pair-listp)
  (if (endp pairs)
      nil
    (cons (bidi-pair-shift (car pairs) offset)
          (bidi-pairs-shift (cdr pairs) offset)))
  :hooks nil)

; The pairs whose closing bracket is at a position from START to END-1.

(define bidi-pairs-closing-in ((pairs bracket-pair-listp)
                               (start natp)
                               (end natp))
  :returns (some-pairs bracket-pair-listp)
  (cond ((endp pairs) nil)
        ((and (<= (lnfix start) (bracket-pair->close (car pairs)))
              (< (bracket-pair->close (car pairs)) (lnfix end)))
         (cons (bracket-pair-fix (car pairs))
               (bidi-pairs-closing-in (cdr pairs) start end)))
        (t (bidi-pairs-closing-in (cdr pairs) start end)))
  :hooks nil)

; No pair has its closing bracket at a position from START to END-1
; and its opening bracket before START.

(define bidi-pairs-none-entering-p ((pairs bracket-pair-listp)
                                    (start natp)
                                    (end natp))
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (or (<= (lnfix start) (bracket-pair->open (car pairs)))
               (< (bracket-pair->close (car pairs)) (lnfix start))
               (<= (lnfix end) (bracket-pair->close (car pairs))))
           (bidi-pairs-none-entering-p (cdr pairs) start end)))
  :hooks nil)

; A pair X is before a pair Y: X opens before Y,
; and Y is all after X or all inside X.
; In a nested list of pairs, each pair is before every later pair,
; so that no two pairs cross.

(define bidi-pair-before-p ((x bracket-pair-p) (y bracket-pair-p))
  :returns (yes/no booleanp)
  (b* (((bracket-pair x))
       ((bracket-pair y)))
    (and (< x.open y.open)
         (or (< x.close y.open)
             (< y.close x.close))))
  :hooks nil)

(define bidi-pair-before-all-p ((x bracket-pair-p) (pairs bracket-pair-listp))
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (bidi-pair-before-p x (car pairs))
           (bidi-pair-before-all-p x (cdr pairs))))
  :hooks nil)

(define bidi-pairs-nested-p ((pairs bracket-pair-listp))
  :returns (yes/no booleanp)
  (or (endp pairs)
      (and (bidi-pair-before-all-p (car pairs) (cdr pairs))
           (bidi-pairs-nested-p (cdr pairs))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here on, the events are local, except the theorems at the end.

(local
 (define list-induction (x)
   (if (consp x)
       (list-induction (cdr x))
     nil)
   :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The stack of the opening brackets that have no closing bracket yet.
; Its positions go down from the top, and are below the current position.
; Each has an opening role, in the list ALL of the roles of the sequence.

(local
 (define stack-positions ((stack open-bracket-listp))
   :returns (positions nat-listp)
   (if (endp stack)
       nil
     (cons (open-bracket->position (car stack))
           (stack-positions (cdr stack))))
   :hooks nil))

(local
 (define stack-below ((stack open-bracket-listp) (bound natp))
   :returns (yes/no booleanp)
   (or (endp stack)
       (and (< (open-bracket->position (car stack)) (nfix bound))
            (stack-below (cdr stack)
                         (open-bracket->position (car stack)))))
   :hooks nil))

(local
 (define stack-opens ((stack open-bracket-listp) all)
   :returns (yes/no booleanp)
   (or (endp stack)
       (and (equal (bidi-bracket-role-kind
                    (nth (open-bracket->position (car stack)) all))
                   :open)
            (stack-opens (cdr stack) all)))
   :verify-guards nil
   :hooks nil))

(defrulel stack-positions-of-open-bracket-list-fix
  (equal (stack-positions (open-bracket-list-fix stack))
         (stack-positions stack))
  :induct (list-induction stack)
  :enable (list-induction
           stack-positions
           open-bracket-list-fix))

(defrulel stack-opens-of-open-bracket-list-fix
  (equal (stack-opens (open-bracket-list-fix stack) all)
         (stack-opens stack all))
  :induct (list-induction stack)
  :enable (list-induction
           stack-opens
           open-bracket-list-fix))

(local
 (define stack-induction (stack bound)
   (if (consp stack)
       (stack-induction (cdr stack)
                        (open-bracket->position (car stack)))
     bound)
   :verify-guards nil
   :hooks nil))

(defrulel stack-below-of-open-bracket-list-fix
  (equal (stack-below (open-bracket-list-fix stack) bound)
         (stack-below stack bound))
  :induct (stack-induction stack bound)
  :enable (stack-induction
           stack-below
           open-bracket-list-fix))

(defrulel stack-below-when-below-less
  (implies (and (stack-below stack bound)
                (<= (nfix bound) (nfix bound2)))
           (stack-below stack bound2))
  :expand ((stack-below stack bound)
           (stack-below stack bound2)))

(defrulel not-member-equal-of-stack-positions-when-stack-below
  (implies (and (stack-below stack bound)
                (<= (nfix bound) position))
           (not (member-equal position (stack-positions stack))))
  :induct (stack-induction stack bound)
  :enable (stack-induction
           stack-below
           stack-positions
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The search of the stack for the opening bracket of a closing bracket.

(local
 (define find-induction (stack id bound)
   (b* (((when (endp stack)) bound)
        ((open-bracket top) (car stack))
        ((when (equal top.id (code-point-fix id))) bound))
     (find-induction (cdr stack) id top.position))
   :verify-guards nil
   :hooks nil))

(defrulel open-bracket-stack-find-when-stack-below
  (b* (((mv found position rest) (open-bracket-stack-find stack id)))
    (implies (and (stack-below stack bound)
                  found)
             (and (< position (nfix bound))
                  (stack-below rest position)
                  (not (member-equal position (stack-positions rest))))))
  :induct (find-induction stack id bound)
  :enable (find-induction
           open-bracket-stack-find
           stack-below
           nfix))

(defrulel stack-below-of-rest-of-open-bracket-stack-find
  (b* (((mv found & rest) (open-bracket-stack-find stack id)))
    (implies (and (stack-below stack bound)
                  found
                  (<= (nfix bound) (nfix bound2)))
             (stack-below rest bound2)))
  :induct (find-induction stack id bound)
  :enable (find-induction
           open-bracket-stack-find
           stack-below
           nfix))

(defrulel open-bracket-stack-find-when-stack-below-linear
  (b* (((mv found position &) (open-bracket-stack-find stack id)))
    (implies (and (stack-below stack bound)
                  found
                  (natp bound))
             (< position bound)))
  :rule-classes :linear
  :induct (find-induction stack id bound)
  :enable (find-induction
           open-bracket-stack-find
           stack-below
           nfix))

(defrulel open-bracket-stack-find-when-stack-opens
  (b* (((mv found position rest) (open-bracket-stack-find stack id)))
    (implies (stack-opens stack all)
             (and (implies found
                           (equal (bidi-bracket-role-kind (nth position all))
                                  :open))
                  (stack-opens rest all))))
  :induct (list-induction stack)
  :enable (list-induction
           open-bracket-stack-find
           stack-opens))

(defrulel member-equal-of-open-bracket-stack-find
  (b* (((mv found position &) (open-bracket-stack-find stack id)))
    (implies found
             (member-equal position (stack-positions stack))))
  :induct (list-induction stack)
  :enable (list-induction
           open-bracket-stack-find
           stack-positions))

(defrulel not-member-equal-of-rest-of-open-bracket-stack-find
  (b* (((mv & & rest) (open-bracket-stack-find stack id)))
    (implies (not (member-equal position (stack-positions stack)))
             (not (member-equal position (stack-positions rest)))))
  :induct (list-induction stack)
  :enable (list-induction
           open-bracket-stack-find
           stack-positions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The pairs, for a list of roles ALL of the whole sequence.
; The pairing goes along the list of the roles with the current position;
; SUFFIX-AT-P says that the roles left are those from that position on.

(local
 (define pair-roles-ok ((pair bracket-pair-p) all)
   :returns (yes/no booleanp)
   (b* (((bracket-pair pair)))
     (and (< pair.open pair.close)
          (equal (bidi-bracket-role-kind (nth pair.open all)) :open)
          (equal (bidi-bracket-role-kind (nth pair.close all)) :close)))
   :verify-guards nil
   :hooks nil))

(local
 (define pairs-roles-ok ((pairs bracket-pair-listp) all)
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (pair-roles-ok (car pairs) all)
            (pairs-roles-ok (cdr pairs) all)))
   :verify-guards nil
   :hooks nil))

(local
 (define suffix-at-p (roles (position natp) all)
   :returns (yes/no booleanp)
   (equal roles (nthcdr position all))
   :verify-guards nil
   :hooks nil))

(defruledl nthcdr-of-+-of-1
  (implies (natp n)
           (equal (nthcdr (+ 1 n) x)
                  (cdr (nthcdr n x))))
  :induct (nthcdr n x)
  :enable (nthcdr natp fix))

(defrulel suffix-at-p-of-cdr
  (implies (and (suffix-at-p roles position all)
                (consp roles)
                (natp position))
           (suffix-at-p (cdr roles) (+ 1 position) all))
  :enable (suffix-at-p
           nthcdr-of-+-of-1))

(defrulel nth-when-suffix-at-p
  (implies (and (suffix-at-p roles position all)
                (consp roles)
                (natp position))
           (equal (nth position all)
                  (car roles)))
  :enable suffix-at-p)

(defrulel suffix-at-p-of-0
  (suffix-at-p all 0 all)
  :enable suffix-at-p)

(defrulel pairs-roles-ok-of-bidi-bracket-pairs-from
  (implies (and (suffix-at-p roles position all)
                (stack-below stack position)
                (stack-opens stack all)
                (natp position))
           (pairs-roles-ok
            (mv-nth 1 (bidi-bracket-pairs-from roles position stack))
            all))
  :induct (bidi-bracket-pairs-from roles position stack)
  :enable (bidi-bracket-pairs-from
           pairs-roles-ok
           pair-roles-ok
           stack-below
           stack-opens
           nfix
           natp))

(defrulel not-member-equal-of-bidi-pair-opens-of-bidi-bracket-pairs-from
  (implies (and (not (member-equal open (stack-positions stack)))
                (< open position)
                (natp position))
           (not (member-equal
                 open
                 (bidi-pair-opens
                  (mv-nth 1
                          (bidi-bracket-pairs-from roles position stack))))))
  :induct (bidi-bracket-pairs-from roles position stack)
  :enable (bidi-bracket-pairs-from
           bidi-pair-opens
           stack-positions
           nfix
           natp))

(defrulel no-duplicatesp-equal-of-bidi-pair-opens-of-bidi-bracket-pairs-from
  (implies (and (stack-below stack position)
                (natp position))
           (no-duplicatesp-equal
            (bidi-pair-opens
             (mv-nth 1 (bidi-bracket-pairs-from roles position stack)))))
  :induct (bidi-bracket-pairs-from roles position stack)
  :enable (bidi-bracket-pairs-from
           bidi-pair-opens
           stack-below
           nfix
           natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The sorting of the pairs.

(defrulel pairs-roles-ok-of-bracket-pair-list-fix
  (equal (pairs-roles-ok (bracket-pair-list-fix pairs) all)
         (pairs-roles-ok pairs all))
  :induct (list-induction pairs)
  :enable (list-induction
           pairs-roles-ok
           pair-roles-ok
           bracket-pair-list-fix))

(defrulel bidi-pair-opens-of-bracket-pair-list-fix
  (equal (bidi-pair-opens (bracket-pair-list-fix pairs))
         (bidi-pair-opens pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pair-opens
           bracket-pair-list-fix))

(defrulel pairs-roles-ok-of-bracket-pair-insert
  (implies (and (pair-roles-ok pair all)
                (pairs-roles-ok pairs all))
           (pairs-roles-ok (bracket-pair-insert pair pairs) all))
  :induct (bracket-pair-insert pair pairs)
  :enable (bracket-pair-insert
           pairs-roles-ok
           pair-roles-ok))

(defrulel pairs-roles-ok-of-bracket-pairs-sort
  (implies (pairs-roles-ok pairs all)
           (pairs-roles-ok (bracket-pairs-sort pairs) all))
  :induct (bracket-pairs-sort pairs)
  :enable (bracket-pairs-sort
           pairs-roles-ok))

(defrulel member-equal-of-bidi-pair-opens-of-bracket-pair-insert
  (iff (member-equal open (bidi-pair-opens (bracket-pair-insert pair pairs)))
       (or (equal open (bracket-pair->open pair))
           (member-equal open (bidi-pair-opens pairs))))
  :induct (bracket-pair-insert pair pairs)
  :enable (bracket-pair-insert
           bidi-pair-opens))

(defrulel no-duplicatesp-equal-of-bidi-pair-opens-of-bracket-pair-insert
  (equal (no-duplicatesp-equal
          (bidi-pair-opens (bracket-pair-insert pair pairs)))
         (and (not (member-equal (bracket-pair->open pair)
                                 (bidi-pair-opens pairs)))
              (no-duplicatesp-equal (bidi-pair-opens pairs))))
  :induct (bracket-pair-insert pair pairs)
  :enable (bracket-pair-insert
           bidi-pair-opens))

(defrulel member-equal-of-bidi-pair-opens-of-bracket-pairs-sort
  (iff (member-equal open (bidi-pair-opens (bracket-pairs-sort pairs)))
       (member-equal open (bidi-pair-opens pairs)))
  :induct (bracket-pairs-sort pairs)
  :enable (bracket-pairs-sort
           bidi-pair-opens))

(defrulel no-duplicatesp-equal-of-bidi-pair-opens-of-bracket-pairs-sort
  (implies (no-duplicatesp-equal (bidi-pair-opens pairs))
           (no-duplicatesp-equal (bidi-pair-opens (bracket-pairs-sort pairs))))
  :induct (bracket-pairs-sort pairs)
  :enable (bracket-pairs-sort
           bidi-pair-opens))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The roles that count for the pairing are those of the positions
; whose class is ON.  So a position with such a role
; has the same role in the list of all the roles, and has the class ON.

(local
 (define nth-two-induction ((position natp) x y)
   (if (or (zp position)
           (atom x)
           (atom y))
       nil
     (nth-two-induction (- position 1) (cdr x) (cdr y)))
   :verify-guards nil
   :hooks nil))

(defrulel role-and-class-when-current-role-is-open
  (implies (equal (bidi-bracket-role-kind
                   (nth position (bidi-current-bracket-roles classes roles)))
                  :open)
           (and (equal (bidi-bracket-role-kind (nth position roles))
                       :open)
                (equal (bidi-class-kind (nth position classes))
                       :other-neutral)))
  :induct (nth-two-induction position classes roles)
  :expand (bidi-current-bracket-roles classes roles)
  :enable (nth-two-induction
           bidi-current-bracket-roles
           nth))

(defrulel role-when-current-role-is-close
  (implies (equal (bidi-bracket-role-kind
                   (nth position (bidi-current-bracket-roles classes roles)))
                  :close)
           (equal (bidi-bracket-role-kind (nth position roles))
                  :close))
  :induct (nth-two-induction position classes roles)
  :expand (bidi-current-bracket-roles classes roles)
  :enable (nth-two-induction
           bidi-current-bracket-roles
           nth))

(defrulel bidi-pairs-sound-p-when-pairs-roles-ok
  (implies (pairs-roles-ok pairs (bidi-current-bracket-roles classes roles))
           (bidi-pairs-sound-p pairs classes roles))
  :induct (list-induction pairs)
  :enable (list-induction
           pairs-roles-ok
           pair-roles-ok
           bidi-pairs-sound-p
           bidi-pair-sound-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If every position that has a bracket role has the class ON,
; the roles that count for the pairing are all the roles,
; cut to the length of the list of the classes.

(local
 (define roles-cut ((count natp) (roles bidi-bracket-role-listp))
   :returns (new-roles bidi-bracket-role-listp)
   (if (or (zp count)
           (endp roles))
       nil
     (cons (bidi-bracket-role-fix (car roles))
           (roles-cut (- count 1) (cdr roles))))
   :hooks nil))

(local
 (define two-lists-induction (x y)
   (if (and (consp x)
            (consp y))
       (two-lists-induction (cdr x) (cdr y))
     nil)
   :hooks nil))

(defrulel fix-of-len
  (equal (fix (len x))
         (len x))
  :enable fix)

(defruledl bidi-current-bracket-roles-when-bidi-roles-neutral-p
  (implies (bidi-roles-neutral-p roles classes)
           (equal (bidi-current-bracket-roles classes roles)
                  (roles-cut (len classes) roles)))
  :induct (two-lists-induction classes roles)
  :expand ((bidi-current-bracket-roles classes roles)
           (:free (count) (roles-cut count roles)))
  :enable (two-lists-induction
           bidi-roles-neutral-p
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The pairs of a part of a sequence.
;
; The rest of this book proves the last theorem of the book:
; in a sequence made of three parts, if the pairing does not give up
; and no pair has its closing bracket in the second part
; and its opening bracket in the first part,
; then the pairs that close in the second part
; are the pairs of the second part alone, moved to its position.
;
; The pairing goes along the roles with a stack.
; The pairs found in the first part do not depend on the rest;
; the second part is then read with the stack that the first part leaves.
; A closing bracket of the second part that finds its opening bracket
; in the stack finds it among the brackets of the second part,
; because otherwise there would be a pair of the kind that is excluded;
; so the stack of the first part plays no part,
; and the pairs are those that the second part gives with an empty stack.
; The pairs are then sorted by their opening brackets,
; and taking the pairs that close in a range of positions
; can be done before or after the sorting.

(defrulel nfix-of-len
  (equal (nfix (len x))
         (len x))
  :enable nfix)

(defrulel fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x))
  :enable fix)

(defrulel bidi-pairs-closing-in-when-not-consp
  (implies (not (consp pairs))
           (equal (bidi-pairs-closing-in pairs lo hi)
                  nil))
  :expand (bidi-pairs-closing-in pairs lo hi))

(defrulel bidi-pairs-shift-when-not-consp
  (implies (not (consp pairs))
           (equal (bidi-pairs-shift pairs offset)
                  nil))
  :expand (bidi-pairs-shift pairs offset))

; The stack after a list of roles, if the pairing does not give up.

(local
 (define stack-after ((roles bidi-bracket-role-listp)
                      (position natp)
                      (stack open-bracket-listp))
   :returns (new-stack open-bracket-listp)
   (b* (((when (endp roles)) (open-bracket-list-fix stack))
        (position (lnfix position))
        (role (bidi-bracket-role-fix (car roles))))
     (bidi-bracket-role-case
      role
      :none (stack-after (cdr roles) (+ 1 position) stack)
      :open (stack-after (cdr roles)
                         (+ 1 position)
                         (cons (make-open-bracket :id role.id
                                                  :position position)
                               (open-bracket-list-fix stack)))
      :close (b* (((mv found & rest)
                   (open-bracket-stack-find stack role.id)))
               (stack-after (cdr roles)
                            (+ 1 position)
                            (if found
                                rest
                              stack)))))
   :hooks nil))

(defrulel overflow-of-bidi-bracket-pairs-from-of-append
  (implies (natp position)
           (equal (mv-nth 0 (bidi-bracket-pairs-from (append x y)
                                                     position
                                                     stack))
                  (or (mv-nth 0 (bidi-bracket-pairs-from x position stack))
                      (mv-nth 0 (bidi-bracket-pairs-from
                                 y
                                 (+ position (len x))
                                 (stack-after x position stack))))))
  :induct (stack-after x position stack)
  :expand ((bidi-bracket-pairs-from x position stack)
           (:free (a b) (bidi-bracket-pairs-from (cons a b) position stack))
           (append x y))
  :enable (stack-after len nfix))

(defrulel pairs-of-bidi-bracket-pairs-from-of-append
  (implies (and (natp position)
                (not (mv-nth 0 (bidi-bracket-pairs-from x position stack))))
           (equal (mv-nth 1 (bidi-bracket-pairs-from (append x y)
                                                     position
                                                     stack))
                  (append (mv-nth 1 (bidi-bracket-pairs-from x position stack))
                          (mv-nth 1 (bidi-bracket-pairs-from
                                     y
                                     (+ position (len x))
                                     (stack-after x position stack))))))
  :induct (stack-after x position stack)
  :expand ((bidi-bracket-pairs-from x position stack)
           (:free (a b) (bidi-bracket-pairs-from (cons a b) position stack))
           (append x y))
  :enable (stack-after len nfix))

(defrulel stack-below-of-stack-after
  (implies (and (stack-below stack position)
                (natp position)
                (natp bound)
                (<= (+ position (len roles)) bound))
           (stack-below (stack-after roles position stack) bound))
  :induct (stack-after roles position stack)
  :enable (stack-after stack-below len nfix))

; The pairs found in a list of roles have their closing brackets
; at the positions of the list.

(defrulel bidi-pairs-closing-in-of-bidi-bracket-pairs-from-when-apart
  (implies (and (natp position)
                (natp lo)
                (natp hi)
                (or (<= (+ position (len roles)) lo)
                    (<= hi position)))
           (equal (bidi-pairs-closing-in
                   (mv-nth 1 (bidi-bracket-pairs-from roles position stack))
                   lo
                   hi)
                  nil))
  :induct (bidi-bracket-pairs-from roles position stack)
  :enable (bidi-bracket-pairs-from
           bidi-pairs-closing-in
           len
           nfix))

;;;;;;;;;;;;;;;;;;;;

; The pairing of a list of roles with a deeper stack.

(local
 (define stack-shift ((stack open-bracket-listp) (offset natp))
   :returns (new-stack open-bracket-listp)
   (if (endp stack)
       nil
     (cons (make-open-bracket
            :id (open-bracket->id (car stack))
            :position (+ (open-bracket->position (car stack))
                         (lnfix offset)))
           (stack-shift (cdr stack) offset)))
   :hooks nil
   ///
   (defret len-of-stack-shift
     (equal (len new-stack)
            (len stack))
     :hints (("Goal" :induct t :in-theory (enable len))))))

(defrulel stack-shift-of-open-bracket-list-fix
  (equal (stack-shift (open-bracket-list-fix stack) offset)
         (stack-shift stack offset))
  :induct (list-induction stack)
  :enable (list-induction
           stack-shift
           open-bracket-list-fix))

(defrulel open-bracket-stack-find-when-not-consp
  (implies (not (consp stack))
           (equal (open-bracket-stack-find stack id)
                  (list nil 0 nil)))
  :expand (open-bracket-stack-find stack id))

(defrulel open-bracket-stack-find-of-append
  (equal (open-bracket-stack-find (append stack1 stack2) id)
         (if (mv-nth 0 (open-bracket-stack-find stack1 id))
             (list t
                   (mv-nth 1 (open-bracket-stack-find stack1 id))
                   (append (mv-nth 2 (open-bracket-stack-find stack1 id))
                           (open-bracket-list-fix stack2)))
           (open-bracket-stack-find stack2 id)))
  :induct (list-induction stack1)
  :expand ((open-bracket-stack-find stack1 id)
           (:free (a b) (open-bracket-stack-find (cons a b) id))
           (append stack1 stack2))
  :enable (list-induction
           open-bracket-list-fix))

(defrulel open-bracket-stack-find-of-stack-shift
  (equal (open-bracket-stack-find (stack-shift stack offset) id)
         (list (mv-nth 0 (open-bracket-stack-find stack id))
               (if (mv-nth 0 (open-bracket-stack-find stack id))
                   (+ (mv-nth 1 (open-bracket-stack-find stack id))
                      (nfix offset))
                 0)
               (stack-shift (mv-nth 2 (open-bracket-stack-find stack id))
                            offset)))
  :induct (list-induction stack)
  :expand ((open-bracket-stack-find stack id)
           (:free (a b) (open-bracket-stack-find (cons a b) id)))
  :enable (list-induction
           stack-shift
           nfix))

(defrulel bidi-bracket-pairs-from-with-deeper-stack
  (b* (((mv overflow1 pairs1)
        (bidi-bracket-pairs-from roles
                                 (+ position offset)
                                 (append (stack-shift stack1 offset) stack)))
       ((mv overflow2 pairs2)
        (bidi-bracket-pairs-from roles position stack1)))
    (implies (and (natp position)
                  (natp offset)
                  (natp end)
                  (<= (+ position offset (len roles)) end)
                  (not overflow1)
                  (stack-below stack offset)
                  (bidi-pairs-none-entering-p pairs1 offset end))
             (and (not overflow2)
                  (equal pairs1
                         (bidi-pairs-shift pairs2 offset)))))
  :rule-classes nil
  :induct (stack-after roles position stack1)
  :expand ((:free (position stack)
                  (bidi-bracket-pairs-from roles position stack))
           (:free (a b) (bidi-pairs-none-entering-p (cons a b) offset end))
           (:free (a b) (bidi-pairs-shift (cons a b) offset)))
  :enable (stack-after
           stack-shift
           bidi-pairs-shift
           bidi-pair-shift
           len
           nfix))

(defrulel bidi-bracket-pairs-from-with-stack
  (b* (((mv overflow1 pairs1)
        (bidi-bracket-pairs-from roles offset stack))
       ((mv overflow2 pairs2)
        (bidi-bracket-pairs-from roles 0 nil)))
    (implies (and (natp offset)
                  (natp end)
                  (<= (+ offset (len roles)) end)
                  (not overflow1)
                  (stack-below stack offset)
                  (bidi-pairs-none-entering-p pairs1 offset end))
             (and (not overflow2)
                  (equal pairs1
                         (bidi-pairs-shift pairs2 offset)))))
  :rule-classes nil
  :use (:instance bidi-bracket-pairs-from-with-deeper-stack
                  (position 0)
                  (stack1 nil))
  :enable stack-shift)

;;;;;;;;;;;;;;;;;;;;

; The pairs that close in a range, the pairs moved,
; and the pairs that do not enter a range, with the sorting.

(defrulel bidi-pairs-closing-in-of-append
  (equal (bidi-pairs-closing-in (append x y) lo hi)
         (append (bidi-pairs-closing-in x lo hi)
                 (bidi-pairs-closing-in y lo hi)))
  :induct (list-induction x)
  :enable (list-induction bidi-pairs-closing-in))

(defrulel bidi-pairs-closing-in-of-bidi-pairs-shift
  (implies (and (natp offset)
                (natp lo)
                (natp hi)
                (<= offset lo)
                (<= offset hi))
           (equal (bidi-pairs-closing-in (bidi-pairs-shift pairs offset) lo hi)
                  (bidi-pairs-shift (bidi-pairs-closing-in pairs
                                                           (- lo offset)
                                                           (- hi offset))
                                    offset)))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-closing-in
           bidi-pairs-shift
           bidi-pair-shift
           nfix))

(defrulel bidi-pairs-none-entering-p-of-append
  (equal (bidi-pairs-none-entering-p (append x y) start end)
         (and (bidi-pairs-none-entering-p x start end)
              (bidi-pairs-none-entering-p y start end)))
  :induct (list-induction x)
  :enable (list-induction bidi-pairs-none-entering-p))

(defrulel bidi-pairs-none-entering-p-of-bracket-pair-list-fix
  (equal (bidi-pairs-none-entering-p (bracket-pair-list-fix pairs) start end)
         (bidi-pairs-none-entering-p pairs start end))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-none-entering-p
           bracket-pair-list-fix))

(defrulel bidi-pairs-closing-in-of-bracket-pair-list-fix
  (equal (bidi-pairs-closing-in (bracket-pair-list-fix pairs) lo hi)
         (bidi-pairs-closing-in pairs lo hi))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-closing-in
           bracket-pair-list-fix))

(defrulel bidi-pairs-none-entering-p-of-bracket-pair-insert
  (equal (bidi-pairs-none-entering-p (bracket-pair-insert pair pairs)
                                     start
                                     end)
         (and (bidi-pairs-none-entering-p (list pair) start end)
              (bidi-pairs-none-entering-p pairs start end)))
  :induct (bracket-pair-insert pair pairs)
  :enable (bracket-pair-insert bidi-pairs-none-entering-p))

(defrulel bidi-pairs-none-entering-p-of-bracket-pairs-sort
  (equal (bidi-pairs-none-entering-p (bracket-pairs-sort pairs) start end)
         (bidi-pairs-none-entering-p pairs start end))
  :induct (bracket-pairs-sort pairs)
  :enable (bracket-pairs-sort bidi-pairs-none-entering-p))

(defrulel bidi-pair-shift-of-bracket-pair-fix
  (equal (bidi-pair-shift (bracket-pair-fix pair) offset)
         (bidi-pair-shift pair offset))
  :enable bidi-pair-shift)

(defrulel bidi-pairs-shift-of-bracket-pair-list-fix
  (equal (bidi-pairs-shift (bracket-pair-list-fix pairs) offset)
         (bidi-pairs-shift pairs offset))
  :induct (list-induction pairs)
  :enable (list-induction
           bidi-pairs-shift
           bidi-pair-shift
           bracket-pair-list-fix))

(defrulel bracket-pair-insert-of-bidi-pair-shift
  (equal (bracket-pair-insert (bidi-pair-shift pair offset)
                              (bidi-pairs-shift pairs offset))
         (bidi-pairs-shift (bracket-pair-insert pair pairs) offset))
  :induct (bracket-pair-insert pair pairs)
  :expand ((bidi-pairs-shift pairs offset)
           (bidi-pairs-shift nil offset)
           (:free (pair a b) (bracket-pair-insert pair (cons a b)))
           (:free (a b) (bidi-pairs-shift (cons a b) offset)))
  :enable (bracket-pair-insert
           nfix))

(defrulel bracket-pairs-sort-of-bidi-pairs-shift
  (equal (bracket-pairs-sort (bidi-pairs-shift pairs offset))
         (bidi-pairs-shift (bracket-pairs-sort pairs) offset))
  :induct (bracket-pairs-sort pairs)
  :enable (bracket-pairs-sort bidi-pairs-shift))

; Sorted pairs, and pairs whose opening brackets are from a position on.

(local
 (define pairs-open-from-p ((pairs bracket-pair-listp) (bound natp))
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (<= (lnfix bound) (bracket-pair->open (car pairs)))
            (pairs-open-from-p (cdr pairs) bound)))
   :hooks nil))

(local
 (define pairs-sorted-p ((pairs bracket-pair-listp))
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (pairs-open-from-p (cdr pairs) (bracket-pair->open (car pairs)))
            (pairs-sorted-p (cdr pairs))))
   :hooks nil))

(defrulel pairs-open-from-p-when-open-from-more
  (implies (and (pairs-open-from-p pairs bound)
                (<= (nfix bound2) (nfix bound)))
           (pairs-open-from-p pairs bound2))
  :induct (list-induction pairs)
  :enable (list-induction pairs-open-from-p nfix))

(defrulel pairs-open-from-p-of-bracket-pair-list-fix
  (equal (pairs-open-from-p (bracket-pair-list-fix pairs) bound)
         (pairs-open-from-p pairs bound))
  :induct (list-induction pairs)
  :enable (list-induction pairs-open-from-p bracket-pair-list-fix))

(defrulel pairs-sorted-p-of-bracket-pair-list-fix
  (equal (pairs-sorted-p (bracket-pair-list-fix pairs))
         (pairs-sorted-p pairs))
  :induct (list-induction pairs)
  :enable (list-induction pairs-sorted-p bracket-pair-list-fix))

(defrulel pairs-open-from-p-of-bracket-pair-insert
  (equal (pairs-open-from-p (bracket-pair-insert pair pairs) bound)
         (and (<= (nfix bound) (bracket-pair->open pair))
              (pairs-open-from-p pairs bound)))
  :induct (bracket-pair-insert pair pairs)
  :enable (bracket-pair-insert pairs-open-from-p))

(defrulel pairs-sorted-p-of-bracket-pair-insert
  (implies (pairs-sorted-p pairs)
           (pairs-sorted-p (bracket-pair-insert pair pairs)))
  :induct (bracket-pair-insert pair pairs)
  :enable (bracket-pair-insert pairs-sorted-p pairs-open-from-p nfix))

(defrulel pairs-sorted-p-of-bracket-pairs-sort
  (pairs-sorted-p (bracket-pairs-sort pairs))
  :induct (bracket-pairs-sort pairs)
  :enable (bracket-pairs-sort pairs-sorted-p))

(defrulel pairs-open-from-p-of-bidi-pairs-closing-in
  (implies (pairs-open-from-p pairs bound)
           (pairs-open-from-p (bidi-pairs-closing-in pairs lo hi) bound))
  :induct (list-induction pairs)
  :enable (list-induction pairs-open-from-p bidi-pairs-closing-in))

(defrulel bracket-pair-insert-when-pairs-open-from-p
  (implies (and (pairs-open-from-p pairs (bracket-pair->open pair))
                (bracket-pair-listp pairs))
           (equal (bracket-pair-insert pair pairs)
                  (cons (bracket-pair-fix pair) pairs)))
  :expand ((bracket-pair-insert pair pairs)
           (bracket-pair-insert pair nil)
           (pairs-open-from-p pairs (bracket-pair->open pair)))
  :enable nfix)

(defrulel bidi-pairs-closing-in-of-bracket-pair-insert
  (implies (pairs-sorted-p pairs)
           (equal (bidi-pairs-closing-in (bracket-pair-insert pair pairs)
                                         lo
                                         hi)
                  (if (and (<= (nfix lo) (bracket-pair->close pair))
                           (< (bracket-pair->close pair) (nfix hi)))
                      (bracket-pair-insert pair
                                           (bidi-pairs-closing-in pairs lo hi))
                    (bidi-pairs-closing-in pairs lo hi))))
  :induct (bracket-pair-insert pair pairs)
  :expand ((:free (a b) (bidi-pairs-closing-in (cons a b) lo hi))
           (bidi-pairs-closing-in pairs lo hi)
           (pairs-sorted-p pairs)
           (:free (a b) (bracket-pair-insert pair (cons a b))))
  :enable (bracket-pair-insert nfix))

(defrulel bidi-pairs-closing-in-of-bracket-pairs-sort
  (equal (bidi-pairs-closing-in (bracket-pairs-sort pairs) lo hi)
         (bracket-pairs-sort (bidi-pairs-closing-in pairs lo hi)))
  :induct (bracket-pairs-sort pairs)
  :expand ((bidi-pairs-closing-in pairs lo hi)
           (:free (a b) (bracket-pairs-sort (cons a b))))
  :enable (bracket-pairs-sort nfix))

;;;;;;;;;;;;;;;;;;;;

; The roles that count for the pairing, for a sequence in two parts.

(defrulel bidi-current-bracket-roles-of-append
  (implies (equal (len roles1) (len classes1))
           (equal (bidi-current-bracket-roles (append classes1 classes2)
                                              (append roles1 roles2))
                  (append (bidi-current-bracket-roles classes1 roles1)
                          (bidi-current-bracket-roles classes2 roles2))))
  :induct (two-lists-induction classes1 roles1)
  :expand ((bidi-current-bracket-roles classes1 roles1)
           (:free (a b c d) (bidi-current-bracket-roles (cons a b) (cons c d)))
           (append classes1 classes2)
           (append roles1 roles2))
  :enable (two-lists-induction len))

(defrulel len-of-bidi-current-bracket-roles
  (implies (equal (len roles) (len classes))
           (equal (len (bidi-current-bracket-roles classes roles))
                  (len classes)))
  :induct (two-lists-induction classes roles)
  :expand (bidi-current-bracket-roles classes roles)
  :enable (two-lists-induction len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; No two pairs cross.
; Two pairs are apart if one is all before the other or all inside the other.
; A pair that closes at a position C, with its opening bracket at O,
; is apart from every pair found later: such a pair closes after C,
; and its opening bracket is after C or was in the stack below O.

(local
 (define pair-apart ((x bracket-pair-p) (y bracket-pair-p))
   :returns (yes/no booleanp)
   (b* (((bracket-pair x))
        ((bracket-pair y)))
     (or (< x.close y.open)
         (< y.close x.open)
         (and (< x.open y.open)
              (< y.close x.close))
         (and (< y.open x.open)
              (< x.close y.close))))
   :hooks nil))

(local
 (define pair-apart-all ((x bracket-pair-p) (pairs bracket-pair-listp))
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (pair-apart x (car pairs))
            (pair-apart-all x (cdr pairs))))
   :hooks nil))

(local
 (define pairs-apart ((pairs bracket-pair-listp))
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (pair-apart-all (car pairs) (cdr pairs))
            (pairs-apart (cdr pairs))))
   :hooks nil))

(local
 (define stack-outside ((stack open-bracket-listp) (o natp) (c natp))
   :returns (yes/no booleanp)
   (or (endp stack)
       (and (or (< (open-bracket->position (car stack)) (nfix o))
                (< (nfix c) (open-bracket->position (car stack))))
            (stack-outside (cdr stack) o c)))
   :hooks nil))

(local
 (define pairs-outside ((pairs bracket-pair-listp) (o natp) (c natp))
   :returns (yes/no booleanp)
   (or (endp pairs)
       (and (< (nfix c) (bracket-pair->close (car pairs)))
            (or (< (bracket-pair->open (car pairs)) (nfix o))
                (< (nfix c) (bracket-pair->open (car pairs))))
            (pairs-outside (cdr pairs) o c)))
   :hooks nil))

(defrulel stack-outside-of-open-bracket-list-fix
  (equal (stack-outside (open-bracket-list-fix stack) o c)
         (stack-outside stack o c))
  :induct (list-induction stack)
  :enable (list-induction
           stack-outside
           open-bracket-list-fix))

(defrulel stack-outside-when-stack-below
  (implies (and (stack-below stack bound)
                (<= (nfix bound) (nfix o)))
           (stack-outside stack o c))
  :induct (stack-induction stack bound)
  :enable (stack-induction
           stack-below
           stack-outside
           nfix))

(defrulel open-bracket-stack-find-when-stack-outside
  (b* (((mv found position rest) (open-bracket-stack-find stack id)))
    (implies (stack-outside stack o c)
             (and (implies found
                           (or (< position (nfix o))
                               (< (nfix c) position)))
                  (stack-outside rest o c))))
  :induct (list-induction stack)
  :enable (list-induction
           open-bracket-stack-find
           stack-outside))

(defrulel pairs-outside-of-bidi-bracket-pairs-from
  (implies (and (stack-outside stack o c)
                (natp position)
                (< (nfix c) position))
           (pairs-outside
            (mv-nth 1 (bidi-bracket-pairs-from roles position stack))
            o
            c))
  :induct (bidi-bracket-pairs-from roles position stack)
  :enable (bidi-bracket-pairs-from
           pairs-outside
           stack-outside
           nfix
           natp)
  :disable open-bracket-stack-find-when-stack-outside
  :hints ('(:use (:instance open-bracket-stack-find-when-stack-outside
                            (id (bidi-bracket-role-close->id
                                 (bidi-bracket-role-fix (car roles))))))))

(defrulel pair-apart-all-when-pairs-outside
  (implies (and (pairs-outside pairs
                               (bracket-pair->open x)
                               (bracket-pair->close x))
                (< (bracket-pair->open x) (bracket-pair->close x)))
           (pair-apart-all x pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           pairs-outside
           pair-apart-all
           pair-apart
           nfix))

(defrulel stack-outside-of-rest-of-open-bracket-stack-find
  (b* (((mv found position rest) (open-bracket-stack-find stack id)))
    (implies (and (stack-below stack bound)
                  found)
             (stack-outside rest position c)))
  :use (open-bracket-stack-find-when-stack-below
        (:instance stack-outside-when-stack-below
                   (stack (mv-nth 2 (open-bracket-stack-find stack id)))
                   (bound (mv-nth 1 (open-bracket-stack-find stack id)))
                   (o (mv-nth 1 (open-bracket-stack-find stack id)))))
  :disable (open-bracket-stack-find-when-stack-below
            stack-outside-when-stack-below))

(defrulel pairs-apart-of-bidi-bracket-pairs-from
  (implies (and (stack-below stack position)
                (natp position))
           (pairs-apart
            (mv-nth 1 (bidi-bracket-pairs-from roles position stack))))
  :induct (bidi-bracket-pairs-from roles position stack)
  :enable (bidi-bracket-pairs-from
           pairs-apart
           stack-below
           nfix
           natp))

; Sorting keeps the pairs apart.

(defrulel pair-apart-all-of-bracket-pair-list-fix
  (equal (pair-apart-all x (bracket-pair-list-fix pairs))
         (pair-apart-all x pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           pair-apart-all
           pair-apart
           bracket-pair-list-fix))

(defrulel pair-apart-all-of-bracket-pair-fix
  (equal (pair-apart-all (bracket-pair-fix x) pairs)
         (pair-apart-all x pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           pair-apart-all
           pair-apart))

(defrulel pairs-apart-of-bracket-pair-list-fix
  (equal (pairs-apart (bracket-pair-list-fix pairs))
         (pairs-apart pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           pairs-apart
           bracket-pair-list-fix))

(defrulel pair-apart-all-of-bracket-pair-insert
  (equal (pair-apart-all x (bracket-pair-insert y pairs))
         (and (pair-apart x y)
              (pair-apart-all x pairs)))
  :induct (list-induction pairs)
  :enable (list-induction
           bracket-pair-insert
           pair-apart-all
           pair-apart))

(defrulel pair-apart-all-of-bracket-pairs-sort
  (equal (pair-apart-all x (bracket-pairs-sort pairs))
         (pair-apart-all x pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           bracket-pairs-sort
           pair-apart-all))

(defrulel pairs-apart-of-bracket-pair-insert
  (implies (and (pair-apart-all x pairs)
                (pairs-apart pairs))
           (pairs-apart (bracket-pair-insert x pairs)))
  :induct (list-induction pairs)
  :enable (list-induction
           bracket-pair-insert
           pairs-apart
           pair-apart-all
           pair-apart))

(defrulel pairs-apart-of-bracket-pairs-sort
  (implies (pairs-apart pairs)
           (pairs-apart (bracket-pairs-sort pairs)))
  :induct (list-induction pairs)
  :enable (list-induction
           bracket-pairs-sort
           pairs-apart))

; Sorted pairs that are apart are nested.

(defrulel bidi-pair-before-all-p-when-apart-and-open-from
  (implies (and (pair-apart-all x pairs)
                (pairs-open-from-p pairs (bracket-pair->open x))
                (pairs-roles-ok pairs all)
                (< (bracket-pair->open x) (bracket-pair->close x)))
           (bidi-pair-before-all-p x pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           pair-apart-all
           pair-apart
           pairs-open-from-p
           pairs-roles-ok
           pair-roles-ok
           bidi-pair-before-all-p
           bidi-pair-before-p
           nfix))

(defrulel bidi-pairs-nested-p-when-sorted-and-apart
  (implies (and (pairs-sorted-p pairs)
                (pairs-apart pairs)
                (pairs-roles-ok pairs all))
           (bidi-pairs-nested-p pairs))
  :induct (list-induction pairs)
  :enable (list-induction
           pairs-sorted-p
           pairs-apart
           pairs-roles-ok
           pair-roles-ok
           bidi-pairs-nested-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems of this book.

(defrule bidi-pairs-sound-p-of-bidi-bracket-pairs
  (bidi-pairs-sound-p (bidi-bracket-pairs classes roles) classes roles)
  :enable (bidi-bracket-pairs
           stack-below
           stack-opens
           pairs-roles-ok
           bidi-pairs-sound-p))

(defrule no-duplicatesp-equal-of-bidi-pair-opens-of-bidi-bracket-pairs
  (no-duplicatesp-equal (bidi-pair-opens (bidi-bracket-pairs classes roles)))
  :enable (bidi-bracket-pairs
           stack-below
           bidi-pair-opens))

; No two pairs cross, and the pairs are in the order of their opening brackets.

(defrule bidi-pairs-nested-p-of-bidi-bracket-pairs
  (bidi-pairs-nested-p (bidi-bracket-pairs classes roles))
  :enable (bidi-bracket-pairs
           stack-below
           stack-opens)
  :use (:instance bidi-pairs-nested-p-when-sorted-and-apart
                  (pairs (bracket-pairs-sort
                          (mv-nth 1 (bidi-bracket-pairs-from
                                     (bidi-current-bracket-roles classes roles)
                                     0
                                     nil))))
                  (all (bidi-current-bracket-roles classes roles)))
  :disable bidi-pairs-nested-p-when-sorted-and-apart)

(defrule bidi-bracket-pairs-of-bidi-resolve-weak-types
  (implies (bidi-roles-neutral-p roles classes)
           (equal (bidi-bracket-pairs (bidi-resolve-weak-types classes sos)
                                      roles)
                  (bidi-bracket-pairs classes roles)))
  :enable (bidi-bracket-pairs
           bidi-current-bracket-roles-when-bidi-roles-neutral-p))

; The pairs that close in the second of three parts of a sequence
; are the pairs of that part alone, moved to its position.

(defruled bidi-pairs-closing-in-of-bidi-bracket-pairs-of-append
  (b* ((classes (append classes1 classes2 classes3))
       (roles (append roles1 roles2 roles3))
       (start (len classes1))
       (end (+ (len classes1) (len classes2))))
    (implies (and (equal (len roles1) (len classes1))
                  (equal (len roles2) (len classes2))
                  (not (bidi-bracket-pairs-overflow-p classes roles))
                  (bidi-pairs-none-entering-p
                   (bidi-bracket-pairs classes roles)
                   start
                   end)
                  (natp lo)
                  (natp hi)
                  (<= start lo)
                  (<= lo hi)
                  (<= hi end))
             (and (not (bidi-bracket-pairs-overflow-p classes2 roles2))
                  (equal (bidi-pairs-closing-in
                          (bidi-bracket-pairs classes roles)
                          lo
                          hi)
                         (bidi-pairs-shift
                          (bidi-pairs-closing-in
                           (bidi-bracket-pairs classes2 roles2)
                           (- lo start)
                           (- hi start))
                          start)))))
  :enable (bidi-bracket-pairs
           bidi-bracket-pairs-overflow-p
           stack-below)
  :use (:instance bidi-bracket-pairs-from-with-stack
                  (roles (bidi-current-bracket-roles classes2 roles2))
                  (offset (len classes1))
                  (end (+ (len classes1) (len classes2)))
                  (stack (stack-after
                          (bidi-current-bracket-roles classes1 roles1)
                          0
                          nil))))
