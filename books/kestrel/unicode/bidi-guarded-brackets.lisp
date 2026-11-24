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

; This book is a step of the proof of the theorem of the book
; bidi-guarded-theorem.lisp.  That book includes this one locally,
; through the book bidi-guarded-neutral.lisp.
; See the book bidi-guarded-theorem.lisp for the plan of the proof.
;
; This book proves facts about the bracket pairs
; that BIDI-BRACKET-PAIRS finds [UAX #9, BD16]:
;
;   in each pair, the opening bracket is before the closing bracket;
;   the opening bracket has an opening role and the class ON,
;   and the closing bracket has a closing role;
;   no two pairs have the same opening bracket;
;   the pairs found after rules W1 to W7 are those found before,
;   if every position that has a bracket role has the class ON.
;
; The definitions of this book are for the proof only.
; The guards of those that look into a list at a position
; that may be beyond its end are not verified.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definitions that the other books of the proof use.

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

(defrule bidi-bracket-pairs-of-bidi-resolve-weak-types
  (implies (bidi-roles-neutral-p roles classes)
           (equal (bidi-bracket-pairs (bidi-resolve-weak-types classes sos)
                                      roles)
                  (bidi-bracket-pairs classes roles)))
  :enable (bidi-bracket-pairs
           bidi-current-bracket-roles-when-bidi-roles-neutral-p))
