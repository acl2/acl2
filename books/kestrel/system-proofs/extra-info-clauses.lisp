; Correctness of the ACL2 system functions that combine sets of clauses
; tagged with calls of EXTRA-INFO
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; When ACL2 builds the termination or guard proof obligations of a definition
;; with :measure-debug t or :guard-debug t, it tags each clause with literals
;; of the form (NOT (EXTRA-INFO 'X 'Y)) at its front, saying where the clause
;; came from.
;; Since EXTRA-INFO always returns T, these literals are false, so they do not
;; change the meaning of the clause.  ACL2 combines such clauses with
;; CONJOIN-CLAUSE-TO-CLAUSE-SET-EXTRA-INFO and CONJOIN-CLAUSE-SETS-EXTRA-INFO
;; (in history-management.lisp), which, when a clause differs from a member of
;; the set only in its tags, merge the tags of the clause into those of the
;; member instead of adding the clause.  CONJOIN-CLAUSE-SETS+ uses them when
;; debugging is on and CONJOIN-CLAUSE-SETS otherwise.
;;
;; This book proves that these functions make the conjunction of the clauses,
;; in terms of an evaluator that knows EXTRA-INFO, and that they merge the
;; tags as described.

(include-book "clause-sets")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "system/pseudo-termp-lemmas" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
(verify-termination extra-info-lit-p)
(verify-termination split-initial-extra-info-lits)
(verify-termination set-difference-equal-changedp)
(verify-termination conjoin-clause-to-clause-set-extra-info1)
(verify-termination conjoin-clause-to-clause-set-extra-info)
(verify-termination
  (conjoin-clause-sets-extra-info (declare (xargs :measure (if (null cl-set1) 0 (+ 1 (acl2-count cl-set1)))))))
(verify-termination conjoin-clause-sets+)

;; An evaluator that knows EXTRA-INFO and the functions that the functions in
;; clause-sets.lisp treat specially:
(defevaluator+ extra-info-eval
  if not equal iff hard-error integerp rationalp extra-info)

;; A set of clauses is true if all of its clauses are.
(defund extra-info-clause-set-true (cl-set a)
  (if (endp cl-set)
      t
    (and (extra-info-eval (disjoin (car cl-set)) a)
         (extra-info-clause-set-true (cdr cl-set) a))))

(defthm extra-info-clause-set-true-when-not-consp
  (implies (not (consp cl-set))
           (extra-info-clause-set-true cl-set a))
  :hints (("Goal" :in-theory (enable extra-info-clause-set-true))))

(defthm extra-info-clause-set-true-of-cons
  (equal (extra-info-clause-set-true (cons cl cl-set) a)
         (and (extra-info-eval (disjoin cl) a)
              (extra-info-clause-set-true cl-set a)))
  :hints (("Goal" :in-theory (enable extra-info-clause-set-true))))

(defthm extra-info-clause-set-true-of-append
  (equal (extra-info-clause-set-true (append cl-set1 cl-set2) a)
         (and (extra-info-clause-set-true cl-set1 a)
              (extra-info-clause-set-true cl-set2 a)))
  :hints (("Goal" :in-theory (enable extra-info-clause-set-true append))))

;; The result of clause-sets.lisp about conjoin-clause-sets, for this
;; evaluator:
(defthm conjoin-clause-sets-correct-for-extra-info-eval
  (implies (true-listp cl-set1)
           (iff (extra-info-clause-set-true (conjoin-clause-sets cl-set1 cl-set2) a)
                (and (extra-info-clause-set-true cl-set1 a)
                     (extra-info-clause-set-true cl-set2 a))))
  :hints (("Goal" :in-theory (e/d (extra-info-eval-of-fncall-args extra-info-clause-set-true)
                                  (extra-info-eval-of-fncall-args-back
                                   extra-info-eval-of-disjoin))
           :use (:functional-instance conjoin-clause-sets-correct
                                      (clause-set-eval extra-info-eval)
                                      (clause-set-eval-list extra-info-eval-list)
                                      (clause-set-true extra-info-clause-set-true)))))

(local (in-theory (disable conjoin-clause-sets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Tags

;; A tag, (NOT (EXTRA-INFO ...)), is false.
(defthm not-extra-info-eval-when-extra-info-lit-p
  (implies (extra-info-lit-p lit)
           (not (extra-info-eval lit a)))
  :hints (("Goal" :in-theory (enable extra-info-lit-p))))

;; Recognizes a list of tags.
(defund extra-info-lit-listp (lits)
  (if (atom lits)
      t
    (and (extra-info-lit-p (car lits))
         (extra-info-lit-listp (cdr lits)))))

(defthm all-eval-to-false-with-extra-info-eval-when-extra-info-lit-listp
  (implies (extra-info-lit-listp lits)
           (all-eval-to-false-with-extra-info-eval lits a))
  :hints (("Goal" :in-theory (enable extra-info-lit-listp
                                     all-eval-to-false-with-extra-info-eval))))

(defthm extra-info-lit-listp-when-subsetp-equal
  (implies (and (subsetp-equal x y)
                (extra-info-lit-listp y))
           (extra-info-lit-listp x))
  :hints (("Goal" :in-theory (enable extra-info-lit-listp subsetp-equal))))

(defthm extra-info-lit-p-when-member-equal-and-extra-info-lit-listp
  (implies (and (member-equal x y)
                (extra-info-lit-listp y))
           (extra-info-lit-p x))
  :hints (("Goal" :in-theory (enable extra-info-lit-listp member-equal))))

(defthm all-eval-to-false-with-extra-info-eval-of-revappend
  (equal (all-eval-to-false-with-extra-info-eval (revappend x y) a)
         (and (all-eval-to-false-with-extra-info-eval x a)
              (all-eval-to-false-with-extra-info-eval y a)))
  :hints (("Goal" :in-theory (enable revappend all-eval-to-false-with-extra-info-eval)
           :induct (revappend x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; SPLIT-INITIAL-EXTRA-INFO-LITS

;; Split-initial-extra-info-lits splits a clause into its initial tags
;; (reversed, onto HYPS-REV) and the rest of the clause.  (We write (CAR ...)
;; for the first result, because ACL2 turns (MV-NTH 0 ...) into (CAR ...).)
(defthm revappend-of-split-initial-extra-info-lits
  (equal (revappend (car (split-initial-extra-info-lits cl hyps-rev))
                    (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev)))
         (revappend hyps-rev cl))
  :hints (("Goal" :in-theory (enable split-initial-extra-info-lits))))

(defthm extra-info-lit-listp-of-car-of-split-initial-extra-info-lits
  (implies (extra-info-lit-listp hyps-rev)
           (extra-info-lit-listp (car (split-initial-extra-info-lits cl hyps-rev))))
  :hints (("Goal" :in-theory (enable split-initial-extra-info-lits extra-info-lit-listp))))

;; The rest of the clause does not start with a tag.
(defthm not-extra-info-lit-p-of-car-of-mv-nth-1-of-split-initial-extra-info-lits
  (implies (consp (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev)))
           (not (extra-info-lit-p (car (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev))))))
  :hints (("Goal" :in-theory (enable split-initial-extra-info-lits))))

(local
 (defun drop-initial-extra-info-lits (cl)
   (cond ((endp cl) cl)
         ((extra-info-lit-p (car cl))
          (drop-initial-extra-info-lits (cdr cl)))
         (t cl))))

(local
 (defthm mv-nth-1-of-split-initial-extra-info-lits-becomes-drop-initial-extra-info-lits
   (equal (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev))
          (drop-initial-extra-info-lits cl))
   :hints (("Goal" :in-theory (enable split-initial-extra-info-lits)))))

(defthm mv-nth-1-of-split-initial-extra-info-lits-irrel
  (implies (syntaxp (not (equal hyps-rev ''nil)))
           (equal (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev))
                  (mv-nth 1 (split-initial-extra-info-lits cl nil)))))

(local (in-theory (disable mv-nth-1-of-split-initial-extra-info-lits-becomes-drop-initial-extra-info-lits)))

;; The rest of the clause is true exactly when the clause is.
(defthm all-eval-to-false-with-extra-info-eval-of-mv-nth-1-of-split-initial-extra-info-lits
  (equal (all-eval-to-false-with-extra-info-eval
          (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev))
          a)
         (all-eval-to-false-with-extra-info-eval cl a))
  :hints (("Goal" :in-theory (enable split-initial-extra-info-lits))))

(local (in-theory (disable split-initial-extra-info-lits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; SET-DIFFERENCE-EQUAL-CHANGEDP

;; Set-difference-equal-changedp computes the set difference, and its first
;; result says whether the lists intersect, as its comment says.
(defthm mv-nth-0-of-set-difference-equal-changedp
  (equal (mv-nth 0 (set-difference-equal-changedp l1 l2))
         (intersectp-equal l1 l2))
  :hints (("Goal" :in-theory (enable set-difference-equal-changedp intersectp-equal))))

(local
 (defthm set-difference-equal-when-not-intersectp-equal
   (implies (and (not (intersectp-equal l1 l2))
                 (true-listp l1))
            (equal (set-difference-equal l1 l2)
                   l1))
   :hints (("Goal" :in-theory (enable set-difference-equal intersectp-equal)))))

(defthm mv-nth-1-of-set-difference-equal-changedp
  (implies (true-listp l1)
           (equal (mv-nth 1 (set-difference-equal-changedp l1 l2))
                  (set-difference-equal l1 l2)))
  :hints (("Goal" :in-theory (enable set-difference-equal-changedp set-difference-equal))))

;; (Without the TRUE-LISTP hypothesis, it still returns a subset of L1.)
(defthm subsetp-equal-of-mv-nth-1-of-set-difference-equal-changedp
  (subsetp-equal (mv-nth 1 (set-difference-equal-changedp l1 l2)) l1)
  :hints (("Goal" :in-theory (enable set-difference-equal-changedp))))

(defthm extra-info-lit-listp-of-mv-nth-1-of-set-difference-equal-changedp
  (implies (extra-info-lit-listp l1)
           (extra-info-lit-listp (mv-nth 1 (set-difference-equal-changedp l1 l2))))
  :hints (("Goal" :in-theory (enable set-difference-equal-changedp extra-info-lit-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; CONJOIN-CLAUSE-TO-CLAUSE-SET-EXTRA-INFO

(local
 (defun conjoin-clause-to-clause-set-extra-info1-induct (cl-set prefix)
   (if (endp cl-set)
       (list cl-set prefix)
     (conjoin-clause-to-clause-set-extra-info1-induct (cdr cl-set)
                                                      (append prefix (list (car cl-set)))))))

;; Conjoin-clause-to-clause-set-extra-info1 is called with CL-SET a tail of
;; CL-SET-ALL, so we prove its correctness for CL-SET-ALL of the form (APPEND
;; PREFIX CL-SET).  CL0 is CL without its tags, which are in TAGS-REV.
(local
 (defthm conjoin-clause-to-clause-set-extra-info1-correct-lemma
   (implies (and (extra-info-lit-listp tags-rev)
                 (equal (all-eval-to-false-with-extra-info-eval cl a)
                        (all-eval-to-false-with-extra-info-eval cl0 a))
                 (true-listp prefix))
            (iff (extra-info-clause-set-true
                  (conjoin-clause-to-clause-set-extra-info1 tags-rev cl0 cl cl-set
                                                            (append prefix cl-set))
                  a)
                 (and (extra-info-eval (disjoin cl) a)
                      (extra-info-clause-set-true (append prefix cl-set) a))))
   :hints (("Goal" :induct (conjoin-clause-to-clause-set-extra-info1-induct cl-set prefix)
            :in-theory (enable conjoin-clause-to-clause-set-extra-info1)))))

(local
 (defthm not-all-eval-to-false-with-extra-info-eval-when-member-equal-of-quote-t
   (implies (member-equal *t* cl)
            (not (all-eval-to-false-with-extra-info-eval cl a)))
   :hints (("Goal" :in-theory (enable all-eval-to-false-with-extra-info-eval)))))

;; Conjoining a (tagged) clause to a set of (tagged) clauses makes their
;; conjunction.
(defthm conjoin-clause-to-clause-set-extra-info-correct
  (iff (extra-info-clause-set-true (conjoin-clause-to-clause-set-extra-info cl cl-set) a)
       (and (extra-info-eval (disjoin cl) a)
            (extra-info-clause-set-true cl-set a)))
  :hints (("Goal" :in-theory (enable conjoin-clause-to-clause-set-extra-info)
           :use (:instance conjoin-clause-to-clause-set-extra-info1-correct-lemma
                           (tags-rev (mv-nth 0 (split-initial-extra-info-lits cl nil)))
                           (cl0 (mv-nth 1 (split-initial-extra-info-lits cl nil)))
                           (prefix nil)))))

(local (in-theory (disable conjoin-clause-to-clause-set-extra-info)))

;; Conjoining two sets of (tagged) clauses makes their conjunction.  The
;; function tests for the end of CL-SET1 with NULL, so CL-SET1 must be a true
;; list (see conjoin-clause-sets-extra-info-needs-true-listp in
;; extra-info-clauses-tests.lisp).
(defthm conjoin-clause-sets-extra-info-correct
  (implies (true-listp cl-set1)
           (iff (extra-info-clause-set-true (conjoin-clause-sets-extra-info cl-set1 cl-set2) a)
                (and (extra-info-clause-set-true cl-set1 a)
                     (extra-info-clause-set-true cl-set2 a))))
  :hints (("Goal" :in-theory (e/d (conjoin-clause-sets-extra-info)
                                  (extra-info-eval-of-disjoin)))))

;; Whether or not DEBUG-INFO is set, conjoin-clause-sets+ makes the
;; conjunction.
(defthm conjoin-clause-sets+-correct
  (implies (true-listp cl-set1)
           (iff (extra-info-clause-set-true (conjoin-clause-sets+ debug-info cl-set1 cl-set2) a)
                (and (extra-info-clause-set-true cl-set1 a)
                     (extra-info-clause-set-true cl-set2 a))))
  :hints (("Goal" :in-theory (enable conjoin-clause-sets+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; How the tags are merged

;;; Facts about REVERSE, REVAPPEND, and SET-DIFFERENCE-EQUAL

(local
 (defthm append-of-revappend
   (equal (append (revappend x z) y)
          (revappend x (append z y)))
   :hints (("Goal" :in-theory (enable revappend)
            :induct (revappend x z)))))

(local
 (defthm append-of-revappend-and-nil
   (equal (append (revappend x nil) y)
          (revappend x y))))

(local
 (defthm append-of-reverse
   (equal (append (reverse x) y)
          (revappend x y))
   :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm member-equal-of-revappend
   (iff (member-equal a (revappend x y))
        (or (member-equal a x)
            (member-equal a y)))
   :hints (("Goal" :in-theory (enable revappend)))))

(local
 (defthm set-difference-equal-of-revappend
   (equal (set-difference-equal (revappend x acc) y)
          (revappend (set-difference-equal x y) (set-difference-equal acc y)))
   :hints (("Goal" :in-theory (enable revappend set-difference-equal)
            :induct (revappend x acc)))))

(local
 (defthm set-difference-equal-of-reverse-arg1
   (implies (not (stringp x))
            (equal (set-difference-equal (reverse x) y)
                   (reverse (set-difference-equal x y))))
   :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm set-difference-equal-of-revappend-arg2
   (equal (set-difference-equal x (revappend y nil))
          (set-difference-equal x y))
   :hints (("Goal" :in-theory (enable set-difference-equal)))))

(local
 (defthm set-difference-equal-when-subsetp-equal
   (implies (subsetp-equal x y)
            (equal (set-difference-equal x y)
                   nil))
   :hints (("Goal" :in-theory (enable set-difference-equal subsetp-equal)))))

(local
 (defthm set-difference-equal-when-not-intersectp-equal-alt
   (implies (and (not (intersectp-equal x y))
                 (true-listp x))
            (equal (set-difference-equal x y)
                   x))
   :hints (("Goal" :in-theory (enable set-difference-equal intersectp-equal)))))

(local
 (defthm true-listp-of-car-of-split-initial-extra-info-lits
   (implies (true-listp hyps-rev)
            (true-listp (car (split-initial-extra-info-lits cl hyps-rev))))
   :hints (("Goal" :in-theory (enable split-initial-extra-info-lits)))))

(local
 (defthm not-stringp-of-car-of-split-initial-extra-info-lits
   (implies (true-listp hyps-rev)
            (not (stringp (car (split-initial-extra-info-lits cl hyps-rev)))))
   :hints (("Goal" :use true-listp-of-car-of-split-initial-extra-info-lits
            :in-theory (disable true-listp-of-car-of-split-initial-extra-info-lits)))))

;; The tags at the front of a clause, in order:
(defund extra-info-tags (cl)
  (mv-let (tags-rev body)
    (split-initial-extra-info-lits cl nil)
    (declare (ignore body))
    (reverse tags-rev)))

;; The rest of the clause:
(defund extra-info-body (cl)
  (mv-let (tags-rev body)
    (split-initial-extra-info-lits cl nil)
    (declare (ignore tags-rev))
    body))

;; A clause is its tags followed by its body.
(defthm append-of-extra-info-tags-and-extra-info-body
  (equal (append (extra-info-tags cl) (extra-info-body cl))
         cl)
  :hints (("Goal" :use (:instance revappend-of-split-initial-extra-info-lits (hyps-rev nil))
           :in-theory (e/d (extra-info-tags extra-info-body)
                           (revappend-of-split-initial-extra-info-lits)))))

;; The index of the first clause in CL-SET whose body is BODY, if any.
(defund index-of-extra-info-body (body cl-set)
  (cond ((endp cl-set) nil)
        ((equal (extra-info-body (car cl-set)) body) 0)
        (t (let ((n (index-of-extra-info-body body (cdr cl-set))))
             (and n (+ 1 n))))))

(local
 (defthm natp-of-index-of-extra-info-body
   (or (null (index-of-extra-info-body body cl-set))
       (natp (index-of-extra-info-body body cl-set)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable index-of-extra-info-body)))))

;; The generalized form, for CL-SET-ALL of the form (APPEND PREFIX CL-SET):
(local
 (defthm conjoin-clause-to-clause-set-extra-info1-merges-tags-lemma
   (implies (and (equal tags-rev (car (split-initial-extra-info-lits cl nil)))
                 (equal cl0 (mv-nth 1 (split-initial-extra-info-lits cl nil)))
                 (true-listp prefix))
            (equal (conjoin-clause-to-clause-set-extra-info1 tags-rev cl0 cl cl-set
                                                             (append prefix cl-set))
                   (let ((n (index-of-extra-info-body (extra-info-body cl) cl-set)))
                     (if n
                         (let ((cl1 (nth n cl-set)))
                           (append prefix
                                   (update-nth n
                                               (append (extra-info-tags cl1)
                                                       (set-difference-equal (extra-info-tags cl)
                                                                             (extra-info-tags cl1))
                                                       (extra-info-body cl))
                                               cl-set)))
                       (cons cl (append prefix cl-set))))))
   :hints (("Goal" :induct (conjoin-clause-to-clause-set-extra-info1-induct cl-set prefix)
            :in-theory (enable conjoin-clause-to-clause-set-extra-info1
                               index-of-extra-info-body
                               extra-info-tags
                               extra-info-body)))))

;; When CL (not the true clause) differs from a member of CL-SET only in its
;; tags, conjoin-clause-to-clause-set-extra-info replaces the first such
;; member with the clause that has the member's tags, followed by the tags of
;; CL that the member lacks, followed by the body.  Otherwise, it adds CL to
;; the front of CL-SET.
(defthm conjoin-clause-to-clause-set-extra-info-merges-tags
  (implies (not (member-equal *t* cl))
           (equal (conjoin-clause-to-clause-set-extra-info cl cl-set)
                  (let ((n (index-of-extra-info-body (extra-info-body cl) cl-set)))
                    (if n
                        (let ((cl1 (nth n cl-set)))
                          (update-nth n
                                      (append (extra-info-tags cl1)
                                              (set-difference-equal (extra-info-tags cl)
                                                                    (extra-info-tags cl1))
                                              (extra-info-body cl))
                                      cl-set))
                      (cons cl cl-set)))))
  :hints (("Goal" :in-theory (enable conjoin-clause-to-clause-set-extra-info)
           :use (:instance conjoin-clause-to-clause-set-extra-info1-merges-tags-lemma
                           (tags-rev (car (split-initial-extra-info-lits cl nil)))
                           (cl0 (mv-nth 1 (split-initial-extra-info-lits cl nil)))
                           (prefix nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Well-formedness

(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "helpers")) ; for term-listp-of-append

(local
 (defthm term-listp-of-revappend
   (implies (and (term-listp x w)
                 (term-listp y w))
            (term-listp (revappend x y) w))
   :hints (("Goal" :in-theory (enable revappend)))))

(local
 (defthm pseudo-term-listp-of-split-initial-extra-info-lits
   (implies (and (pseudo-term-listp cl)
                 (pseudo-term-listp hyps-rev))
            (and (pseudo-term-listp (car (split-initial-extra-info-lits cl hyps-rev)))
                 (pseudo-term-listp (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev)))))
   :hints (("Goal" :in-theory (enable split-initial-extra-info-lits)))))

(local
 (defthm term-listp-of-split-initial-extra-info-lits
   (implies (and (term-listp cl w)
                 (term-listp hyps-rev w))
            (and (term-listp (car (split-initial-extra-info-lits cl hyps-rev)) w)
                 (term-listp (mv-nth 1 (split-initial-extra-info-lits cl hyps-rev)) w)))
   :hints (("Goal" :in-theory (enable split-initial-extra-info-lits)))))

(local
 (defthm pseudo-term-listp-of-set-difference-equal
   (implies (pseudo-term-listp x)
            (pseudo-term-listp (set-difference-equal x y)))
   :hints (("Goal" :in-theory (enable set-difference-equal)))))

(local
 (defthm term-listp-of-set-difference-equal
   (implies (term-listp x w)
            (term-listp (set-difference-equal x y) w))
   :hints (("Goal" :in-theory (enable set-difference-equal)))))

(local
 (defthm pseudo-term-listp-of-extra-info-tags-and-extra-info-body
   (implies (pseudo-term-listp cl)
            (and (pseudo-term-listp (extra-info-tags cl))
                 (pseudo-term-listp (extra-info-body cl))))
   :hints (("Goal" :in-theory (enable extra-info-tags extra-info-body reverse)))))

(local
 (defthm term-listp-of-extra-info-tags-and-extra-info-body
   (implies (term-listp cl w)
            (and (term-listp (extra-info-tags cl) w)
                 (term-listp (extra-info-body cl) w)))
   :hints (("Goal" :in-theory (enable extra-info-tags extra-info-body reverse)))))

(local
 (defthm pseudo-term-list-listp-of-update-nth
   (implies (and (pseudo-term-list-listp l)
                 (pseudo-term-listp v)
                 (< (nfix n) (len l)))
            (pseudo-term-list-listp (update-nth n v l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm term-list-listp-of-update-nth
   (implies (and (term-list-listp l w)
                 (term-listp v w)
                 (< (nfix n) (len l)))
            (term-list-listp (update-nth n v l) w))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm pseudo-term-listp-of-nth-when-pseudo-term-list-listp
   (implies (pseudo-term-list-listp l)
            (pseudo-term-listp (nth n l)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm term-listp-of-nth-when-term-list-listp
   (implies (term-list-listp l w)
            (term-listp (nth n l) w))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm <-of-index-of-extra-info-body-and-len
   (implies (index-of-extra-info-body body cl-set)
            (< (index-of-extra-info-body body cl-set) (len cl-set)))
   :hints (("Goal" :in-theory (enable index-of-extra-info-body)))))

(defthm pseudo-term-list-listp-of-conjoin-clause-to-clause-set-extra-info
  (implies (and (pseudo-term-listp cl)
                (pseudo-term-list-listp cl-set))
           (pseudo-term-list-listp (conjoin-clause-to-clause-set-extra-info cl cl-set)))
  :hints (("Goal" :cases ((member-equal *t* cl))
           :in-theory (enable conjoin-clause-to-clause-set-extra-info))))

(defthm term-list-listp-of-conjoin-clause-to-clause-set-extra-info
  (implies (and (term-listp cl w)
                (term-list-listp cl-set w))
           (term-list-listp (conjoin-clause-to-clause-set-extra-info cl cl-set) w))
  :hints (("Goal" :cases ((member-equal *t* cl))
           :in-theory (enable conjoin-clause-to-clause-set-extra-info))))

(defthm pseudo-term-list-listp-of-conjoin-clause-sets-extra-info
  (implies (and (pseudo-term-list-listp cl-set1)
                (pseudo-term-list-listp cl-set2))
           (pseudo-term-list-listp (conjoin-clause-sets-extra-info cl-set1 cl-set2)))
  :hints (("Goal" :in-theory (enable conjoin-clause-sets-extra-info))))

(defthm term-list-listp-of-conjoin-clause-sets-extra-info
  (implies (and (term-list-listp cl-set1 w)
                (term-list-listp cl-set2 w))
           (term-list-listp (conjoin-clause-sets-extra-info cl-set1 cl-set2) w))
  :hints (("Goal" :in-theory (enable conjoin-clause-sets-extra-info))))

(defthm pseudo-term-list-listp-of-conjoin-clause-sets+
  (implies (and (pseudo-term-list-listp cl-set1)
                (pseudo-term-list-listp cl-set2))
           (pseudo-term-list-listp (conjoin-clause-sets+ debug-info cl-set1 cl-set2)))
  :hints (("Goal" :in-theory (enable conjoin-clause-sets+))))

(defthm term-list-listp-of-conjoin-clause-sets+
  (implies (and (term-list-listp cl-set1 w)
                (term-list-listp cl-set2 w))
           (term-list-listp (conjoin-clause-sets+ debug-info cl-set1 cl-set2) w))
  :hints (("Goal" :in-theory (enable conjoin-clause-sets+))))
