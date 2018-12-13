;;    *** Reasoning about an Instant-Runoff Voting Algorithm ***

;; Note: The license below is based on the template at:
;; http://opensource.org/licenses/BSD-3-Clause

;; Copyright (C) 2018, Shilpi Goel and Mayank Manjrekar
;; All rights reserved.

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holders nor the names of its
;;   contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Original Authors: Shilpi Goel      <shigoel@gmail.com>
;;                   Mayank Manjrekar <mankmonjre@gmail.com>

(in-package "IRV")

(include-book "irv")
(local (include-book "std/lists/set-difference"  :dir :system))
(local (include-book "std/lists/flatten"  :dir :system))
(local (include-book "std/lists/duplicity"  :dir :system))
(local (include-book "std/lists/remove-duplicates"  :dir :system))
(local (include-book "std/lists/remove"  :dir :system))
(local (include-book "std/lists/nth"  :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ----------------------------------------------------------------------

(defxdoc fairness-criteria
  :parents (instant-runoff-voting)
  :short "Some fairness theorems about @(tsee irv)"
  :long "<p>We prove that @(tsee irv) satisfies the following fairness
  criteria.</p>

 <ul>

 <li><p><b>Majority Criterion:</b> If a candidate is preferred by an absolute
   majority of voters, then that candidate must win.</p>

 @(def irv-satisfies-the-majority-criterion)
 </li>

 <li><p><b>Condorcet Loser Criteria:</b> A simple definition from <a
     href='https://en.m.wikipedia.org/wiki/Instant-runoff_voting#Satisfied_Criteria'>Wikipedia</a>
     is as follows:</p>

     <blockquote>...if a candidate would lose a head-to-head competition
     against every other candidate, then that candidate must not win the
     overall election.</blockquote>

    <p>Note that a given election may or may not have a Condorcet Loser.</p>

 @(def irv-satisfies-the-condorcet-loser-criterion)
 </li>

 <li><p><b>Majority Loser Criterion:</b> If a majority of voters prefers every
   other candidate over a given candidate, then that candidate must not win.
   Or said differently: if a candidate has a majority of last-place votes, then
   he must not win.</p>

  @(def irv-satisfies-the-majority-loser-criterion)
  </li>

 <li><p><b>Independence of Clones Criterion:</b> If a set of clones
 contains at least two non-winning candidates, then deleting one of
 the clones must not change the winner.</p>

 <p>This property depends on the definition of @('pick-candidate'),
 the tie-breaker, in our formalization.  Since the tie-breaker is a
 constrained function, we can't prove it about @(tsee irv) in the
 general case.  Here's an illustration:</p>

 <code>
  (irv '((1 3) (2))) ;; 2 is the winner.

  ;; 3 is a clone of 1 --- both are non-winning candidates.
  (clone-p 3 1 '((1 3) (2)))

  ;; Suppose the tie-breaker picked the candidate with the smallest
  ;; ID.

  ;; Now, eliminating one clone changes the winner from 2 to 3.
  (irv (eliminate-candidate 1 '((1 3) (2))))
 </code>

 <p>However, we do prove that this property holds when the winner is
 elected in the first step, i.e., if he has a majority of first-place
 votes.</p>

  @(def irv-satisfies-the-independence-of-clones-criterion-majority-winner)

 </li>

 </ul>")

;; Note that IRV fails the following fairness criteria:

;;  - Condorcet Winner Criterion: If a candidate can beat every other candidate
;;    head-to-head, he must win.

;;  - Monotonicity: If a candidate wins one election, then he should also win
;;    an election where the only difference is that a voter ranked the winner
;;    higher.  Or said differently: more first place votes should help.

;;  - Independence of Irrelevant Alternatives (IIA): Disqualifying a loser
;;    should not affect who wins.

(local (xdoc::set-default-parents fairness-criteria))

(xdoc::order-subtopics
 fairness-criteria
 (find-condorcet-loser
  all-head-to-head-competition-loser-p
  eliminate-other-candidates
  eliminate-candidates
  last-place))

;; ----------------------------------------------------------------------

;; Let us first tackle the Condorcet Loser Criterion.

(define remove-all ((x true-listp)
                    (y true-listp))
  :parents (eliminate-other-candidates)
  :short "Remove all elements in @('x') from @('y')"
  :enabled t
  (if (endp x)
      y
    (remove-all (cdr x) (remove-equal (car x) y)))

  ///

  (defthm remove-all-cons-to-remove-all-remove-equal
    (equal (remove-all (cons e x) y)
           (remove-all x (remove-equal e y))))

  (defthm remove-all-x-and-cdr-x
    (equal (remove-all x (cdr x)) nil))

  (defthm remove-all-x-x-is-nil
    (implies (true-listp x)
             (equal (remove-all x x) nil))
    :hints (("Goal"
             :in-theory (e/d () (remove-all-cons-to-remove-all-remove-equal))
             :use ((:instance remove-all-cons-to-remove-all-remove-equal
                              (e (car x))
                              (x (cdr x))
                              (y (cdr x)))))))

  (defthm remove-all-and-remove-equal-commute
    (equal (remove-all as (remove-equal e bs))
           (remove-equal e (remove-all as bs))))

  (defthm remove-all-commutes
    (equal (remove-all as (remove-all bs cs))
           (remove-all bs (remove-all as cs))))

  (defthm remove-all-returns-a-subset-of-the-list
    (subsetp-equal (remove-all x y) y)
    :hints (("Goal" :in-theory (e/d (subsetp-equal) ()))))

  (defthm remove-all-and-member-equal-1
    (implies (member-equal e a)
             (equal (member-equal e (remove-all a b)) nil)))

  (defthm remove-all-and-member-equal-2
    (implies (not (member-equal e a))
             (iff (member-equal e (remove-all a b))
                  (member-equal e b))))

  (defthm remove-all-of-nil-is-nil
    (equal (remove-all x nil) nil))

  (defthm remove-all-x-from-cons-e-y
    (equal (remove-all x (cons e y))
           (if (member-equal e x)
               (remove-all x y)
             (cons e (remove-all x y)))))

  (defthm remove-all-superset-from-subset-is-nil
    (implies (and (subsetp-equal y x)
                  (true-listp y))
             (equal (remove-all x y) nil))
    :hints (("Goal" :in-theory (e/d (subsetp-equal) ()))))

  (defthm remove-all-and-set-equiv
    ;; More general version of remove-all-x-x-is-nil.
    (implies (and (acl2::set-equiv x y)
                  (true-listp y))
             (equal (remove-all x y) nil))
    :hints (("Goal"
             :induct (remove-all x y)
             :in-theory (e/d (acl2::set-equiv)
                             ((:induction member-equal)
                              remove-all-cons-to-remove-all-remove-equal
                              remove-all-and-remove-equal-commute)))))

  (defthm nested-remove-alls-and-subsetp-equal
    (implies (subsetp-equal a c)
             (subsetp-equal a (remove-all (remove-all a b) c)))
    :hints (("Goal" :in-theory (e/d (subsetp-equal) ())))))

(define eliminate-candidates ((cids nat-listp "Candidates to remove")
                              (xs   irv-ballot-p))
  :short "Remove @('cids') from @('xs')"
  :returns (new-xs irv-ballot-p :hyp (irv-ballot-p xs))

  (if (endp cids)
      xs
    (b* ((new-xs (eliminate-candidate (car cids) xs)))
      (eliminate-candidates (cdr cids) new-xs)))

  ///

  (defthm eliminate-candidates-returns-a-subset-of-candidates
    (subsetp-equal (candidate-ids (eliminate-candidates cids xs))
                   (candidate-ids xs)))

  (defthm intersectp-equal-and-remove-equal
    (implies (intersectp-equal x (remove-equal e y))
             (intersectp-equal x y))
    :hints (("Goal" :in-theory (e/d (intersectp-equal remove-equal) ()))))

  (defthm eliminate-candidates-removes-no-candidate-when-cids-not-in-candidates
    (implies (and (irv-ballot-p xs)
                  (not (intersectp-equal cids (candidate-ids xs))))
             (equal (eliminate-candidates cids xs) xs))
    :hints (("Goal" :in-theory (e/d (intersectp-equal) ()))))

  (defthm remove-equal-commutes
    (equal (remove-equal c1 (remove-equal c2 x))
           (remove-equal c2 (remove-equal c1 x)))
    :hints (("Goal" :in-theory (e/d (remove-equal) ()))))

  (local
   (defthm remove-equal-and-consp-lemma
     (implies (and (not (consp (remove-equal c1 x)))
                   (consp (remove-equal c2 x)))
              (not (consp (remove-equal c1 (remove-equal c2 x)))))
     :hints (("Goal" :in-theory (e/d (remove-equal) ())))))

  (defthm eliminate-candidate-commutes
    (equal (eliminate-candidate c1 (eliminate-candidate c2 xs))
           (eliminate-candidate c2 (eliminate-candidate c1 xs)))
    :hints (("Goal" :in-theory (e/d (eliminate-candidate) ()))))

  (defthm eliminate-candidates-and-eliminate-candidate-commute
    (equal (eliminate-candidates cids (eliminate-candidate cid xs))
           (eliminate-candidate cid (eliminate-candidates cids xs))))

  (defthm eliminate-candidates-does-remove-candidates
    (implies (member-equal cid cids)
             (equal (member-equal cid (candidate-ids (eliminate-candidates cids xs)))
                    nil))
    :hints (("Goal" :in-theory
             (e/d (eliminate-candidates-and-eliminate-candidate-commute)
                  ()))))

  (defthm eliminate-candidates-removes-only-the-requested-candidates
    (implies (not (member-equal c cids))
             (iff (member-equal c (candidate-ids (eliminate-candidates cids xs)))
                  (member-equal c (candidate-ids xs)))))

  (defthm candidate-ids-of-eliminate-candidates
    (equal (candidate-ids (eliminate-candidates cids xs))
           (remove-all cids (candidate-ids xs))))

  (defthm eliminate-candidates-where-cids=nil-does-not-modify-xs
    (equal (eliminate-candidates nil xs) xs)
    :hints (("Goal" :in-theory (e/d (eliminate-candidates) ())))))

(define eliminate-other-candidates ((cids nat-listp "Candidates to preserve")
                                    (xs irv-ballot-p))

  :short "Remove all candidates from @('xs'), except for those in
  @('cids')"

  :prepwork
  ((defthm nat-listp-of-set-difference-equal
     (implies (nat-listp x)
              (nat-listp (set-difference-equal x y)))
     :hints (("Goal" :in-theory (e/d (set-difference-equal) ())))))

  :returns (new-xs irv-ballot-p :hyp (irv-ballot-p xs))

  (b* ((candidates-to-remove
        (remove-all cids (candidate-ids xs))))
    (eliminate-candidates candidates-to-remove xs))

  ///

  (defthm eliminate-other-candidates-returns-a-subset-of-cids
    (subsetp-equal (candidate-ids (eliminate-other-candidates cids xs))
                   cids))

  (defthm cids-is-a-subset-of-eliminate-other-candidates
    (implies (subsetp-equal cids (candidate-ids xs))
             (subsetp-equal
              cids
              (candidate-ids (eliminate-other-candidates cids xs)))))

  (defthm eliminate-other-candidates-equal-to-cids-under-set-equiv
    (implies (subsetp-equal cids (candidate-ids xs))
             (acl2::set-equiv
              (candidate-ids (eliminate-other-candidates cids xs))
              cids))
    :hints (("Goal" :in-theory (e/d (acl2::set-equiv)
                                    (eliminate-other-candidates
                                     candidate-ids)))))

  (defthm eliminate-other-candidates-does-not-modify-xs-when-cids=candidate-ids
    ;; Directly follows from remove-all-and-set-equiv.
    (implies
     (acl2::set-equiv cids (candidate-ids xs))
     (equal (eliminate-other-candidates cids xs) xs))
    :hints (("Goal" :do-not-induct t))))

(define head-to-head-competition-loser-p
  ((l natp "Possible loser")
   (c natp "The other candidate in @('xs')")
   (xs irv-ballot-p))
  :parents (all-head-to-head-competition-loser-p)
  :short "Check if @('l') will lose in a head-to-head competition against
  @('c')"
  :guard (and (member-equal l (candidate-ids xs))
              (member-equal c (candidate-ids xs))
              (not (equal l c)))

  (b* ((xs-pairwise (eliminate-other-candidates (list l c) xs)))
    (equal (irv xs-pairwise) c)))

(define all-head-to-head-competition-loser-p
  ((l    natp      "Possible loser")
   (cids nat-listp "All candidates in @('xs'), except @('l')")
   (xs   irv-ballot-p))
  :short "Check if @('l') will lose in a head-to-head competition against
  every candidate in @('cids')"
  :guard (and (member-equal l (candidate-ids xs))
              (not (member-equal l cids))
              (subsetp-equal cids (candidate-ids xs)))

  (if (endp cids)
      t
    (if (member-equal l cids)
        nil
      (if (head-to-head-competition-loser-p l (car cids) xs)
          (all-head-to-head-competition-loser-p l (cdr cids) xs)
        nil))))

(define find-condorcet-loser-aux
  ((loser-cids nat-listp "Candidates in @('xs') to consider as losers")
   (cids       nat-listp "All candidates in @('xs')")
   (xs         irv-ballot-p))
  :parents (find-condorcet-loser)
  :measure (len loser-cids)
  :guard (and (acl2::set-equiv cids (candidate-ids xs))
              (subsetp-equal loser-cids cids))

  (if (endp loser-cids)
      nil
    (if (all-head-to-head-competition-loser-p
         (car loser-cids)
         (remove-equal (car loser-cids) cids)
         xs)
        (car loser-cids)
      (find-condorcet-loser-aux (cdr loser-cids) cids xs))))

(define find-condorcet-loser ((xs irv-ballot-p))
  :short "Returns a condorcet loser in @('xs'), if any"
  (find-condorcet-loser-aux
   (candidate-ids xs) (candidate-ids xs) xs))

(assert-event
 (equal
  (find-condorcet-loser
   ;; "Approval Voting" Example
   ;; https://en.wikipedia.org/wiki/Condorcet_loser_criterion
   '((1 2 4 3)
     (2 3 4 1)
     (3 1 4 2)))
  4))

(assert-event
 (equal
  (find-condorcet-loser
   ;; "Majority Judgment" Example
   ;; https://en.wikipedia.org/wiki/Condorcet_loser_criterion
   '((1 3 2)
     (2 3 1)
     (1 2 3)))
  3))

(assert-event
 ;; There is no condorcet loser here (Condorcet's Paradox --- even if each
 ;; voter's preference ordering is transitive, the majority ordering may
 ;; not be transitive).
 ;; https://plato.stanford.edu/entries/voting-methods/#2
 (equal
  (find-condorcet-loser
   '((1 2 3)
     (2 3 1)
     (3 1 2)))
  nil))

(assert-event
 ;; There is no condorcet loser here.
 (equal
  (find-condorcet-loser
   '((1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (1 2 3 4)
     (2 3 4 1)
     (2 3 4 1)
     (2 3 4 1)
     (2 3 4 1)
     (2 3 4 1)
     (2 3 4 1)
     (2 3 4 1)
     (3 4 1 2)
     (3 4 1 2)
     (3 4 1 2)
     (3 4 1 2)
     (3 4 1 2)
     (4 3 2 1)
     (4 3 2 1)
     (4 3 2 1)))
  nil))

;; Our top-level Condorcet Loser Criteria theorem will look something like the
;; following:

;; (defthm all-head-to-head-competition-loser-cant-be-an-irv-winner
;;   (implies (and (all-head-to-head-competition-loser-p l cids xs)
;;                 (acl2::set-equiv (cons l cids) (candidate-ids xs))
;;                 (consp cids)
;;                 (irv-ballot-p xs))
;;            (not (equal (irv xs) l))))

;; Let us first reason about the case when (irv xs) is a candidate who won by a
;; majority of first-preference votes in the first round itself.  Note that
;; such a candidate satisfies the Condorcet Winner Criterion (which says that
;; if a candidate wins a head-to-head competition against every other
;; candidate, then that candidate must win the overall election), which is not
;; true for IRV in general.

;;;;; Begin proof of
;;;;; first-preference-majority-winner-cannot-be-condorcet-loser:

;; First, some lower and upper bounds on the number of first
;; preference votes obtained by the majority winner, i.e.,
;; (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))

(defthm max-nats-of-count-alist-when-not-consp-choice-list
  (implies (not (consp choice-list))
           (equal (max-nats (strip-cdrs (create-count-alist cids choice-list)))
                  0))
  :hints (("Goal" :in-theory (e/d (create-count-alist
                                   max-nats)
                                  ()))))

(defthm upper-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
  (<= (max-nats (strip-cdrs (create-count-alist x y))) (len y))
  :hints (("Goal"
           :induct (create-count-alist x y)
           :in-theory (e/d (create-count-alist
                            max-nats len)
                           ())))
  :rule-classes (:rewrite :linear))

(defthm upper-bound-of-max-nats-of-strip-cdrs-of-create-nth-choice-count-alist
  (implies (irv-ballot-p xs)
           (<=
            (max-nats
             (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))
            (number-of-voters xs)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (number-of-voters
                            create-nth-choice-count-alist)
                           ())))
  :rule-classes (:rewrite :linear))

(defthm lower-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
  ;; max-nats has got to be greater than or equal to the total count of any
  ;; element in x.
  (implies (member-equal e x)
           (<= (acl2::duplicity e y)
               (max-nats (strip-cdrs (create-count-alist x y)))))
  :hints (("Goal"
           :induct (create-count-alist x y)
           :in-theory (e/d (create-count-alist
                            max-nats len)
                           ())))
  :rule-classes (:rewrite :linear))

(defthm lower-bound-of-max-nats-of-strip-cdrs-of-create-nth-choice-count-alist
  (implies (member-equal e cids)
           (<= (acl2::duplicity e (make-nth-choice-list 0 xs))
               (max-nats
                (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (number-of-voters
                            create-nth-choice-count-alist)
                           ())))
  :rule-classes (:rewrite :linear))

;; Now, we prove that the number of first preference votes obtained by
;; a candidate (expressed using acl2::duplicity) cannot decrease if
;; some other candidate is deleted from the ballot.

(defthm lower-bound-of-duplicity-of-choice-list-after-eliminate-candidate
  (implies (not (equal e id))
           (<=
            (acl2::duplicity e (make-nth-choice-list 0 xs))
            (acl2::duplicity e (make-nth-choice-list 0 (eliminate-candidate id xs)))))
  :hints (("Goal" :in-theory (e/d (eliminate-candidate
                                   make-nth-choice-list)
                                  ())))
  :rule-classes (:linear :rewrite))

;; The above lemma allows us to infer that if a candidate e gets a
;; majority number of first preference votes, then the same candidate
;; e will retain his majority after some other candidate is
;; eliminated.  Note that after a candidate's elimination, the total
;; number of voters being considered may change (e.g., if a voter gave
;; only one preference --- to the eliminated candidate); thus, the
;; notion of majority may be different.  See
;; number-of-voters-after-eliminate-candidate.

(defthm majority-in-terms-of-duplicity-and-choice-list-after-eliminate-candidate
  (implies
   (and (< (majority (number-of-voters xs))
           (acl2::duplicity e (make-nth-choice-list 0 xs)))
        (not (equal id e))
        (irv-ballot-p xs))
   (< (majority (number-of-voters (eliminate-candidate id xs)))
      (acl2::duplicity e (make-nth-choice-list 0 (eliminate-candidate id xs)))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (e/d ()
         (lower-bound-of-duplicity-of-choice-list-after-eliminate-candidate
          majority-may-increase-if-num-voters-increase))
    :use
    ((:instance lower-bound-of-duplicity-of-choice-list-after-eliminate-candidate)
     (:instance majority-may-increase-if-num-voters-increase
                (m (number-of-voters (eliminate-candidate id xs)))
                (n (number-of-voters xs))))))
  :rule-classes (:rewrite :linear))

;; Since first-choice-of-majority-p is in terms of max-nats, we need
;; to prove that the votes obtained by the candidate e in the above
;; lemma are indeed the maximum first-preference votes, i.e.,
;; (acl2::duplicity e (make-nth-choice-list 0 xs)) ==
;; (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs))).

;; In order to do this, we define a helper function sum-nats that
;; returns the sum of elements in a nat-listp, and prove that a member
;; of a nat-listp lst is greater than majority(sum-nats(lst)) is the
;; largest element in lst and is unique --- see
;; sum-nats->-majority-is-unique-1 and
;; sum-nats->-majority-is-unique-2.  We then arrive at our required
;; theorem, duplicity-of-e-higher-than-majority-is-max-nats.

(local
 (defthm subset-member-cdr-lemma
   (implies (and (not (subsetp-equal y (cdr x)))
                 (subsetp-equal y x))
            (member-equal (car x) y))
   :hints (("Goal" :in-theory (e/d (subsetp-equal member-equal) ())))))

(define sum-nats ((lst nat-listp))
  :enabled t
  :returns (sum natp :hyp (nat-listp lst)
                :rule-classes (:type-prescription :rewrite))
  (if (endp lst)
      0
    (+ (car lst) (sum-nats (cdr lst))))

  ///

  (defthm sum-nats-lower-bound
    (implies (and (member-equal e lst)
                  (nat-listp lst))
             (<= e (sum-nats lst)))
    :rule-classes :linear)

  (encapsulate
    ()
    (local (include-book "arithmetic-5/top" :dir :system))

    (defthmd majority-+-lemma
      (implies (and (<= j (majority x))
                    (natp i)
                    (natp j)
                    (natp x))
               (<= j (majority (+ i x))))
      :hints (("Goal" :in-theory (e/d (majority) ())))
      :rule-classes (:linear :rewrite))

    (defthmd majority-lower-bound-lemma
      (implies (and (natp x)
                    (natp j)
                    (<= j x))
               (<= j (majority (+ j x))))
      :hints (("Goal" :in-theory (e/d (majority)
                                      (acl2::functional-commutativity-of-minus-*-left)))))

    (defthm sum-nats->-majority-is-unique-1
      (implies (and (< (majority (sum-nats x)) j)
                    (member-equal j x)
                    (member-equal i x)
                    ;; (not (equal i j))
                    (nat-listp x)
                    (natp j))
               ;; (< i j)
               (<= i j))
      :hints (("Goal"
               :in-theory (e/d (majority sum-nats)
                               ())))
      :rule-classes nil))

  (local
   (defthmd duplicity-member-lemma
     (implies (posp (acl2::duplicity e x))
              (member-equal e x))))

  (defthmd sum-nats-majority-duplicity=1
    (implies (and (< (majority (sum-nats lst)) e)
                  (member-equal e lst)
                  (nat-listp lst))
             (equal (acl2::duplicity e lst) 1))
    :hints (("Goal"
             :induct (cons (acl2::duplicity e lst)
                           (cons (sum-nats lst) (member-equal e lst)))
             :in-theory (e/d (acl2::duplicity)
                             ()))
            (if (and (consp id)
                     (equal (car id) '(0 1)))
                ;; Subgoals in top-level induction
                '(:in-theory
                  (e/d (member-of-nat-listp) ())
                  :use ((:instance majority-+-lemma
                                   (x (sum-nats (cdr lst)))
                                   (i (car lst))
                                   (j e))
                        (:instance duplicity-member-lemma
                                   (e (car lst))
                                   (x (cdr lst)))
                        (:instance majority-lower-bound-lemma
                                   (x (sum-nats (cdr lst)))
                                   (j (car lst)))))
              nil)))

  (defthm sum-nats->-majority-is-unique-2
    (implies (and (< (majority (sum-nats x)) j)
                  (< (majority (sum-nats x)) i)
                  (member-equal j x)
                  (member-equal i x)
                  (nat-listp x))
             (equal i j))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance sum-nats->-majority-is-unique-1
                              (j i) (i j) (x x))
                   (:instance sum-nats->-majority-is-unique-1
                              (j j) (i i) (x x))
                   (:instance member-of-nat-listp
                              (e i) (lst x))
                   (:instance member-of-nat-listp
                              (e j) (lst x)))))
    :rule-classes nil)

  ;; Now proving:
  ;; (sum-nats (strip-cdrs (create-count-alist cids (make-nth-choice-list 0 xs))))
  ;; ==
  ;; (number-of-voters xs)

  (defthm sum-nats-of-count-alist-of-empty-choice-list
    (equal (sum-nats (strip-cdrs (create-count-alist cids nil))) 0)
    :hints (("Goal" :in-theory (e/d (create-count-alist) ()))))

  (defthm sum-nats-cons-e-x=sum-nats-x-if-e=0
    (implies (natp e)
             (iff (equal (sum-nats (cons e x))
                         (sum-nats x))
                  (equal e 0))))

  (local
   (defthm sum-nats-count-alist-if-e-not-in-x-then-e-can-be-removed-from-y
     (implies (not (member-equal e x))
              (equal
               (sum-nats (strip-cdrs (create-count-alist x (remove-equal e y))))
               (sum-nats (strip-cdrs (create-count-alist x y)))))
     :hints (("Goal" :in-theory (e/d (create-count-alist) ())))))

  (local
   (defun sum-nats-count-alist-ind-hint (x y)
     (if (endp x)
         y
       (if (member-equal (car x) y)
           (+ (acl2::duplicity (car x) y)
              (sum-nats-count-alist-ind-hint (cdr x) (remove-equal (car x) y)))
         (sum-nats-count-alist-ind-hint (cdr x) y)))))

  (defthm sum-nats-of-strip-cdrs-of-create-count-alist-is-len-y
    (implies (and (no-duplicatesp-equal x)
                  (subsetp-equal y x))
             (equal (sum-nats (strip-cdrs (create-count-alist x y)))
                    (len y)))
    :hints (("Goal"
             :induct (sum-nats-count-alist-ind-hint x y)
             :in-theory (e/d (create-count-alist) ()))))

  (defthm sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters
    (implies (and (irv-ballot-p xs)
                  (no-duplicatesp-equal cids)
                  (acl2::set-equiv cids (candidate-ids xs)))
             (equal (sum-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))
                    (number-of-voters xs)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (create-nth-choice-count-alist acl2::set-equiv)
                             ())))))

(defthm duplicity-of-e-higher-than-majority-is-max-nats
  (implies
   (and (< (majority (number-of-voters xs))
           (acl2::duplicity e (make-nth-choice-list 0 xs)))
        (member e cids)
        (no-duplicatesp-equal cids)
        (acl2::set-equiv cids (candidate-ids xs))
        (irv-ballot-p xs))
   (equal (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))
          (acl2::duplicity e (make-nth-choice-list 0 xs))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (create-nth-choice-count-alist)
                           (duplicity-is-a-member-of-strip-cdrs-count-alist
                            max-nats-returns-a-member-of-input
                            sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters))
           :use ((:instance duplicity-is-a-member-of-strip-cdrs-count-alist
                            (x cids)
                            (y (make-nth-choice-list 0 xs)))
                 (:instance max-nats-returns-a-member-of-input
                            (x (strip-cdrs (create-nth-choice-count-alist 0 cids xs))))
                 (:instance sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters)
                 (:instance sum-nats->-majority-is-unique-2
                            (x (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))
                            (j (acl2::duplicity e (make-nth-choice-list 0 xs)))
                            (i (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))))))))

;;  We want to replace the
;; (< (majority ...) (acl2::duplicity ...)
;; term in the lemma above with
;; (< (majority ...) (max-nats ...).
;; So we prove
;; max-nats-greater-than-majority-implies-max-nats-equal-to-duplicity
;; below.

(local
 (defthmd e==car-x-if-e-in-y-but-not-in-cdr-x-where-y-is-subset-of-x
   (implies (and
             (not (member-equal e (cdr x)))
             (member-equal e y)
             (subsetp-equal y x))
            (equal (car x) e))))

(defthm car-of-assoc-of-key-is-the-key
  (implies (member-equal e (strip-cars x))
           (equal (car (assoc-equal e x)) e)))

(defthmd car-rassoc-c-a==e-implies-cdr-assoc-e-a==c
  (implies (and (equal (car (rassoc-equal count alst)) e)
                (no-duplicatesp-equal (strip-cars alst))
                e)
           (equal (cdr (assoc-equal e alst)) count)))

(defthm rassoc-and-assoc-lemma-in-terms-of-count-alist
  (implies (and (equal (car (rassoc-equal count (create-count-alist x y))) e)
                (member-equal e x)
                (nat-listp x)
                (no-duplicatesp-equal x))
           (equal (cdr (assoc-equal e (create-count-alist x y))) count))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance car-rassoc-c-a==e-implies-cdr-assoc-e-a==c
                            (e e)
                            (count count)
                            (alst (create-count-alist x y)))))))

(local
 (defthm non-nil-val-is-a-member-of-strip-cdrs-alistp
   (implies (and (equal (cdr (assoc-equal key alst)) val) val)
            (member-equal val (strip-cdrs alst)))))

(defthm key-for-a-unique-val-in-alist
  (implies (and (equal (acl2::duplicity val (strip-cdrs alst)) 1)
                (equal (cdr (assoc-equal key alst)) val)
                (nat-listp (strip-cdrs alst))
                (alistp alst))
           (equal (car (rassoc-equal val alst)) key))
  :hints (("Goal" :in-theory (e/d (acl2::duplicity) ()))))

(defthm unique-duplicity-e-y-is-the-val-of-only-e-in-count-alist
  (implies (and (< (majority (sum-nats (strip-cdrs (create-count-alist x y))))
                   (acl2::duplicity e y))
                (member-equal e x)
                (nat-listp x))
           (equal (car (rassoc-equal (acl2::duplicity e y) (create-count-alist x y)))
                  e))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance sum-nats-majority-duplicity=1
                            (e (acl2::duplicity e y))
                            (lst (strip-cdrs (create-count-alist x y))))
                 (:instance duplicity-is-a-member-of-strip-cdrs-count-alist)
                 (:instance duplicity-e-y-is-the-val-of-e-in-count-alist))
           :in-theory (e/d (create-count-alist)
                           (duplicity-e-y-is-the-val-of-e-in-count-alist
                            sum-nats-majority-duplicity=1
                            duplicity-is-a-member-of-strip-cdrs-count-alist
                            sum-nats-of-strip-cdrs-of-create-count-alist-is-len-y)))))

(defthmd relating-rassoc-equal-in-count-alist-and-duplicity-helper
  ;; Equating two different ways of saying 'the number of times "e"
  ;; occurs in "y" is equal to "count".'
  (implies (and
            (equal (car (rassoc-equal count (create-count-alist x y))) e)
            (member-equal e x)
            (natp e)
            (nat-listp x)
            (nat-listp y)
            (subsetp-equal y x)
            (no-duplicatesp-equal x))
           (equal (acl2::duplicity e y) count))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rassoc-and-assoc-lemma-in-terms-of-count-alist))
           :in-theory (e/d ()
                           (rassoc-and-assoc-lemma-in-terms-of-count-alist
                            key-for-a-unique-val-in-alist
                            unique-duplicity-e-y-is-the-val-of-only-e-in-count-alist)))))

(defthm relating-rassoc-equal-in-count-alist-and-duplicity
  (implies (and
            (member-equal (car (rassoc-equal count (create-count-alist x y))) x)
            (natp (car (rassoc-equal count (create-count-alist x y))))
            (nat-listp x)
            (nat-listp y)
            (subsetp-equal y x)
            (no-duplicatesp-equal x))
           (equal (acl2::duplicity (car (rassoc-equal count (create-count-alist x y))) y)
                  count))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance relating-rassoc-equal-in-count-alist-and-duplicity-helper
                            (e (car (rassoc-equal count (create-count-alist x y)))))))))

(defthm relating-majority-of-sum-nats-with-duplicity
  (implies
   (and
    (< (majority (sum-nats (strip-cdrs (create-count-alist x y)))) count)
    (member-equal count (strip-cdrs (create-count-alist x y)))
    (member-equal (car (rassoc-equal count (create-count-alist x y))) x)
    (natp (car (rassoc-equal count (create-count-alist x y))))
    (subsetp-equal y x)
    (no-duplicatesp-equal x)
    (nat-listp x)
    (nat-listp y)
    (natp count))
   (equal (acl2::duplicity
           (car (rassoc-equal count (create-count-alist x y))) y)
          count))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (e==car-x-if-e-in-y-but-not-in-cdr-x-where-y-is-subset-of-x
                            create-count-alist)
                           (sum-nats-majority-duplicity=1))
           :use ((:instance sum-nats-majority-duplicity=1
                            (lst (strip-cdrs (create-count-alist x y)))
                            (e count))))))

(defthmd max-nats-greater-than-majority-implies-max-nats-equal-to-duplicity
  (implies
   (and
    (< (majority (number-of-voters xs))
       (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs))))
    (no-duplicatesp-equal cids)
    (acl2::set-equiv cids (candidate-ids xs))
    (nat-listp cids)
    (irv-ballot-p xs))
   (equal (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))
          (acl2::duplicity
           (car
            (rassoc-equal
             (max-nats (strip-cdrs (create-nth-choice-count-alist 0 cids xs)))
             (create-nth-choice-count-alist 0 cids xs)))
           (make-nth-choice-list 0 xs))))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance relating-majority-of-sum-nats-with-duplicity
                     (count (max-nats (strip-cdrs
                                       (create-nth-choice-count-alist 0 cids xs))))
                     (x cids)
                     (y (make-nth-choice-list 0 xs)))
          (:instance sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters)
          (:instance max-nats-returns-a-member-of-input
                     (x (strip-cdrs (create-count-alist cids (make-nth-choice-list 0 xs)))))
          (:instance rassoc-equal-returns-a-member-of-keys
                     (val (max-nats
                           (strip-cdrs (create-count-alist
                                        cids
                                        (make-nth-choice-list 0 xs)))))
                     (alst (create-count-alist cids (make-nth-choice-list 0 xs)))))
    :in-theory
    (e/d (create-nth-choice-count-alist
          acl2::set-equiv)
         (relating-majority-of-sum-nats-with-duplicity
          duplicity-is-a-member-of-strip-cdrs-count-alist
          max-nats-returns-a-member-of-input
          sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters
          max-nats-returns-a-member-of-input
          rassoc-equal-returns-a-member-of-keys)))))

;; Note that both the theorems
;; duplicity-of-e-higher-than-majority-is-max-nats and
;; max-nats-greater-than-majority-implies-max-nats-equal-to-duplicity
;; rewrite a (max-nats ...) term to (acl2::duplicity ...) term --- the
;; difference is that the former is useful when the (< (majority ...)
;; (acl2::duplicity ...)) term is in the hypotheses, and the latter
;; when the (< (majority ...) (max-nats ...)) term is in the
;; hypotheses.

;; Now, in first-choice-of-majority-p-in-terms-of-candidate-duplicity
;; below, we prove that e is the majority winner iff the number of
;; times e occurs in first-preference list is greater than the
;; majority (using acl2::duplicity).  So, we basically removed
;; (max-nats ...) from the statement --- that's "inside"
;; first-choice-of-majority-p.

(local
 (defthmd first-choice-of-majority-p-in-terms-of-candidate-duplicity-1
   (implies
    (and (< (majority (number-of-voters xs))
            (acl2::duplicity e (make-nth-choice-list 0 xs)))
         (member-equal e cids)
         (no-duplicatesp-equal cids)
         (nat-listp cids)
         (acl2::set-equiv cids (candidate-ids xs))
         (irv-ballot-p xs))
    (equal (first-choice-of-majority-p cids xs) e))
   :hints
   (("Goal"
     :do-not-induct t
     :use ((:instance sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters)
           (:instance duplicity-of-e-higher-than-majority-is-max-nats)
           (:instance unique-duplicity-e-y-is-the-val-of-only-e-in-count-alist
                      (x cids)
                      (y (make-nth-choice-list 0 xs))
                      (e e)))
     :in-theory (e/d (first-choice-of-majority-p
                      create-nth-choice-count-alist)
                     (sum-nats-strip-cdrs-create-nth-choice-count-alist==number-of-voters
                      unique-duplicity-e-y-is-the-val-of-only-e-in-count-alist
                      duplicity-of-e-higher-than-majority-is-max-nats))))))

(local
 (defthmd first-choice-of-majority-p-in-terms-of-candidate-duplicity-2
   (implies
    (and (equal (first-choice-of-majority-p cids xs) e)
         (member-equal e cids)
         (no-duplicatesp-equal cids)
         (acl2::set-equiv cids (candidate-ids xs))
         (nat-listp cids)
         (irv-ballot-p xs))
    (< (majority (number-of-voters xs))
       (acl2::duplicity e (make-nth-choice-list 0 xs))))
   :hints
   (("Goal"
     :do-not-induct t
     :in-theory (e/d (first-choice-of-majority-p
                      create-nth-choice-count-alist
                      acl2::set-equiv)
                     ())))))

(defthm first-choice-of-majority-p-in-terms-of-candidate-duplicity
  (implies
   (and (member-equal e cids)
        (no-duplicatesp-equal cids)
        (acl2::set-equiv cids (candidate-ids xs))
        (nat-listp cids)
        (irv-ballot-p xs))
   (iff (equal (first-choice-of-majority-p cids xs) e)
        (< (majority (number-of-voters xs))
           (acl2::duplicity e (make-nth-choice-list 0 xs)))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (first-choice-of-majority-p-in-terms-of-candidate-duplicity-1
                     first-choice-of-majority-p-in-terms-of-candidate-duplicity-2)
                    ()))))

(defthm sum-of-duplicities-upper-bound
  (implies (not (equal e1 e2))
           (<= (+ (acl2::duplicity e1 x)
                  (acl2::duplicity e2 x))
               (len x)))
  :hints (("Goal" :in-theory (e/d (acl2::duplicity) ())))
  :rule-classes :linear)

(defthm duplicity->-majority-is-unique
  (implies (and (< (majority (len y)) (acl2::duplicity e y))
                (not (equal id e)))
           (< (acl2::duplicity id y) (acl2::duplicity e y)))
  :hints (("Goal" :in-theory (e/d (majority len acl2::duplicity)
                                  ())))
  :rule-classes :linear)

(defthmd duplicity->-majority-is-unique-stronger
  (implies (< (majority (len y)) (acl2::duplicity e y))
           (iff (equal id e)
                (equal (acl2::duplicity id y) (acl2::duplicity e y)))))

;; We finally arrive at our key lemma:
;; first-choice-of-majority-p-same-after-eliminate-candidate.

(local
 (defthm first-choice-of-majority-p-same-after-eliminate-candidate-helper-1
   (implies
    (and
     (no-duplicatesp-equal cids)
     (< 1 (len cids)))
    (not (subsetp-equal cids (list id))))
   :hints (("Goal" :in-theory (e/d (subsetp-equal)
                                   ())))))

(local
 (defthm first-choice-of-majority-p-is-in-cids
   (implies (natp (first-choice-of-majority-p cids xs))
            (member-equal (first-choice-of-majority-p cids xs)
                          cids))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance member-equal-of-car-of-rassoc-equal
                             (val (max-nats
                                   (strip-cdrs (create-count-alist
                                                cids
                                                (make-nth-choice-list 0 xs)))))
                             (alst (create-count-alist
                                    cids
                                    (make-nth-choice-list 0 xs)))))
            :in-theory (e/d (first-choice-of-majority-p
                             create-nth-choice-count-alist)
                            (member-equal-of-car-of-rassoc-equal))))))

(defthm natp-of-first-choice-of-majority-p-after-eliminate-candidate
  (implies
   (and (equal e (first-choice-of-majority-p cids xs))
        (natp e)
        (not (equal id e))
        (acl2::set-equiv cids (candidate-ids xs))
        (no-duplicatesp-equal cids)
        (nat-listp cids)
        (irv-ballot-p xs))
   (natp (first-choice-of-majority-p
          (remove-equal id cids)
          (eliminate-candidate id xs))))
  :hints (("Goal"
           :do-not-induct t
           :use
           ((:instance first-choice-of-majority-p-is-in-cids)
            (:instance max-nats-greater-than-majority-implies-max-nats-equal-to-duplicity)
            (:instance majority-may-increase-if-num-voters-increase
                       (m (number-of-voters (eliminate-candidate id xs)))
                       (n (number-of-voters xs)))
            (:instance lower-bound-of-duplicity-of-choice-list-after-eliminate-candidate
                       (e (first-choice-of-majority-p cids xs))
                       (id id)
                       (xs xs))
            (:instance duplicity-of-e-higher-than-majority-is-max-nats
                       (e (first-choice-of-majority-p cids xs))
                       (cids (remove-equal id cids))
                       (xs (eliminate-candidate id xs))))
           :in-theory
           (e/d (create-nth-choice-count-alist
                 first-choice-of-majority-p)
                (first-choice-of-majority-p-is-in-cids
                 not
                 no-duplicatesp-equal
                 member-equal
                 irv-ballot-p
                 majority-may-increase-if-num-voters-increase
                 lower-bound-of-duplicity-of-choice-list-after-eliminate-candidate
                 duplicity-of-e-higher-than-majority-is-max-nats
                 first-choice-of-majority-p-is-in-cids)))))

(defthm first-choice-of-majority-p-same-after-eliminate-candidate
  (implies
   (and (acl2::set-equiv cids (candidate-ids xs))
        (no-duplicatesp-equal cids)
        (nat-listp cids)
        (not (equal id (first-choice-of-majority-p cids xs)))
        (natp (first-choice-of-majority-p cids xs))
        (irv-ballot-p xs))
   (equal
    (first-choice-of-majority-p
     (remove-equal id cids)
     (eliminate-candidate id xs))
    (first-choice-of-majority-p cids xs)))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance first-choice-of-majority-p-in-terms-of-candidate-duplicity
                     ;; Introduces the following term:
                     ;; (< (majority (number-of-voters xs))
                     ;;    (acl2::duplicity (first-choice-of-majority-p cids xs) (make-nth-choice-list 0 xs)))
                     (e (first-choice-of-majority-p cids xs)))
          (:instance first-choice-of-majority-p-in-terms-of-candidate-duplicity
                     ;; Introduces the following term:
                     ;; (< (majority (number-of-voters (eliminate-candidate id xs)))
                     ;;    (acl2::duplicity
                     ;;     (first-choice-of-majority-p
                     ;;      (remove-equal id cids)
                     ;;      (eliminate-candidate id xs))
                     ;;     (make-nth-choice-list 0 (eliminate-candidate id xs))))
                     (e (first-choice-of-majority-p
                         (remove-equal id cids)
                         (eliminate-candidate id xs)))
                     (cids (remove-equal id cids))
                     (xs (eliminate-candidate id xs)))
          ;; From
          ;; majority-in-terms-of-duplicity-and-choice-list-after-eliminate-candidate,
          ;; we know that the term introduced by the first use hint implies the following:
          ;; (< (majority (number-of-voters (eliminate-candidate id xs)))
          ;;    (acl2::duplicity (first-choice-of-majority-p cids xs)
          ;;                     (make-nth-choice-list 0 (eliminate-candidate id xs))))
          ;; However, from duplicity->-majority-is-unique, we know
          ;; that the above term is equal to the term introduced by
          ;; the second use hint.
          (:instance first-choice-of-majority-p-is-in-cids)
          (:instance first-choice-of-majority-p-is-in-cids
                     (cids (remove-equal id cids))
                     (xs (eliminate-candidate id xs))))
    :in-theory (e/d (member-of-nat-listp)
                    (first-choice-of-majority-p-in-terms-of-candidate-duplicity
                     first-choice-of-majority-p-is-in-cids
                     irv-ballot-p)))))

(defthm first-choice-of-majority-p-same-after-eliminate-candidates
  ;; Generalization of
  ;; first-choice-of-majority-p-same-after-eliminate-candidate to more
  ;; than 1 candidate's elimination.
  (implies (and (equal m (first-choice-of-majority-p (candidate-ids xs) xs))
                (not (member-equal m cids))
                (natp m)
                (irv-ballot-p xs))
           (equal (first-choice-of-majority-p
                   (remove-all cids (candidate-ids xs))
                   (eliminate-candidates cids xs))
                  m))
  :hints (("Goal" :in-theory (e/d (eliminate-candidates) ()))))

(defthmd first-preference-majority-winner-cannot-be-condorcet-loser-helper
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (equal m (first-choice-of-majority-p (candidate-ids xs) xs))
                (acl2::set-equiv (cons l cids) (candidate-ids xs))
                (no-duplicatesp-equal (cons l cids))
                (nat-listp cids) (<= 1 (len cids))
                (natp m)
                (irv-ballot-p xs))
           (not (equal m l)))
  :hints (("Goal"
           :do-not-induct t
           :expand (all-head-to-head-competition-loser-p
                    (first-choice-of-majority-p (candidate-ids xs) xs)
                    cids xs)
           :in-theory (e/d (irv
                            all-head-to-head-competition-loser-p
                            head-to-head-competition-loser-p
                            eliminate-other-candidates
                            eliminate-candidates)
                           ()))))

(defthm first-preference-majority-winner-cannot-be-condorcet-loser
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (equal m (irv xs))
                (natp (first-choice-of-majority-p (candidate-ids xs) xs))
                (acl2::set-equiv (cons l cids) (candidate-ids xs))
                (no-duplicatesp-equal (cons l cids))
                (nat-listp cids) (<= 1 (len cids))
                (natp m)
                (irv-ballot-p xs))
           (not (equal m l)))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance first-preference-majority-winner-cannot-be-condorcet-loser-helper))
    :in-theory (e/d (irv)
                    ()))))

;; ----------------------------------------------------------------------

;; Now, let us reason about the case when there's no majority of
;; first-preference votes in the first round.

(local
 (defthmd candidate-with-least-nth-place-votes-is-never-equal-to-irv-winner-helper
   (implies
    (and (irv-ballot-p xs)
         (not (first-choice-of-majority-p (candidate-ids xs) xs))
         (consp xs))
    (not
     (equal (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                  xs)
            (irv (eliminate-candidate
                  (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                        xs)
                  xs)))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d () (irv-winner-is-a-member-of-initial-candidate-ids))
            :use ((:instance irv-winner-is-a-member-of-initial-candidate-ids
                             (xs
                              (eliminate-candidate
                               (candidate-with-least-nth-place-votes
                                0 (candidate-ids xs) xs)
                               xs))))))))

(defthm candidate-with-least-nth-place-votes-is-never-equal-to-irv-winner
  (implies (and (not (first-choice-of-majority-p (candidate-ids xs) xs))
                (< 1 (len (candidate-ids xs)))
                (irv-ballot-p xs))
           (not (equal (irv xs)
                       (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs))))
  :hints
  (("Goal"
    :induct (irv xs)
    :in-theory
    (e/d (irv
          candidate-with-least-nth-place-votes
          candidate-with-least-nth-place-votes-is-never-equal-to-irv-winner-helper)
         ()))))

(defthm len-of-candidate-ids-from-len-of-cids-lemma
  (implies (and (acl2::set-equiv (candidate-ids xs) (cons l cids))
                (no-duplicatesp-equal (cons l cids))
                (<= 1 (len cids)))
           (< 1 (len (candidate-ids xs))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance equal-len-of-no-duplicates-set-equivs
                            (x (candidate-ids xs))
                            (y (cons l cids))))))
  :rule-classes (:rewrite))

(defthm no-duplicatesp-equal-cons-and-remove-equal-lemma
  (implies (no-duplicatesp-equal (cons i cids))
           (no-duplicatesp-equal (cons i (remove-equal j cids)))))

(defthm len-of-remove-equal=0-lemma
  (implies (and (equal (len (remove-equal e cids)) 0)
                (no-duplicatesp-equal cids)
                (true-listp cids)
                (<= 1 (len cids)))
           (equal cids (list e)))
  :hints (("Goal" :in-theory (e/d ()
                                  ((:linear upper-bound-of-duplicity)
                                   (:linear sum-of-duplicities-upper-bound)
                                   (:rewrite acl2::len-of-remove-exact)))))
  :rule-classes nil)

(defthm no-duplicatesp-equal-cons-lemma
  (implies (no-duplicatesp-equal (cons i cids))
           (no-duplicatesp-equal cids)))

(defthm two-candidates-left-first-round-no-majority-lemma
  (implies
   (and
    (equal
     (len
      (remove-equal
       (candidate-with-least-nth-place-votes
        0 (candidate-ids xs) xs) cids))
     0)
    (not (first-choice-of-majority-p (candidate-ids xs)
                                     xs))
    (acl2::set-equiv (candidate-ids xs)
                     (cons (irv xs) cids))
    (no-duplicatesp-equal (cons (irv xs) cids))
    (nat-listp cids)
    (<= 1 (len cids))
    (irv-ballot-p xs))
   (not (all-head-to-head-competition-loser-p
         (irv xs) cids xs)))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance len-of-remove-equal=0-lemma
                     (e (candidate-with-least-nth-place-votes
                         0 (candidate-ids xs) xs))
                     (cids cids)))
    :in-theory (e/d (all-head-to-head-competition-loser-p
                     head-to-head-competition-loser-p
                     eliminate-other-candidates
                     eliminate-candidates)
                    ((:definition irv-ballot-p)
                     (:definition member-equal)
                     (:definition no-duplicatesp-equal)
                     (:definition not)
                     acl2::len-of-remove-exact
                     (:linear upper-bound-of-duplicity))))))

(defthmd subsetp-cons-and-remove-equal-lemma
  (implies (and (subsetp-equal orig-cids (cons i cids))
                (not (equal i j)))
           (subsetp-equal (remove-equal j orig-cids)
                          (cons i (remove-equal j cids))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance acl2::subsetp-of-remove1
                            (x (remove-equal j orig-cids))
                            (a j)
                            (y (cons i cids)))
                 (:instance acl2::subsetp-of-remove2
                            (x orig-cids)
                            (y (cons i cids))
                            (a j)))
           :in-theory (e/d () (acl2::subsetp-of-remove2
                               acl2::subsetp-of-remove1
                               (:rewrite subset-member-remove-equal-lemma)
                               (:rewrite acl2::subsetp-cons-2)
                               (:rewrite acl2::subsetp-refl)
                               (:rewrite acl2::subsetp-trans2))))))

(defthm set-equiv-cons-and-remove-equal-lemma
  (implies (and
            (acl2::set-equiv orig-cids (cons i cids))
            (not (equal i j)))
           (acl2::set-equiv (remove-equal j orig-cids)
                            (cons i (remove-equal j cids))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subsetp-cons-and-remove-equal-lemma))
           :in-theory (e/d (acl2::set-equiv) ()))))

(defthm simplify-nest-of-eliminate-candidate-of-eliminate-candidates-of-remove-equal
  (implies (and (irv-ballot-p xs)
                (member-equal id cids))
           (equal (eliminate-candidate id (eliminate-candidates (remove-equal id cids) xs))
                  (eliminate-candidates cids xs)))
  :hints (("Goal" :in-theory (e/d (eliminate-candidates)
                                  ()))))

(defthm eliminate-candidates-when-id-not-in-cids
  (implies (and (irv-ballot-p xs)
                (not (member-equal id cids)))
           (equal (eliminate-candidates (remove-equal id cids) xs)
                  (eliminate-candidates cids xs)))
  :hints (("Goal" :in-theory (e/d (eliminate-candidates)
                                  ()))))

(defthm remove-all-of-nil
  (equal (remove-all nil x) x))

(defthm head-to-head-competition-loser-p-after-eliminate-candidate
  (implies (and (head-to-head-competition-loser-p l c xs)
                (member-equal id (candidate-ids xs))
                (not (equal id c))
                (not (equal id l))
                (irv-ballot-p xs))
           (head-to-head-competition-loser-p l c (eliminate-candidate id xs)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (head-to-head-competition-loser-p
                            eliminate-other-candidates
                            eliminate-candidates)
                           (remove-all
                            remove-all-cons-to-remove-all-remove-equal
                            acl2::remove-is-commutative
                            (:rewrite remove-equal-commutes))))))

(defthm head-to-head-competition-loser-p-from-all-head-to-head-competition-loser-p
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (member-equal c cids))
           (head-to-head-competition-loser-p l c xs))
  :hints (("Goal"
           :in-theory (e/d (all-head-to-head-competition-loser-p)
                           (len
                            no-duplicatesp-equal)))))

(defthm no-duplicatesp-equal-cons-cdr-lemma
  (implies (no-duplicatesp-equal (cons i cids))
           (no-duplicatesp-equal (cons i (cdr cids)))))

(defthm all-head-to-head-competition-loser-p-with-a-subset-of-cids
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (subsetp-equal cids-smaller cids))
           (all-head-to-head-competition-loser-p l cids-smaller xs))
  :hints (("Goal" :in-theory (e/d (all-head-to-head-competition-loser-p
                                   subsetp-equal)
                                  ()))))

(defthm all-head-to-head-competition-loser-p-with-a-superset-of-cids
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (head-to-head-competition-loser-p l i xs)
                (not (equal l i)))
           (all-head-to-head-competition-loser-p l (cons i cids) xs))
  :hints (("Goal" :in-theory (e/d (all-head-to-head-competition-loser-p)
                                  ()))))

(defthm l-is-still-condorcet-loser-after-eliminate-candidate
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (member-equal id (candidate-ids xs))
                (not (equal id l))
                (irv-ballot-p xs))
           (all-head-to-head-competition-loser-p
            l
            (remove-equal id cids)
            (eliminate-candidate id xs)))
  :hints (("Goal"
           :induct (all-head-to-head-competition-loser-p l cids xs)
           :in-theory (e/d (all-head-to-head-competition-loser-p)
                           (len
                            remove-equal
                            member-equal
                            (:definition irv-ballot-p)
                            (:definition member-equal)
                            (:definition no-duplicatesp-equal)
                            (:definition not))))))

(define non-maj-ind-hint (l cids xs)
  :measure (number-of-candidates xs)
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (eliminate-candidate-reduces-the-number-of-candidates))
           :use ((:instance eliminate-candidate-reduces-the-number-of-candidates
                            (id (candidate-with-least-nth-place-votes
                                 0 (candidate-ids xs) xs))
                            (xs xs)))))
  :prepwork
  ((defthm candidate-with-least-nth-place-votes-is-a-member-of-cids-alt
     (implies (and (nat-listp cids)
                   (consp cids)
                   (irv-ballot-p xs))
              (member-equal (candidate-with-least-nth-place-votes n cids xs)
                            cids))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance candidate-with-least-nth-place-votes-is-in-cids
                               (n n) (cids cids) (xs xs))
                    (:instance candidate-with-least-nth-place-votes-returns-a-natp
                               (n n) (cids cids) (xs xs)))
              :in-theory (e/d (subsetp-equal)
                              (candidate-with-least-nth-place-votes-is-in-cids
                               candidate-with-least-nth-place-votes-returns-a-natp))))))
  :verify-guards nil
  :enabled t
  (if (or (not (irv-ballot-p xs)) (endp cids) (endp xs))
      (mv l cids xs)
    ;; (if (natp (first-choice-of-majority-p (candidate-ids xs) xs))
    ;;     (mv l cids xs)
    (b* ((step-2-candidate-to-remove
          (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs))
         (new-xs
          (eliminate-candidate step-2-candidate-to-remove xs)))
      (if (equal l step-2-candidate-to-remove)
          (mv step-2-candidate-to-remove cids xs)
        (non-maj-ind-hint l
                          (remove-equal step-2-candidate-to-remove cids)
                          new-xs)))))

(defthm natp-of-first-choice-of-majority-p-when-non-nil
  (implies (and (first-choice-of-majority-p cids xs)
                (nat-listp cids))
           (natp (first-choice-of-majority-p cids xs)))
  :hints (("Goal" :in-theory (e/d (first-choice-of-majority-p
                                   create-nth-choice-count-alist)
                                  ()))))

(defthm condorcet-loser-is-not-a-member-of-cids
  (implies (all-head-to-head-competition-loser-p l cids xs)
           (not (member-equal l cids)))
  :hints (("Goal" :in-theory (e/d (all-head-to-head-competition-loser-p)
                                  ()))))

(defthm all-head-to-head-competition-loser-cant-be-an-irv-winner-non-maj
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (not (first-choice-of-majority-p (candidate-ids xs) xs))
                (acl2::set-equiv (cons l cids) (candidate-ids xs))
                (no-duplicatesp-equal (cons l cids))
                (nat-listp cids) (<= 1 (len cids))
                (irv-ballot-p xs))
           (not (equal (irv xs) l)))
  :hints
  (("Goal"
    :induct (non-maj-ind-hint l cids xs)
    :in-theory (e/d (all-head-to-head-competition-loser-p
                     head-to-head-competition-loser-p
                     eliminate-other-candidates
                     eliminate-candidates)
                    (acl2::len-of-remove-exact
                     (:definition irv-ballot-p)
                     (:definition member-equal)
                     (:definition no-duplicatesp-equal)
                     (:definition not)
                     (:definition endp)
                     (:linear upper-bound-of-duplicity))))
   (if (and (consp id)
            (equal (car id) '(0 1)))
       ;; Subgoals in top-level induction
       '(:do-not-induct
         t
         :expand
         ((irv xs)
          (irv (eliminate-candidate
                (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                      xs)
                xs)))
         :use
         ((:instance candidate-with-least-nth-place-votes-is-never-equal-to-irv-winner)
          (:instance natp-of-first-choice-of-majority-p-when-non-nil
                     (cids (remove-equal
                            (candidate-with-least-nth-place-votes
                             0 (candidate-ids xs) xs)
                            (candidate-ids xs)))
                     (xs
                      (eliminate-candidate
                       (candidate-with-least-nth-place-votes
                        0 (candidate-ids xs) xs)
                       xs)))
          (:instance majority-winner-is-a-member-of-cids
                     (cids (remove-equal
                            (candidate-with-least-nth-place-votes
                             0 (candidate-ids xs) xs)
                            (candidate-ids xs)))
                     (xs (eliminate-candidate
                          (candidate-with-least-nth-place-votes
                           0 (candidate-ids xs) xs)
                          xs)))
          (:instance l-is-still-condorcet-loser-after-eliminate-candidate
                     (l (irv xs))
                     (cids cids)
                     (id (candidate-with-least-nth-place-votes
                          0 (candidate-ids xs) xs))
                     (xs xs))
          (:instance first-preference-majority-winner-cannot-be-condorcet-loser-helper
                     (l (first-choice-of-majority-p
                         (remove-equal
                          (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs)
                          (candidate-ids xs))
                         (eliminate-candidate
                          (candidate-with-least-nth-place-votes
                           0 (candidate-ids xs) xs)
                          xs)))
                     (cids (remove-equal
                            (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                                  xs)
                            cids))
                     (xs (eliminate-candidate
                          (candidate-with-least-nth-place-votes
                           0 (candidate-ids xs) xs) xs))
                     (m (first-choice-of-majority-p
                         (remove-equal (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                                             xs)
                                       (candidate-ids xs))
                         (eliminate-candidate
                          (candidate-with-least-nth-place-votes 0 (candidate-ids xs)
                                                                xs)
                          xs))))
          (:instance two-candidates-left-first-round-no-majority-lemma))
         :in-theory
         (e/d ()
              ((:definition irv-ballot-p)
               (:definition member-equal)
               (:definition no-duplicatesp-equal)
               (:definition not)
               acl2::len-of-remove-exact
               (:linear upper-bound-of-duplicity)
               candidate-with-least-nth-place-votes-is-never-equal-to-irv-winner
               natp-of-first-choice-of-majority-p-when-non-nil
               majority-winner-is-a-member-of-cids
               l-is-still-condorcet-loser-after-eliminate-candidate
               (:rewrite acl2::member-of-cons)
               (:rewrite acl2::member-of-remove)
               two-candidates-left-first-round-no-majority-lemma)))
     nil)))

;; ----------------------------------------------------------------------

;; We now arrive at the final theorem below:

(local
 (defthm consp-of-xs-from-len-of-candidate-ids
   (implies (and (irv-ballot-p xs)
                 (< 1 (len (candidate-ids xs))))
            (consp xs))))

(defthm irv-satisfies-the-condorcet-loser-criterion
  (implies (and (all-head-to-head-competition-loser-p l cids xs)
                (acl2::set-equiv (cons l cids) (candidate-ids xs))
                (no-duplicatesp-equal (cons l cids))
                (nat-listp cids) (<= 1 (len cids))
                (irv-ballot-p xs))
           (not (equal (irv xs) l)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  all-head-to-head-competition-loser-cant-be-an-irv-winner-non-maj)
                 (:instance first-preference-majority-winner-cannot-be-condorcet-loser
                            (m (irv xs)))
                 (:instance len-of-candidate-ids-from-len-of-cids-lemma))
           :in-theory
           (e/d ()
                (len-of-candidate-ids-from-len-of-cids-lemma
                 all-head-to-head-competition-loser-cant-be-an-irv-winner-non-maj
                 first-preference-majority-winner-cannot-be-condorcet-loser)))))

;; ----------------------------------------------------------------------
;; ----------------------------------------------------------------------
;; ----------------------------------------------------------------------

;; Majority Criterion: if a candidate is preferred by an absolute majority of
;; voters, then that candidate must win.

(defthm irv-satisfies-the-majority-criterion
  (implies (and (< (majority (number-of-voters xs))
                   (acl2::duplicity e (make-nth-choice-list 0 xs)))
                (irv-ballot-p xs))
           (equal (irv xs) e))
  :hints
  (("Goal"
    :do-not-induct t
    :expand ((irv xs))
    :use ((:instance first-choice-of-majority-p-in-terms-of-candidate-duplicity
                     (cids (candidate-ids xs))))
    :in-theory
    (e/d (first-choice-of-majority-p)
         (first-choice-of-majority-p-in-terms-of-candidate-duplicity
          duplicity-of-e-higher-than-majority-is-max-nats
          no-duplicatesp-equal
          irv-ballot-p
          key-for-a-unique-val-in-alist
          first-choice-of-majority-p-empty-implies-more-than-one-candidate
          exactly-one-candidate-gets-all-the-votes
          sum-nats-majority-duplicity=1)))))

;; ----------------------------------------------------------------------
;; ----------------------------------------------------------------------
;; ----------------------------------------------------------------------

;; Majority Loser Criterion: if a candidate has a majority of last-place votes,
;; then he must not win.

;; Note that the Condorcet Loser Criterion implies the majority loser criterion
;; (see why below).  Interestingly, the Condorcet Winner Criterion does not
;; imply the Majority Loser Criterion.

;; We can prove this from the proof of the Condorcet Loser Criterion; we need
;; to show that if a candidate has a majority of last-place votes, then he is a
;; Condorcet loser.  We'd need the following lemmas:

;; - If there's a majority winner in the first round: If a candidate has a
;;   majority of last-place votes, then he can't have a majority of first-place
;;   votes.

;; - Such a candidate will always lose a head-to-head competition with
;;   every other candidate because the other candidate will have a
;;   majority of first-place votes.

(local
 (defthmd no-duplicatesp-and-duplicity-helper-lemma
   (implies (and (no-duplicatesp-equal xs)
                 (<= j i))
            (<= (+ j (acl2::duplicity e xs))
                (+ 1 i)))))

(defthm upper-bound-of-the-total-votes-of-a-candidate-in-a-ballot
  (implies (irv-ballot-p xs)
           (<= (acl2::duplicity e (acl2::flatten xs))
               (number-of-voters xs)))
  :hints (("Goal" :in-theory (e/d (number-of-voters
                                   irv-ballot-p
                                   no-duplicatesp-and-duplicity-helper-lemma)
                                  ())))
  :rule-classes (:linear :rewrite))

(defthm member-equal-and-nth-helper-lemma
  (implies (and (not (member-equal e x))
                (nat-listp x)
                (natp e))
           (not (equal (nth n x) e))))

(defthm nth-of-no-duplicatesp-unequal
  (implies (and (no-duplicatesp-equal x)
                (not (equal m n))
                ;; really, just a list with non-nil elements
                (nat-listp x)
                (< m (len x))
                (natp n)
                (natp m))
           (not (equal (nth n x) (nth m x))))
  :hints (("Goal" :in-theory (e/d (no-duplicatesp-equal) ()))))

(defun total-votes-ind-hint (e m n nth-choice-lst mth-choice-lst xs)
  (cond ((or (atom xs)
             (not (natp e))
             (not (natp m))
             (not (natp n)))
         (mv e m n nth-choice-lst mth-choice-lst xs))
        ((or (and (equal e (nth n (car xs)))
                  (not (equal e (nth m (car xs)))))
             (and (equal e (nth m (car xs)))
                  (not (equal e (nth n (car xs)))))
             (and (not (equal e (nth n (car xs))))
                  (not (equal e (nth m (car xs))))))
         (total-votes-ind-hint
          e m n
          (cdr nth-choice-lst) (cdr mth-choice-lst) (cdr xs)))
        (t
         (mv e m n nth-choice-lst mth-choice-lst xs))))

(defthm upper-bound-of-the-total-votes-in-terms-of-make-nth-choice-list
  (implies (and (not (equal m n))
                (irv-ballot-p xs)
                (natp m) (natp n) (natp e))
           (<= (+ (acl2::duplicity e (make-nth-choice-list m xs))
                  (acl2::duplicity e (make-nth-choice-list n xs)))
               (number-of-voters xs)))
  :hints (("Goal"
           :induct (total-votes-ind-hint
                    e m n
                    (make-nth-choice-list n xs)
                    (make-nth-choice-list m xs)
                    xs)
           :in-theory (e/d (number-of-voters
                            make-nth-choice-list)
                           (not
                            no-duplicatesp-equal
                            consp-of-xs-from-len-of-candidate-ids
                            sum-nats-majority-duplicity=1
                            natp-of-sum-nats
                            majority-upper-bound))))
  :rule-classes :linear)

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm majority-unique-lemma
    (implies (and (<= (+ x y) n)
                  (< (majority n) x)
                  (natp n) (natp x) (natp y))
             (<= y (majority n)))
    :hints (("Goal" :in-theory (e/d (majority) ())))
    :rule-classes :linear))

(defthm irv-majority-winner-satisfies-the-majority-loser-criterion
  (implies
   (and (< (majority (number-of-voters xs))
           (acl2::duplicity l (make-nth-choice-list last-place xs)))
        (natp (first-choice-of-majority-p (candidate-ids xs) xs))
        (equal last-place (1- (number-of-candidates xs)))
        (< 1 (number-of-candidates xs))
        (irv-ballot-p xs))
   (not (equal (irv xs) l)))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance first-choice-of-majority-p-in-terms-of-candidate-duplicity-2
                (cids (candidate-ids xs))
                (xs xs)
                (e (first-choice-of-majority-p (candidate-ids xs) xs)))
     (:instance upper-bound-of-the-total-votes-in-terms-of-make-nth-choice-list
                (m 0)
                (n (+ -1 (number-of-candidates xs)))
                (e (first-choice-of-majority-p (candidate-ids xs) xs))
                (xs xs)))
    :in-theory
    (e/d (irv)
         (irv-ballot-p
          upper-bound-of-the-total-votes-in-terms-of-make-nth-choice-list)))))

(local
 (defthm number-of-candidates-after-eliminate-other-candidates-helper-lemma
   (implies (and (acl2::set-equiv (list l c) (candidate-ids xs))
                 (not (equal l c)))
            (equal (number-of-candidates xs) 2))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance equal-len-of-no-duplicates-set-equivs
                             (x (list l c))
                             (y (candidate-ids xs))))
            :in-theory (e/d (number-of-candidates)
                            ())))))

(local
 (defthm irv-winner-with-two-candidates-lemma
   (implies (and (not (equal (irv xs) l))
                 (acl2::set-equiv (list l c) (candidate-ids xs))
                 (irv-ballot-p xs))
            (equal (irv xs) c))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance irv-winner-is-a-member-of-initial-candidate-ids))
            :in-theory (e/d ()
                            (irv-winner-is-a-member-of-initial-candidate-ids))))))


(local
 (defthmd nth-n-x-is-a-member-of-flatten-xs
   (implies (and (< n (len x))
                 (natp n)
                 (member-equal x xs))
            (member-equal (nth n x) (acl2::flatten xs)))))

(local
 (defthmd id-in-xs-iff-id-in-candidate-ids
   (iff (member-equal id (acl2::flatten xs))
        (member-equal id (candidate-ids xs)))
   :hints (("Goal" :in-theory (e/d (candidate-ids) ())))))

(local
 (defthm id-not-in-xs-implies-id-not-in-choice-list
   (implies (and (not (member-equal id (candidate-ids xs)))
                 (natp n)
                 (irv-ballot-p xs))
            (not (member-equal id (make-nth-choice-list n xs))))
   :hints (("Goal"
            :in-theory (e/d (make-nth-choice-list)
                            (id-in-xs-iff-id-in-candidate-ids
                             nth-n-x-is-a-member-of-flatten-xs))
            :use ((:instance nth-n-x-is-a-member-of-flatten-xs
                             (x (car xs))
                             (xs xs)))))))

(defthmd make-nth-choice-list-cons-and-nth
  (implies (and (nat-listp x) (natp n))
           (equal (make-nth-choice-list n (cons x xs))
                  (if (nth n x)
                      (cons (nth n x) (make-nth-choice-list n xs))
                    (make-nth-choice-list n xs))))
  :hints (("Goal" :in-theory (e/d (make-nth-choice-list) ()))))

(defthmd duplicity-of-make-nth-choice-list-cons-lemma
  (implies (and (nat-listp x) (natp n) (natp e))
           (equal
            (acl2::duplicity e (make-nth-choice-list n (cons x xs)))
            (if (equal e (nth n x))
                (+ 1 (acl2::duplicity e (make-nth-choice-list n xs)))
              (acl2::duplicity e (make-nth-choice-list n xs)))))
  :hints (("Goal" :in-theory (e/d (make-nth-choice-list-cons-and-nth)
                                  (sum-nats-majority-duplicity=1
                                   irv-ballot-p
                                   consp-of-xs-from-len-of-candidate-ids
                                   duplicity->-majority-is-unique)))))

(defthm a-voters-preferences-are-a-subset-of-candidate-ids
  (implies (and (irv-ballot-p xs)
                (member-equal v xs))
           (subsetp-equal v (candidate-ids xs)))
  :hints (("Goal" :in-theory (e/d (number-of-candidates
                                   candidate-ids)
                                  ()))))

(defun subset-ind-hint (x y)
  (if (or (endp x) (endp y))
      nil
    (if (member-equal (car x) y)
        (subset-ind-hint (cdr x) (remove-equal (car x) y))
      (subset-ind-hint (cdr x) y))))

(defthmd subsetp-equal-no-duplicatesp-equal-and-len-lemma
  (implies (and (subsetp-equal x y)
                (no-duplicatesp-equal x))
           (<= (len x) (len y)))
  :hints (("Goal"
           :induct (subset-ind-hint x y)
           :in-theory (e/d (subsetp-equal) ())))
  :rule-classes (:rewrite :linear))

(defthm subsetp-equal-and-remove-equal-lemma
  (implies (and (subsetp-equal
                 (remove-equal e y)
                 (remove-equal e x))
                (member-equal e x))
           (subsetp-equal y x))
  :hints (("Goal"
           :in-theory (e/d (subsetp-equal) ()))))

(defthm len-of-proper-subset-is-strictly-less-than-its-superset
  (implies (and (subsetp-equal x y)
                (not (subsetp-equal y x))
                (no-duplicatesp-equal x))
           (< (len x) (len y)))
  :hints (("Goal"
           :induct (subset-ind-hint x y)
           :in-theory (e/d (subsetp-equal)
                           ()))
          (if (and (consp id)
                   (equal (car id) '(0 1)))
              ;; Subgoals in top-level induction
              '(:use
                ((:instance
                  subsetp-equal-and-remove-equal-lemma
                  (e (car x)) (x x) (y y))))
            nil))
  :rule-classes (:rewrite :linear))

(defthm no-duplicatesp-equal-of-voter-preferences
  ;; dumb, dumb.
  (implies (and (irv-ballot-p xs)
                (member-equal v xs))
           (no-duplicatesp-equal v)))

(defthm upper-bound-of-len-of-voter-preferences
  (implies (and (irv-ballot-p xs)
                (member-equal v xs))
           (<= (len v) (number-of-candidates xs)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance a-voters-preferences-are-a-subset-of-candidate-ids)
                 (:instance subsetp-equal-no-duplicatesp-equal-and-len-lemma
                            (x v)
                            (y (candidate-ids xs))))
           :in-theory (e/d (number-of-candidates)
                           (irv-ballot-p
                            no-duplicatesp-equal
                            acl2::member-of-cons
                            a-voters-preferences-are-a-subset-of-candidate-ids
                            subsetp-equal-no-duplicatesp-equal-and-len-lemma))))
  :rule-classes (:rewrite :linear))

(defthmd lpv-of-partial-preference-candidate-is-nil
  (implies (and (equal last-place (1- (number-of-candidates xs)))
                (< (len v) (number-of-candidates xs)))
           (equal (nth last-place v) nil))
  :hints (("Goal" :in-theory (e/d () ()))))

(local
 (defthm number-of-preferences-of-a-voter-lemma
   (implies
    (and (not (member-equal l (make-nth-choice-list n xs)))
         (<= 1 (acl2::duplicity l (make-nth-choice-list n (cons x xs)))))
    ;; (equal (nth n x) l)
    (< n (len x)))
   :hints (("Goal" :in-theory (e/d (make-nth-choice-list) ())))))


(local
 (defthmd number-of-candidates-lower-bound-helper
   (implies
    (and (not (member-equal l (make-nth-choice-list n (cdr xs))))
         (<= 1 (acl2::duplicity l (make-nth-choice-list n xs)))
         (nat-listp (car xs))
         (car xs)
         (no-duplicatesp-equal (car xs))
         (irv-ballot-p (cdr xs)))
    (< n (number-of-candidates xs)))
   :hints (("Goal"
            :in-theory (e/d ()
                            (number-of-preferences-of-a-voter-lemma
                             upper-bound-of-len-of-voter-preferences))
            :use ((:instance number-of-preferences-of-a-voter-lemma
                             (l l) (x (car xs)) (xs (cdr xs)))
                  (:instance upper-bound-of-len-of-voter-preferences
                             (v (car xs))
                             (xs xs)))))))

(defthm number-of-candidates-cdr-xs-<=-number-of-candidates-xs
  (<= (number-of-candidates (cdr xs)) (number-of-candidates xs))
  :hints (("Goal"
           :use ((:instance subsetp-equal-no-duplicatesp-equal-and-len-lemma
                            (x (candidate-ids (cdr xs)))
                            (y (candidate-ids xs))))
           :in-theory (e/d (number-of-candidates)
                           ())))
  :rule-classes :linear)


(defthm number-of-candidates-lower-bound
  (implies (and (<= 1 (acl2::duplicity l (make-nth-choice-list n xs)))
                (natp n)
                (irv-ballot-p xs))
           (< n (number-of-candidates xs)))
  :hints (("Goal"
           :induct (len xs)
           :in-theory (e/d (number-of-candidates-lower-bound-helper)
                           ())))
  :rule-classes (:linear :rewrite))

(defthmd dup-of-cdr-xs-and-dup-of-xs-lemma
  (implies (and
            (equal last-place (1- (number-of-candidates xs)))
            (< (len (car xs)) (number-of-candidates xs))
            (irv-ballot-p xs))
           (equal (acl2::duplicity l (make-nth-choice-list last-place xs))
                  (acl2::duplicity l (make-nth-choice-list last-place (cdr xs)))))
  :hints (("Goal" :in-theory (e/d (make-nth-choice-list)
                                  (consp-of-xs-from-len-of-candidate-ids
                                   sum-nats-majority-duplicity=1)))))

(defthm candidate-ids-subset-implies-length-of-voter-preferences
  (implies (and (member-equal v (cdr xs))
                (not (subsetp-equal
                      (candidate-ids xs)
                      (candidate-ids (cdr xs))))
                (irv-ballot-p xs))
           (< (len v) (number-of-candidates xs)))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance len-of-proper-subset-is-strictly-less-than-its-superset
                     (x (candidate-ids (cdr xs)))
                     (y (candidate-ids xs)))
          (:instance upper-bound-of-len-of-voter-preferences
                     (v v) (xs (cdr xs))))
    :in-theory (e/d (number-of-candidates)
                    (irv-ballot-p
                     upper-bound-of-len-of-voter-preferences
                     len-of-proper-subset-is-strictly-less-than-its-superset))))
  :rule-classes (:rewrite :linear))

(define last-place ((xs irv-ballot-p))
  :short "Index of the last-place vote in @('xs')"
  :returns (lp natp :rule-classes :type-prescription)
  :prepwork
  ((defthm posp-number-of-candidates
     (implies (and (irv-ballot-p xs)
                   (consp xs))
              (posp (number-of-candidates xs)))
     :hints (("Goal" :in-theory (e/d (number-of-candidates) ())))))

  (if (and (irv-ballot-p xs)
           (consp xs))
      (1- (number-of-candidates xs))
    0)

  ///
  (defthm last-place-after-eliminate-candidate
    (implies (and (irv-ballot-p xs)
                  (< 1 (number-of-candidates xs)))
             (equal (last-place (eliminate-candidate id xs))
                    (if (member-equal id (candidate-ids xs))
                        (1- (last-place xs))
                      (last-place xs))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (number-of-candidates)
                             ()))))

  (local
   (defthm last-place-of-cdr-xs-helper
     (implies (and (equal (len (candidate-ids xs)) 0)
                   (nat-listp (car xs))
                   (not (cdr xs)))
              (not (car xs)))
     :hints (("Goal" :in-theory (e/d (candidate-ids) ())))))

  (defthm last-place-of-cdr-xs
    (implies (irv-ballot-p xs)
             (<= (last-place (cdr xs)) (last-place xs)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance subset-of-candidate-ids-cdr)
                   (:instance subsetp-equal-no-duplicatesp-equal-and-len-lemma
                              (x (candidate-ids (cdr xs)))
                              (y (candidate-ids xs))))
             :in-theory (e/d (number-of-candidates)
                             (subset-of-candidate-ids-cdr
                              subsetp-of-irv-ballots-implies-subsetp-of-candidate-ids))))
    :rule-classes (:linear :rewrite)))


(local
 (defthm cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
   (implies (and (irv-ballot-p xs)
                 (remove-equal id (car xs)))
            (equal (cdr (eliminate-candidate id xs))
                   (eliminate-candidate id (cdr xs))))
   :hints (("Goal" :in-theory (e/d (eliminate-candidate
                                    number-of-candidates)
                                   (consp-of-xs-from-len-of-candidate-ids
                                    upper-bound-of-len-of-voter-preferences
                                    member-equal))))))

(local
 (defthmd cdr-of-eliminate-candidate-when-car-xs-is-id
   (implies (and (irv-ballot-p xs)
                 (subsetp-equal (car xs) (list id)))
            (equal (eliminate-candidate id xs)
                   (eliminate-candidate id (cdr xs))))
   :hints (("Goal" :in-theory (e/d (eliminate-candidate
                                    number-of-candidates)
                                   (consp-of-xs-from-len-of-candidate-ids
                                    upper-bound-of-len-of-voter-preferences
                                    member-equal))))))

(defun nth-lemma-ind-scheme (n id x)
  (declare (irrelevant n))
  (if (or (endp x) (<= (len x) 2))
      nil
    (if (equal id (car x))
        (equal (remove-equal id x) (cdr x))
      (nth-lemma-ind-scheme (1- n) id (cdr x)))))

(defthmd nth-of-remove-equal-lemma
  (implies (and (equal n (1- (len x)))
                (not (equal id (nth n x)))
                (member-equal id x)
                (no-duplicatesp-equal x))
           (equal (nth (1- n) (remove-equal id x))
                  (nth n x)))
  :hints (("Goal"
           :induct (nth-lemma-ind-scheme n id x)
           :in-theory (e/d (remove-equal)
                           ((:induction remove-equal)
                            (:induction true-listp)
                            (:induction member-equal)
                            (:induction no-duplicatesp-equal)
                            irv-ballot-p
                            consp-of-xs-from-len-of-candidate-ids)))))

(encapsulate
  ()

  (local
   (defthm candidate-ids-of-xs-with-one-voter
     (implies (and (irv-ballot-p xs)
                   (equal (len xs) 1))
              (subsetp-equal (candidate-ids xs) (car xs)))
     :hints (("Goal"
              :induct (irv-ballot-p xs)
              :in-theory (e/d (candidate-ids
                               subsetp-equal
                               acl2::flatten)
                              (consp-of-xs-from-len-of-candidate-ids
                               member-equal
                               subsetp-equal))))))

  (local
   (defthm number-of-candidates-of-xs-with-one-voter
     (implies (and (irv-ballot-p xs)
                   (equal (len xs) 1))
              (equal (number-of-candidates xs)
                     ;; (len (candidate-ids xs))
                     (len (car xs))))
     :hints (("Goal"
              :use ((:instance subsetp-equal-no-duplicatesp-equal-and-len-lemma
                               (x (candidate-ids xs))
                               (y (car xs))))
              :in-theory (e/d (number-of-candidates)
                              (subsetp-equal-no-duplicatesp-equal-and-len-lemma
                               consp-of-xs-from-len-of-candidate-ids
                               sum-nats-majority-duplicity=1))))))

  (local
   (defthm subgoal-1-helper
     (implies
      (and (not (equal (nth (last-place xs) (car xs)) l))
           (equal (len xs) 1))
      (equal (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
             0))
     :hints (("goal"
              :induct (make-nth-choice-list (last-place xs) xs)
              :in-theory (e/d (make-nth-choice-list)
                              (member-equal
                               no-duplicatesp-equal-of-voter-preferences
                               subset-member-cdr-lemma
                               lower-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
                               upper-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
                               acl2::subsetp-when-atom-right
                               acl2::subsetp-when-atom-left
                               no-duplicatesp-equal
                               (:linear duplicity->-majority-is-unique)
                               if-eliminate-candidate-reduced-the-number-of-candidates-then-id-was-a-candidate
                               (:linear acl2::duplicity-when-member-equal)
                               (:linear first-choice-of-majority-p-empty-implies-more-than-one-candidate)))))))

  (local
   (defthm subgoal-2-helper-1
     (implies
      (and (not (member-equal (nth (+ -1 (len (car xs))) (car xs))
                              (make-nth-choice-list 0 xs)))
           (member-equal id (candidate-ids xs))
           (equal (len xs) 1)
           (irv-ballot-p xs)
           (not (consp (eliminate-candidate id xs))))
      (<= (acl2::duplicity (nth (+ -1 (len (car xs))) (car xs))
                           (make-nth-choice-list (+ -1 (len (car xs))) xs))
          0))
     :hints
     (("goal"
       :in-theory
       (e/d
        (make-nth-choice-list eliminate-candidate)
        (member-equal
         no-duplicatesp-equal-of-voter-preferences
         subset-member-cdr-lemma
         lower-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
         upper-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
         acl2::subsetp-when-atom-right
         acl2::subsetp-when-atom-left
         no-duplicatesp-equal
         (:linear duplicity->-majority-is-unique)
         if-eliminate-candidate-reduced-the-number-of-candidates-then-id-was-a-candidate
         (:linear acl2::duplicity-when-member-equal)
         (:linear
          first-choice-of-majority-p-empty-implies-more-than-one-candidate)
         upper-bound-of-max-nats-of-strip-cdrs-of-create-nth-choice-count-alist))))))

  (local
   (defthmd eliminate-candidate-nil
     (implies (equal (len xs) 0)
              (equal (eliminate-candidate id xs) nil))
     :hints (("Goal" :in-theory (e/d (eliminate-candidate) ())))))

  (local
   (defthmd remove-equal-nil
     (implies (equal (len xs) 0)
              (equal (remove-equal id xs) nil))
     :hints (("Goal" :in-theory (e/d (remove-equal) ())))))

  (local
   (defthmd eliminate-candidate-equal-when-one-voter
     (implies (and (irv-ballot-p xs)
                   (consp (eliminate-candidate id xs))
                   (equal (len xs) 1))
              (equal (eliminate-candidate id xs)
                     (list (remove-equal id (car xs)))))
     :hints (("Goal"
              :expand ((eliminate-candidate id xs))
              :do-not-induct t
              :in-theory (e/d (eliminate-candidate
                               number-of-candidates
                               eliminate-candidate-nil
                               remove-equal-nil)
                              (consp-of-xs-from-len-of-candidate-ids
                               member-equal))))))

  (local
   (defthm make-nth-choice-list-with-nil-xs
     (implies (and (equal (len xs) 0)
                   (irv-ballot-p xs))
              (equal (make-nth-choice-list n xs) nil))
     :hints (("Goal" :in-theory (e/d (make-nth-choice-list) ())))))

  (local
   (defthm subgoal-2-helper-2
     (implies
      (and (member-equal id (candidate-ids xs))
           (equal (len xs) 1)
           (not (equal (nth (+ -1 (len (car xs))) (car xs)) id))
           (irv-ballot-p xs))
      (<= (acl2::duplicity (nth (+ -1 (len (car xs))) (car xs))
                           (make-nth-choice-list (+ -1 (len (car xs))) xs))
          (acl2::duplicity
           (nth (+ -1 (len (car xs))) (car xs))
           (make-nth-choice-list (+ -2 (len (car xs)))
                                 (list (remove-equal id (car xs)))))))
     :hints (("goal"
              :expand ((make-nth-choice-list (+ -1 (len (car xs))) xs))
              :do-not-induct t
              :use ((:instance nth-of-remove-equal-lemma
                               (id id)
                               (n (1- (len (car xs))))
                               (x (car xs))))
              :in-theory (e/d (make-nth-choice-list
                               eliminate-candidate-equal-when-one-voter)
                              (member-equal
                               no-duplicatesp-equal-of-voter-preferences
                               subset-member-cdr-lemma
                               lower-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
                               upper-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
                               acl2::subsetp-when-atom-right
                               acl2::subsetp-when-atom-left
                               no-duplicatesp-equal
                               (:linear duplicity->-majority-is-unique)
                               if-eliminate-candidate-reduced-the-number-of-candidates-then-id-was-a-candidate
                               (:linear acl2::duplicity-when-member-equal)
                               (:linear first-choice-of-majority-p-empty-implies-more-than-one-candidate)
                               upper-bound-of-max-nats-of-strip-cdrs-of-create-nth-choice-count-alist))))))

  (local
   (defthm subgoal-2-helper
     (implies
      (and (member-equal id (candidate-ids xs))
           (consp xs)
           (equal (len xs) 1)
           (not (equal (nth (last-place xs) (car xs)) id))
           (irv-ballot-p xs))
      (<= (acl2::duplicity (nth (last-place xs) (car xs))
                           (make-nth-choice-list (last-place xs) xs))
          (acl2::duplicity
           (nth (last-place xs) (car xs))
           (make-nth-choice-list (last-place (eliminate-candidate id xs))
                                 (eliminate-candidate id xs)))))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d (last-place
                               eliminate-candidate-equal-when-one-voter)
                              (member-equal
                               no-duplicatesp-equal-of-voter-preferences
                               subset-member-cdr-lemma
                               lower-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
                               upper-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
                               acl2::subsetp-when-atom-right
                               acl2::subsetp-when-atom-left
                               no-duplicatesp-equal
                               (:linear duplicity->-majority-is-unique)
                               if-eliminate-candidate-reduced-the-number-of-candidates-then-id-was-a-candidate
                               (:linear acl2::duplicity-when-member-equal)
                               (:linear first-choice-of-majority-p-empty-implies-more-than-one-candidate)
                               upper-bound-of-max-nats-of-strip-cdrs-of-create-nth-choice-count-alist))))))

  (defthmd duplicity-in-last-place-after-eliminate-candidate-subgoal-*1/2
    (implies
     (and (consp xs)
          (equal (len xs) 1)
          (not (equal l id))
          (irv-ballot-p xs))
     (<= (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
         (acl2::duplicity l
                          (make-nth-choice-list
                           (last-place (eliminate-candidate id xs))
                           (eliminate-candidate id xs)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((and (member-equal id (candidate-ids xs))
                          (equal (nth (last-place xs) (car xs)) l))
                     (and (member-equal id (candidate-ids xs))
                          (not (equal (nth (last-place xs) (car xs)) l))))
             :in-theory (e/d ()
                             (consp-of-xs-from-len-of-candidate-ids
                              no-duplicatesp-equal-of-voter-preferences
                              member-equal
                              acl2::duplicity-when-non-member-equal
                              duplicity-of-element-in-no-duplicatesp-list))))))

(encapsulate
  ()

  (defthm nat-listp-of-make-nth-choice-list-stronger
    (implies (irv-ballot-p xs)
             (nat-listp (make-nth-choice-list n xs)))
    :hints (("goal" :in-theory (e/d (make-nth-choice-list) ()))))

  (defthmd counting-a-non-natp-in-a-nat-listp
    (implies (and (not (natp n))
                  (nat-listp x))
             (equal (acl2::duplicity n x) 0))
    :hints (("Goal" :in-theory (e/d (acl2::duplicity) ()))))

  (local
   (defthm last-place-is-the-max-length-of-a-voter-record
     ;; acl2::nth-when-too-large-cheap
     ;; upper-bound-of-len-of-voter-preferences
     (implies (and (< (last-place xs) n)
                   (member-equal x xs)
                   (natp n)
                   (irv-ballot-p xs))
              (equal (nth n x) nil))
     :hints (("Goal" :in-theory (e/d (last-place) ())))))

  (defthmd len-of-one-voter-<=-n-if-n-is-greater-than-last-place
    (implies (and (< (last-place xs) n)
                  (natp n)
                  (irv-ballot-p xs))
             (<= (len (car xs)) n))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance upper-bound-of-len-of-voter-preferences
                              (v (car xs))))
             :in-theory (e/d (last-place)
                             (upper-bound-of-len-of-voter-preferences)))))

  (local
   (defthmd make-nth-choice-list-beyond-last-place-is-empty-helper
     (implies (and (< n (len (car xs)))
                   (< (last-place xs) n)
                   (natp n)
                   (nat-listp (car xs))
                   (no-duplicatesp-equal (car xs))
                   (irv-ballot-p (cdr xs)))
              (not (list (nth n (car xs)))))
     :hints
     (("Goal"
       :use
       ((:instance len-of-one-voter-<=-n-if-n-is-greater-than-last-place))))))

  (local
   (defthm make-nth-choice-list-beyond-last-place-is-empty
     (implies (and (< (last-place xs) n)
                   (natp n)
                   (irv-ballot-p xs))
              (equal (make-nth-choice-list n xs) nil))
     :hints (("Goal"
              :in-theory
              (e/d (make-nth-choice-list
                    make-nth-choice-list-beyond-last-place-is-empty-helper)
                   ())))))

  (defthm count-in-choice-list-at-preference-beyond-the-last-place-is-zero
    (implies
     (and (< (last-place xs) m)
          (irv-ballot-p xs)
          (natp m))
     (equal (acl2::duplicity l (make-nth-choice-list m xs)) 0))
    :hints (("Goal" :in-theory (e/d (make-nth-choice-list) ()))))

  (local
   (defthm lower-bound-of-duplicity-of-make-nth-choice-list-at-last-place
     (implies
      (irv-ballot-p xs)
      (<= 0
          (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))))
     :hints (("Goal" :in-theory (e/d (make-nth-choice-list) ())))
     :rule-classes (:rewrite :linear)))

  (defthmd last-place-in-terms-of-len-of-car-xs
    (implies (and (irv-ballot-p xs)
                  (natp (nth (last-place xs) (car xs))))
             (equal (last-place xs) (+ -1 (len (car xs)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance upper-bound-of-len-of-voter-preferences
                              (v (car xs))))
             :in-theory (e/d (last-place
                              number-of-candidates)
                             (upper-bound-of-len-of-voter-preferences)))))

  (defthmd cids-subset-of-voter-with-natp-last-place-vote
    (implies (and (irv-ballot-p xs)
                  (natp (nth (last-place xs) (car xs))))
             (subsetp-equal (candidate-ids xs) (car xs)))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance last-place-in-terms-of-len-of-car-xs)
            (:instance len-of-proper-subset-is-strictly-less-than-its-superset
                       (x (car xs))
                       (y (candidate-ids xs))))
      :in-theory
      (e/d (last-place
            number-of-candidates)
           (upper-bound-of-len-of-voter-preferences
            len-of-proper-subset-is-strictly-less-than-its-superset)))))

  (local
   (defthmd id-not-in-xs-if-not-ranked-by-voter-with-natp-last-place-vote
     (implies (and (natp (nth (last-place xs) (car xs)))
                   (irv-ballot-p xs))
              (equal (not (member-equal id (car xs)))
                     (not (member-equal id (candidate-ids xs)))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance cids-subset-of-voter-with-natp-last-place-vote))
              :in-theory (e/d ()
                              (upper-bound-of-len-of-voter-preferences))))))

  (local
   (defthmd elim-candidate-if-id-not-in-xs-if-not-ranked-by-voter-with-natp-last-place-vote
     (implies (and (not (member-equal id (car xs)))
                   (natp (nth (last-place xs) (car xs)))
                   (irv-ballot-p xs))
              (equal (eliminate-candidate id xs) xs))
     :hints
     (("Goal"
       :do-not-induct t
       :use
       ((:instance id-not-in-xs-if-not-ranked-by-voter-with-natp-last-place-vote))
       :in-theory (e/d ()
                       (upper-bound-of-len-of-voter-preferences))))))

  (local
   (defthm subgoal-2-helper
     (implies
      (and (not (member-equal id (car xs)))
           (equal (last-place xs)
                  (+ -1 (len (car xs))))
           (nat-listp (car xs))
           (no-duplicatesp-equal (car xs))
           (irv-ballot-p (cdr xs)))
      (<= (acl2::duplicity (nth (last-place xs) (car xs))
                           (make-nth-choice-list (last-place xs) xs))
          (acl2::duplicity
           (nth (last-place xs) (car xs))
           (make-nth-choice-list
            (last-place (eliminate-candidate id xs))
            (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use
       ((:instance
         elim-candidate-if-id-not-in-xs-if-not-ranked-by-voter-with-natp-last-place-vote))
       :in-theory
       (e/d ()
            (consp-of-xs-from-len-of-candidate-ids
             no-duplicatesp-equal-of-voter-preferences
             member-equal
             acl2::duplicity-when-non-member-equal
             duplicity-of-element-in-no-duplicatesp-list))))))

  (local
   (defthmd nat-listp-of-car-of-eliminate-candidate
     (implies (irv-ballot-p xs)
              (nat-listp (car (eliminate-candidate id xs))))
     :hints (("Goal"
              :use ((:instance irv-ballot-p-of-eliminate-candidate))
              :in-theory (e/d () (irv-ballot-p-of-eliminate-candidate))))))

  (local
   (defthm x-not-a-subset-of-list-id
     (implies (and (not (equal (nth n x) id))
                   (natp (nth n x)))
              (not (subsetp-equal x (list id))))
     :hints (("Goal" :in-theory (e/d (subsetp-equal) ())))))

  (local
   (defthm car-of-eliminate-candidate-in-terms-of-remove-equal
     (implies (and (not (equal (nth (last-place xs) (car xs)) id))
                   (natp (nth (last-place xs) (car xs))))
              (equal (car (eliminate-candidate id xs))
                     (remove-equal id (car xs))))
     :hints (("Goal"
              :expand ((eliminate-candidate id xs))
              :use ((:instance cids-subset-of-voter-with-natp-last-place-vote))
              :in-theory (e/d () (irv-ballot-p))))))


  (local
   (defthm number-of-candidates->-1-if-car-xs-ranked-all-voters
     (implies (and (not (equal (nth (last-place xs) (car xs)) id))
                   (natp (nth (last-place xs) (car xs)))
                   (member-equal id (candidate-ids xs))
                   (irv-ballot-p xs))
              (< 1 (number-of-candidates xs)))
     :hints
     (("Goal"
       :do-not-induct t
       :use ((:instance cids-subset-of-voter-with-natp-last-place-vote)
             (:instance last-place-in-terms-of-len-of-car-xs))
       :in-theory
       (e/d (number-of-candidates)
            (upper-bound-of-max-nats-of-strip-cdrs-of-create-count-alist
             lower-bound-of-max-nats-of-strip-cdrs-of-create-count-alist))))))

  (defthmd count-in-last-place-and-in-last-place-cdr-xs-lemma
    (implies
     (and (irv-ballot-p xs))
     (<= (acl2::duplicity l
                          (make-nth-choice-list (last-place xs) (cdr xs)))
         (acl2::duplicity l
                          (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))))
    :hints
    (("Goal"
      :do-not-induct t
      :use
      ((:instance
        count-in-choice-list-at-preference-beyond-the-last-place-is-zero
        (m (last-place xs)) (xs (cdr xs)))
       (:instance
        lower-bound-of-duplicity-of-make-nth-choice-list-at-last-place)
       (:instance last-place-of-cdr-xs))
      :in-theory
      (e/d ()
           (last-place-of-cdr-xs
            count-in-choice-list-at-preference-beyond-the-last-place-is-zero
            lower-bound-of-duplicity-of-make-nth-choice-list-at-last-place)))))

  (local
   (defthm candidate-ids-strict-subset-lemma
     (implies (and (< (last-place (cdr xs)) (last-place xs))
                   (irv-ballot-p xs))
              (not (subsetp-equal (candidate-ids xs)
                                  (candidate-ids (cdr xs)))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (last-place
                               number-of-candidates
                               subsetp-equal-no-duplicatesp-equal-and-len-lemma)
                              ())))))

  (local
   (defthmd strict-inequality-last-place-lemma-helper
     (implies (and
               (subsetp-equal (car xs) (list id))
               (member-equal id (candidate-ids xs))
               (irv-ballot-p xs))
              (equal (number-of-candidates (eliminate-candidate id (cdr xs)))
                     (number-of-candidates (eliminate-candidate id xs))))
     :hints (("Goal" :in-theory (e/d (eliminate-candidate) ())))))

  (local
   (defthm len-of-remove-equal-of-no-duplicates
     (implies (no-duplicatesp-equal x)
              (equal (len (remove-equal id x))
                     (if (member-equal id x)
                         (1- (len x))
                       (len x))))
     :hints (("Goal" :in-theory (e/d (remove-equal) ())))))

  (local
   (defthmd remove-equal-and-len-lemma
     (implies (and (< (len (remove-equal id x))
                      (len (remove-equal id y)))
                   (member-equal id y)
                   (no-duplicatesp-equal x)
                   (no-duplicatesp-equal y))
              (< (len x) (len y)))
     :hints (("Goal" :in-theory (e/d (remove-equal) ())))))

  (defthmd strict-inequality-last-place-lemma
    (implies (and
              (< (number-of-candidates (eliminate-candidate id (cdr xs)))
                 (number-of-candidates (eliminate-candidate id xs)))
              (member-equal id (candidate-ids xs))
              (irv-ballot-p xs))
             (< (number-of-candidates (cdr xs))
                (number-of-candidates xs)))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory
      (e/d (strict-inequality-last-place-lemma-helper
            number-of-candidates remove-equal-and-len-lemma)
           (candidate-ids-strict-subset-lemma
            candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids
            cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
            eliminate-candidate-reduces-the-number-of-candidates-by-one
            consp-of-xs-from-len-of-candidate-ids
            member-equal
            acl2::subsetp-when-atom-right))
      :use
      ((:instance cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr)
       (:instance
        candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids)
       (:instance
        candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids
        (xs (cdr xs)))))))

  (local
   (defthmd number-of-candidates-eliminate-candidate-strict-inequality-last-place-lemma
     (implies (and
               (< (number-of-candidates (eliminate-candidate id (cdr xs)))
                  (number-of-candidates (eliminate-candidate id xs)))
               (member-equal id (candidate-ids xs))
               (irv-ballot-p xs))
              (< (last-place (cdr xs))
                 (last-place xs)))
     :hints (("Goal"
              :use ((:instance strict-inequality-last-place-lemma))
              :in-theory (e/d (last-place) ())))))

  (local
   (defthmd last-place-and-number-of-candidates-strict-inequality-lemma
     (implies (and
               (< (last-place (cdr xs))
                  (last-place xs))
               (irv-ballot-p xs))
              (< (number-of-candidates (cdr xs))
                 (number-of-candidates xs)))
     :hints (("Goal"
              :in-theory (e/d (last-place) ())))))

  (defthmd strict-inequality-last-place-lemma-in-terms-of-last-place
    (implies (and
              (< (last-place (eliminate-candidate id (cdr xs)))
                 (last-place (eliminate-candidate id xs)))
              (remove-equal id (car xs))
              (member-equal id (candidate-ids xs))
              (irv-ballot-p xs))
             (< (last-place (cdr xs)) (last-place xs)))
    :hints
    (("Goal"
      :do-not-induct t
      :use
      ((:instance cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr)
       (:instance number-of-candidates-eliminate-candidate-strict-inequality-last-place-lemma)
       (:instance last-place-and-number-of-candidates-strict-inequality-lemma
                  (xs (eliminate-candidate id xs))))
      :in-theory (e/d ()
                      (cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr)))))

  (defthmd nth-member-of-make-nth-choice-list
    (implies (and (< n (len (car xs)))
                  (consp xs))
             (member-equal (nth n (car xs))
                           (make-nth-choice-list n xs)))
    :hints (("Goal" :in-theory (e/d (make-nth-choice-list) ()))))

  (local
   (defthmd subgoal-1-helper-3
     (implies
      (and
       (not (equal (last-place (eliminate-candidate id xs))
                   (last-place (eliminate-candidate id (cdr xs)))))
       (<= (last-place (eliminate-candidate id xs))
           (last-place (eliminate-candidate id (cdr xs))))
       (equal (last-place xs)
              (+ -1 (len (car xs))))
       (not (equal (nth (last-place xs) (car xs)) id))
       (nat-listp (car xs))
       (no-duplicatesp-equal (car xs))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use
       ((:instance last-place-of-cdr-xs
                   (xs (eliminate-candidate id xs)))
        (:instance cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr))
       :in-theory
       (e/d ()
            (cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
             consp-of-xs-from-len-of-candidate-ids
             no-duplicatesp-equal-of-voter-preferences
             member-equal
             acl2::duplicity-when-non-member-equal
             duplicity-of-element-in-no-duplicatesp-list))))))

  (local
   (defthmd subgoal-1-helper-2
     (implies
      (and
       (member-equal id (candidate-ids xs))
       (equal
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list (last-place xs) xs))
        (+ 1
           (acl2::duplicity
            (nth (last-place xs) (car xs))
            (make-nth-choice-list (last-place xs) (cdr xs)))))
       (equal (nth (+ -2 (len (car xs)))
                   (remove-equal id (car xs)))
              (nth (last-place xs) (car xs)))
       (equal (last-place xs)
              (+ -1 (len (car xs))))
       (<=
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list
          (last-place (eliminate-candidate id xs))
          (eliminate-candidate id (cdr xs)))))
       (nat-listp (car xs))
       (no-duplicatesp-equal (car xs))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use ((:instance duplicity-of-make-nth-choice-list-cons-lemma
                        (e (nth (last-place (eliminate-candidate id xs))
                                (car (eliminate-candidate id xs))))
                        (n (last-place (eliminate-candidate id xs)))
                        (x (car (eliminate-candidate id xs)))
                        (xs (eliminate-candidate id (cdr xs))))
             (:instance number-of-candidates->-1-if-car-xs-ranked-all-voters)
             (:instance last-place-after-eliminate-candidate)
             (:instance count-in-last-place-and-in-last-place-cdr-xs-lemma
                        (l (nth (last-place xs) (car xs)))))
       :in-theory (e/d (eliminate-candidate)
                       (number-of-candidates->-1-if-car-xs-ranked-all-voters
                        last-place-after-eliminate-candidate
                        cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
                        consp-of-xs-from-len-of-candidate-ids
                        no-duplicatesp-equal-of-voter-preferences
                        member-equal
                        acl2::duplicity-when-non-member-equal
                        duplicity-of-element-in-no-duplicatesp-list))))))

  (local
   (defthmd subgoal-1-helper-1
     (implies
      (and
       (< (last-place (eliminate-candidate id (cdr xs)))
          (last-place (eliminate-candidate id xs)))
       (member-equal id (candidate-ids xs))
       (equal
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list (last-place xs) xs))
        (+ 1
           (acl2::duplicity
            (nth (last-place xs) (car xs))
            (make-nth-choice-list (last-place xs) (cdr xs)))))
       (equal (nth (+ -2 (len (car xs)))
                   (remove-equal id (car xs)))
              (nth (last-place xs) (car xs)))
       (equal (last-place xs)
              (+ -1 (len (car xs))))
       (not (equal (nth (last-place xs) (car xs)) id))
       (nat-listp (car xs))
       (no-duplicatesp-equal (car xs))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use ((:instance strict-inequality-last-place-lemma-in-terms-of-last-place)
             (:instance nth-of-remove-equal-lemma
                        ;; (nth (last-place (elim id xs)) (car (elim id xs))) ==
                        ;; (nth (last-place xs) (car xs))
                        (n (1- (len (car xs))))
                        (x (car xs))
                        (id id))
             (:instance number-of-candidates->-1-if-car-xs-ranked-all-voters)
             (:instance last-place-after-eliminate-candidate)
             (:instance nth-member-of-make-nth-choice-list
                        (n (1- (last-place xs)))
                        (xs (eliminate-candidate id xs))))
       :in-theory (e/d ()
                       (number-of-candidates->-1-if-car-xs-ranked-all-voters
                        last-place-after-eliminate-candidate
                        cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
                        consp-of-xs-from-len-of-candidate-ids
                        no-duplicatesp-equal-of-voter-preferences
                        member-equal
                        acl2::duplicity-when-non-member-equal
                        duplicity-of-element-in-no-duplicatesp-list))))))

  (local
   (defthm subgoal-1-helper
     (implies
      (and
       (member-equal id (candidate-ids xs))
       (equal
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list (last-place xs) xs))
        (+ 1
           (acl2::duplicity
            (nth (last-place xs) (car xs))
            (make-nth-choice-list (last-place xs) (cdr xs)))))
       (equal (nth (+ -2 (len (car xs)))
                   (remove-equal id (car xs)))
              (nth (last-place xs) (car xs)))
       (equal (last-place xs)
              (+ -1 (len (car xs))))
       (consp xs)
       (not (equal 0 (len (cdr xs))))
       (<=
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
        (acl2::duplicity
         (nth (last-place xs) (car xs))
         (make-nth-choice-list
          (last-place (eliminate-candidate id (cdr xs)))
          (eliminate-candidate id (cdr xs)))))
       (not (equal (nth (last-place xs) (car xs))
                   id))
       (nat-listp (car xs))
       (car xs)
       (no-duplicatesp-equal (car xs))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :cases ((equal (last-place (eliminate-candidate id xs))
                      (last-place (eliminate-candidate id (cdr xs))))
               (< (last-place (eliminate-candidate id (cdr xs)))
                  (last-place (eliminate-candidate id xs))))
       :in-theory (e/d (subgoal-1-helper-3
                        subgoal-1-helper-2
                        subgoal-1-helper-1)
                       (consp-of-xs-from-len-of-candidate-ids
                        no-duplicatesp-equal-of-voter-preferences
                        member-equal
                        acl2::duplicity-when-non-member-equal
                        duplicity-of-element-in-no-duplicatesp-list))))))

  (defthmd duplicity-in-last-place-after-eliminate-candidate-subgoal-*1/3
    (implies
     (and
      (member-equal id (candidate-ids xs))
      (not (equal 0 (len (cdr xs))))
      (<=
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
       (acl2::duplicity
        (nth (last-place xs) (car xs))
        (make-nth-choice-list
         (last-place (eliminate-candidate id (cdr xs)))
         (eliminate-candidate id (cdr xs)))))
      (not (equal (nth (last-place xs) (car xs)) id))
      (irv-ballot-p xs))
     (<=
      (acl2::duplicity (nth (last-place xs) (car xs))
                       (make-nth-choice-list (last-place xs) xs))
      (acl2::duplicity
       (nth (last-place xs) (car xs))
       (make-nth-choice-list
        (last-place (eliminate-candidate id xs))
        (eliminate-candidate id xs)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance duplicity-of-make-nth-choice-list-cons-lemma
                              (n (last-place xs))
                              (e (nth (last-place xs) (car xs)))
                              (x (car xs))
                              (xs (cdr xs)))
                   (:instance nth-of-remove-equal-lemma
                              ;; (nth (last-place (elim id xs)) (car (elim id xs))) ==
                              ;; (nth (last-place xs) (car xs))
                              (n (1- (len (car xs))))
                              (x (car xs))
                              (id id))
                   (:instance last-place-in-terms-of-len-of-car-xs)
                   (:instance counting-a-non-natp-in-a-nat-listp
                              (n (nth (last-place xs) (car xs)))
                              (x (make-nth-choice-list (last-place xs) xs)))
                   (:instance counting-a-non-natp-in-a-nat-listp
                              (n (nth (last-place xs) (car xs)))
                              (x (make-nth-choice-list
                                  (last-place (eliminate-candidate id xs))
                                  (eliminate-candidate id xs)))))
             :in-theory (e/d ()
                             (consp-of-xs-from-len-of-candidate-ids
                              no-duplicatesp-equal-of-voter-preferences
                              member-equal
                              acl2::duplicity-when-non-member-equal
                              duplicity-of-element-in-no-duplicatesp-list))))))

(encapsulate
  ()

  (local
   (defthmd not-consp-eliminate-candidate
     (implies (not (consp (eliminate-candidate id xs)))
              (subsetp-equal (candidate-ids xs) (list id)))
     :hints
     (("Goal"
       :do-not-induct t
       :use
       ((:instance
         candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids))
       :in-theory
       (e/d ()
            (candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids
             eliminate-candidate-returns-a-subset-of-candidates
             candidate-ids-of-eliminate-candidate-is-remove-equal-of-candidate-ids
             subsetp-of-irv-ballots-implies-subsetp-of-candidate-ids))))))

  (local
   (defthmd remove-id-x-non-empty
     (implies (not (subsetp-equal x (list id)))
              (remove-equal id x))
     :hints (("Goal" :in-theory (e/d (remove-equal) ())))))

  (local
   (defthmd eliminate-candidate-if-car-xs-has-only-id
     (implies (subsetp-equal (car xs) (list id))
              (equal (eliminate-candidate id xs)
                     (eliminate-candidate id (cdr xs))))
     :hints (("Goal" :in-theory (e/d (eliminate-candidate) ())))))


  (local
   (defthmd goal-helper-2-helper-3
     (implies
      (and (<= (last-place (eliminate-candidate id xs))
               (last-place (eliminate-candidate id (cdr xs))))
           (not (equal (last-place (eliminate-candidate id xs))
                       (last-place (eliminate-candidate id (cdr xs)))))
           (nat-listp (car xs))
           (no-duplicatesp-equal (car xs))
           (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity
        l (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        l
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :cases ((remove-equal id (car xs)))
       :use ((:instance eliminate-candidate-if-car-xs-has-only-id)
             (:instance last-place-of-cdr-xs
                        (xs (eliminate-candidate id xs)))
             (:instance not-consp-eliminate-candidate)
             (:instance irv-ballot-p-of-eliminate-candidate)
             (:instance a-voters-preferences-are-a-subset-of-candidate-ids
                        (v (car xs)))
             (:instance remove-id-x-non-empty
                        (x (car xs))))
       :in-theory
       (e/d (eliminate-candidate)
            (count-in-choice-list-at-preference-beyond-the-last-place-is-zero
             cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
             last-place-of-cdr-xs
             consp-of-xs-from-len-of-candidate-ids
             no-duplicatesp-equal-of-voter-preferences
             member-equal
             acl2::duplicity-when-non-member-equal
             duplicity-of-element-in-no-duplicatesp-list
             id-not-in-xs-implies-id-not-in-choice-list))))))

  (local
   (defthmd goal-helper-2-helper-2
     (implies
      (and (< (last-place (cdr xs)) (last-place xs))
           (equal
            (acl2::duplicity
             l (make-nth-choice-list (last-place xs) xs))
            (acl2::duplicity
             l (make-nth-choice-list (last-place xs) (cdr xs))))
           (irv-ballot-p (cdr xs)))
      (<= (acl2::duplicity
           l (make-nth-choice-list (last-place xs) xs))
          (acl2::duplicity
           l
           (make-nth-choice-list
            (last-place (eliminate-candidate id xs))
            (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use
       ((:instance eliminate-candidate-if-car-xs-has-only-id)
        (:instance count-in-choice-list-at-preference-beyond-the-last-place-is-zero
                   (m (last-place xs))
                   (xs (cdr xs))
                   (l l)))
       :in-theory
       (e/d ()
            (count-in-choice-list-at-preference-beyond-the-last-place-is-zero
             cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
             last-place-of-cdr-xs
             consp-of-xs-from-len-of-candidate-ids
             no-duplicatesp-equal-of-voter-preferences
             member-equal
             acl2::duplicity-when-non-member-equal
             duplicity-of-element-in-no-duplicatesp-list
             id-not-in-xs-implies-id-not-in-choice-list))))))

  (local
   (defthmd goal-helper-2-helper-1
     (implies
      (and
       (subsetp-equal (car xs) (list id))
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) xs))
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs))))
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
        (acl2::duplicity
         l
         (make-nth-choice-list
          (last-place (eliminate-candidate id (cdr xs)))
          (eliminate-candidate id (cdr xs)))))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        l
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use ((:instance duplicity-of-make-nth-choice-list-cons-lemma
                        (e l)
                        (n (last-place (eliminate-candidate id xs)))
                        (x (car (eliminate-candidate id xs)))
                        (xs (eliminate-candidate id (cdr xs))))
             (:instance id-not-in-xs-implies-id-not-in-choice-list
                        (id l)
                        (n (last-place xs))
                        (xs xs))
             (:instance irv-ballot-p-of-eliminate-candidate)
             (:instance count-in-last-place-and-in-last-place-cdr-xs-lemma
                        (xs (eliminate-candidate id xs)))
             (:instance not-consp-eliminate-candidate))
       :in-theory (e/d (eliminate-candidate)
                       (irv-ballot-p
                        irv-ballot-p-of-eliminate-candidate
                        last-place-of-cdr-xs
                        consp-of-xs-from-len-of-candidate-ids
                        no-duplicatesp-equal-of-voter-preferences
                        member-equal
                        acl2::duplicity-when-non-member-equal
                        duplicity-of-element-in-no-duplicatesp-list
                        id-not-in-xs-implies-id-not-in-choice-list))))))

  (local
   (defthmd goal-helper-2
     (implies
      (and
       (not (equal (last-place (eliminate-candidate id xs))
                   (last-place (eliminate-candidate id (cdr xs)))))
       (equal
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) xs))
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) (cdr xs))))
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) xs))
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs))))
       (member-equal id (candidate-ids xs))
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
        (acl2::duplicity
         l
         (make-nth-choice-list
          (last-place (eliminate-candidate id (cdr xs)))
          (eliminate-candidate id (cdr xs)))))
       (nat-listp (car xs))
       (no-duplicatesp-equal (car xs))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        l
        (make-nth-choice-list (last-place (eliminate-candidate id xs))
                              (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use ((:instance strict-inequality-last-place-lemma-in-terms-of-last-place))
       :in-theory
       (e/d (goal-helper-2-helper-3
             goal-helper-2-helper-2
             goal-helper-2-helper-1)
            (count-in-choice-list-at-preference-beyond-the-last-place-is-zero
             cdr-of-eliminate-candidate-is-eliminate-candidate-of-cdr
             last-place-of-cdr-xs
             consp-of-xs-from-len-of-candidate-ids
             no-duplicatesp-equal-of-voter-preferences
             member-equal
             acl2::duplicity-when-non-member-equal
             duplicity-of-element-in-no-duplicatesp-list
             id-not-in-xs-implies-id-not-in-choice-list))))))

  (local
   (defthmd goal-helper-1
     (implies
      (and
       (<=
        (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs))))
       (natp l)
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
        (acl2::duplicity
         l
         (make-nth-choice-list (last-place (eliminate-candidate id xs))
                               (eliminate-candidate id (cdr xs)))))
       (nat-listp (car xs))
       (irv-ballot-p (cdr xs)))
      (<=
       (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity
        l
        (make-nth-choice-list
         (last-place (eliminate-candidate id xs))
         (eliminate-candidate id xs)))))
     :hints
     (("Goal"
       :do-not-induct t
       :use ((:instance irv-ballot-p-of-eliminate-candidate)
             (:instance count-in-last-place-and-in-last-place-cdr-xs-lemma
                        (xs (eliminate-candidate id xs)))
             (:instance not-consp-eliminate-candidate)
             (:instance id-not-in-xs-implies-id-not-in-choice-list
                        (id l)
                        (n (last-place xs))
                        (xs xs))
             (:instance duplicity-of-make-nth-choice-list-cons-lemma
                        (e l)
                        (n (last-place (eliminate-candidate id xs)))
                        (x (car (eliminate-candidate id xs)))
                        (xs (eliminate-candidate id (cdr xs))))
             (:instance id-not-in-xs-implies-id-not-in-choice-list
                        (id l)
                        (n (last-place xs))
                        (xs xs)))
       :in-theory (e/d (eliminate-candidate)
                       (irv-ballot-p
                        irv-ballot-p-of-eliminate-candidate
                        last-place-of-cdr-xs
                        consp-of-xs-from-len-of-candidate-ids
                        no-duplicatesp-equal-of-voter-preferences
                        member-equal
                        acl2::duplicity-when-non-member-equal
                        duplicity-of-element-in-no-duplicatesp-list
                        id-not-in-xs-implies-id-not-in-choice-list))))))

  (local
   (defthm goal-helper
     (implies
      (and
       (equal
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) xs))
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) (cdr xs))))
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place xs) xs))
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs))))
       (natp l)
       (member-equal id (candidate-ids xs))
       (<=
        (acl2::duplicity
         l (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
        (acl2::duplicity
         l
         (make-nth-choice-list (last-place (eliminate-candidate id (cdr xs)))
                               (eliminate-candidate id (cdr xs)))))
       (nat-listp (car xs))
       (no-duplicatesp-equal (car xs))
       (irv-ballot-p (cdr xs)))
      (<= (acl2::duplicity
           l (make-nth-choice-list (last-place xs) xs))
          (acl2::duplicity
           l
           (make-nth-choice-list (last-place (eliminate-candidate id xs))
                                 (eliminate-candidate id xs)))))
     :hints (("Goal"
              :do-not-induct t
              :cases ((equal (last-place (eliminate-candidate id xs))
                             (last-place (eliminate-candidate id (cdr xs)))))
              :in-theory (e/d (goal-helper-2
                               goal-helper-1)
                              (last-place-of-cdr-xs
                               consp-of-xs-from-len-of-candidate-ids
                               no-duplicatesp-equal-of-voter-preferences
                               member-equal
                               acl2::duplicity-when-non-member-equal
                               duplicity-of-element-in-no-duplicatesp-list))))))

  (defthmd duplicity-in-last-place-after-eliminate-candidate-subgoal-*1/4
    (implies
     (and
      (consp xs)
      (member-equal id (candidate-ids xs))
      (not (equal 0 (len (cdr xs))))
      (not (equal (nth (last-place xs) (car xs)) l))
      (<=
       (acl2::duplicity l (make-nth-choice-list (last-place (cdr xs)) (cdr xs)))
       (acl2::duplicity l
                        (make-nth-choice-list
                         (last-place (eliminate-candidate id (cdr xs)))
                         (eliminate-candidate id (cdr xs)))))
      (not (equal l id))
      (irv-ballot-p xs))
     (<= (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
         (acl2::duplicity l
                          (make-nth-choice-list (last-place (eliminate-candidate id xs))
                                                (eliminate-candidate id xs)))))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance duplicity-of-make-nth-choice-list-cons-lemma
                       (n (last-place xs))
                       (e l)
                       (x (car xs))
                       (xs (cdr xs)))
            (:instance last-place-of-cdr-xs)
            (:instance count-in-last-place-and-in-last-place-cdr-xs-lemma)
            (:instance counting-a-non-natp-in-a-nat-listp
                       (n l) (x (make-nth-choice-list (last-place xs) xs)))
            (:instance counting-a-non-natp-in-a-nat-listp
                       (n l)
                       (x (make-nth-choice-list (last-place (eliminate-candidate id xs))
                                                (eliminate-candidate id xs)))))
      :in-theory (e/d ()
                      (last-place-of-cdr-xs
                       consp-of-xs-from-len-of-candidate-ids
                       no-duplicatesp-equal-of-voter-preferences
                       member-equal
                       acl2::duplicity-when-non-member-equal
                       duplicity-of-element-in-no-duplicatesp-list))))))

(define last-place-elim-ind-hint (l id xs)
  :enabled t
  :verify-guards nil
  :prepwork
  ((local (in-theory (e/d () (member-equal irv-ballot-p)))))
  (cond ((or (endp xs)
             (not (member-equal id (candidate-ids xs))))
         nil)
        ((equal (len xs) 1) nil)
        (t
         (if (equal (nth (last-place xs) (car xs)) l)
             (last-place-elim-ind-hint l id (cdr xs))
           (last-place-elim-ind-hint l id (cdr xs))))))

(defthm duplicity-in-last-place-after-eliminate-candidate
  (implies
   (and (not (equal l id))
        (irv-ballot-p xs))
   (<= (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity l (make-nth-choice-list
                           (last-place (eliminate-candidate id xs))
                           (eliminate-candidate id xs)))))
  :hints
  (("Goal"
    :induct
    (last-place-elim-ind-hint l id xs)
    :in-theory
    (e/d (duplicity-in-last-place-after-eliminate-candidate-subgoal-*1/2
          duplicity-in-last-place-after-eliminate-candidate-subgoal-*1/3
          duplicity-in-last-place-after-eliminate-candidate-subgoal-*1/4)
         (irv-ballot-p
          consp-of-xs-from-len-of-candidate-ids
          no-duplicatesp-equal-of-voter-preferences))))
  :rule-classes :linear)

(defthm duplicity-in-last-place-after-eliminate-candidates
  (implies (and
            (not (member-equal l ids))
            (irv-ballot-p xs))
           (<= (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
               (acl2::duplicity l (make-nth-choice-list
                                   (last-place (eliminate-candidates ids xs))
                                   (eliminate-candidates ids xs)))))
  :hints (("Goal"
           :induct (eliminate-candidates ids xs)
           :in-theory (e/d (eliminate-candidates)
                           (irv-ballot-p
                            consp-of-xs-from-len-of-candidate-ids
                            no-duplicatesp-equal-of-voter-preferences))))
  :rule-classes :linear)

(defthm duplicity-in-last-place-after-eliminate-other-candidates
  (implies
   (and
    (member-equal l ids)
    (irv-ballot-p xs))
   (<= (acl2::duplicity l (make-nth-choice-list (last-place xs) xs))
       (acl2::duplicity l (make-nth-choice-list
                           (last-place (eliminate-other-candidates ids xs))
                           (eliminate-other-candidates ids xs)))))
  :hints (("Goal"
           :in-theory (e/d (eliminate-other-candidates)
                           (irv-ballot-p
                            consp-of-xs-from-len-of-candidate-ids
                            no-duplicatesp-equal-of-voter-preferences))))
  :rule-classes :linear)

;; ----------------------------------------------------------------------

(defthm number-of-voters-after-eliminate-candidates
  (implies (irv-ballot-p xs)
           (<= (number-of-voters (eliminate-candidates ids xs))
               (number-of-voters xs)))
  :hints (("goal" :induct (eliminate-candidates ids xs)
           :in-theory (e/d (eliminate-candidates)
                           (consp-of-xs-from-len-of-candidate-ids
                            subset-member-cdr-lemma
                            irv-ballot-p))))
  :rule-classes :linear)

(defthm number-of-voters-after-eliminate-other-candidates
  (implies (irv-ballot-p xs)
           (<= (number-of-voters (eliminate-other-candidates ids xs))
               (number-of-voters xs)))
  :hints (("goal"
           :in-theory (e/d (eliminate-other-candidates) ())))
  :rule-classes :linear)

(defthm majority-may-increase-if-num-voters-increase-alt
    (implies (and (<= m n)
                  (natp m)
                  (natp n))
             (<= (majority m) (majority n)))
    :hints (("Goal" :in-theory (e/d (majority) ())))
    :rule-classes :linear)

(defthmd last-place-of-eliminate-other-candidates-with-l-c
  (implies (and (irv-ballot-p xs)
                (not (equal l c))
                (member-equal l (candidate-ids xs))
                (member-equal c (candidate-ids xs)))
           (equal (last-place (eliminate-other-candidates (list l c) xs))
                  1))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance number-of-candidates-after-eliminate-other-candidates-helper-lemma
                (xs (eliminate-other-candidates (list l c) xs))))
    :in-theory
    (e/d (last-place)
         (number-of-candidates-after-eliminate-other-candidates-helper-lemma
          consp-of-xs-from-len-of-candidate-ids
          sum-of-duplicities-upper-bound
          subset-member-cdr-lemma
          irv-ballot-p)))))

(defthm majority-loser-loses-in-head-to-head-competition-helper-1
  (implies
   (and (< (majority (number-of-voters xs))
           (acl2::duplicity l (make-nth-choice-list (last-place xs) xs)))
        (member-equal c (candidate-ids xs))
        (not (equal l c))
        (irv-ballot-p xs))
   (<
    (majority (number-of-voters (eliminate-other-candidates (list l c) xs)))
    (acl2::duplicity
     l
     (make-nth-choice-list 1 (eliminate-other-candidates (list l c) xs)))))
  :hints (("Goal"
           :do-not-induct t
           :use
           ((:instance duplicity-in-last-place-after-eliminate-other-candidates
                       (ids (list l c)))
            (:instance last-place-of-eliminate-other-candidates-with-l-c)
            (:instance number-of-voters-after-eliminate-other-candidates
                       (ids (list l c)))
            (:instance majority-may-increase-if-num-voters-increase-alt
                       (m (number-of-voters (eliminate-other-candidates (list l c) xs)))
                       (n (number-of-voters xs))))
           :in-theory
           (e/d ()
                (majority-may-increase-if-num-voters-increase-alt
                 number-of-voters-after-eliminate-other-candidates
                 duplicity-in-last-place-after-eliminate-other-candidates
                 eliminate-other-candidates-equal-to-cids-under-set-equiv
                 not
                 irv-majority-winner-satisfies-the-majority-loser-criterion
                 (:rewrite acl2::consp-of-remove)
                 (:rewrite consp-of-xs-from-len-of-candidate-ids)
                 first-choice-of-majority-p-same-after-eliminate-candidate-helper-1
                 irv-ballot-p
                 sum-nats-majority-duplicity=1
                 acl2::natp-posp))))
  :rule-classes :linear)

(defthmd subsetp-equal-and-remove-equal-of-two-candidates
  (implies (and (subsetp-equal v (list l c))
                (not (equal l c)))
           (equal (remove-equal l (remove-equal c v))
                  nil))
  :hints (("Goal" :in-theory (e/d (remove-equal) ()))))

(defthmd sum-of-duplicities-upper-bound-when-two-candidates
  (implies (and (not (equal l c))
                (subsetp-equal v (list l c))
                (nat-listp v))
           (equal (+ (acl2::duplicity l v)
                     (acl2::duplicity c v))
                  (len v)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subsetp-equal-and-remove-equal-of-two-candidates)
                 (:instance acl2::len-of-remove-exact
                            (x v) (a l))
                 (:instance acl2::len-of-remove-exact
                            (x (remove-equal l v)) (a c)))
           :in-theory (e/d ()
                           (acl2::len-of-remove-exact)))))

(defthm majority-loser-loses-in-head-to-head-competition-helper-2
  (implies
   (and (acl2::set-equiv (list l c)
                         (candidate-ids
                          (eliminate-other-candidates (list l c) xs)))
        (< (majority (number-of-voters xs))
           (acl2::duplicity l (make-nth-choice-list (last-place xs) xs)))
        (member-equal c (candidate-ids xs))
        (not (equal l c))
        (natp l)
        (irv-ballot-p xs))
   (equal (irv (eliminate-other-candidates (list l c) xs))
          c))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance 0th-choice-occurrence-list-is-a-subset-of-all-candidates
                     (xs (eliminate-other-candidates (list l c) xs)))
          (:instance member-of-nat-listp
                     (e c) (lst (candidate-ids xs)))
          (:instance sum-of-duplicities-upper-bound-when-two-candidates
                     (l l) (c c)
                     (v (make-nth-choice-list
                         0
                         (eliminate-other-candidates (list l c) xs))))
          (:instance first-choice-of-majority-p-in-terms-of-candidate-duplicity
                     (e c)
                     (xs (eliminate-other-candidates (list l c) xs))
                     (cids (list l c)))
          (:instance majority-loser-loses-in-head-to-head-competition-helper-1)
          (:instance len-of-0th-choice-occurrence-list
                     (xs (eliminate-other-candidates (list l c) xs)))
          (:instance upper-bound-of-the-total-votes-in-terms-of-make-nth-choice-list
                     (m 0)
                     (n 1)
                     (e l)
                     (xs (eliminate-other-candidates (list l c) xs))))
    :in-theory
    (e/d ()
         (0th-choice-occurrence-list-is-a-subset-of-all-candidates
          first-choice-of-majority-p-in-terms-of-candidate-duplicity
          len-of-0th-choice-occurrence-list
          majority-loser-loses-in-head-to-head-competition-helper-1
          upper-bound-of-the-total-votes-in-terms-of-make-nth-choice-list
          majority-may-increase-if-num-voters-increase-alt
          number-of-voters-after-eliminate-other-candidates
          duplicity-in-last-place-after-eliminate-other-candidates
          eliminate-other-candidates-equal-to-cids-under-set-equiv
          not
          irv-majority-winner-satisfies-the-majority-loser-criterion
          (:rewrite acl2::consp-of-remove)
          (:rewrite consp-of-xs-from-len-of-candidate-ids)
          first-choice-of-majority-p-same-after-eliminate-candidate-helper-1
          irv-ballot-p
          sum-nats-majority-duplicity=1
          acl2::natp-posp)))))

(defthm majority-loser-loses-in-head-to-head-competition
  (implies (and (< (majority (number-of-voters xs))
                   (acl2::duplicity l (make-nth-choice-list (last-place xs) xs)))
                (member-equal c (candidate-ids xs))
                (not (equal l c))
                (natp l)
                (< 1 (number-of-candidates xs))
                (irv-ballot-p xs))
           (head-to-head-competition-loser-p l c xs))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance eliminate-other-candidates-equal-to-cids-under-set-equiv
                (cids (list l c))
                (xs xs))
     (:instance irv-majority-winner-satisfies-the-majority-loser-criterion
                (xs
                 (eliminate-other-candidates (list l c) xs))
                (l l)
                (last-place
                 (1- (number-of-candidates
                      (eliminate-other-candidates (list l c) xs))))))
    :in-theory
    (e/d (head-to-head-competition-loser-p)
         (eliminate-other-candidates-equal-to-cids-under-set-equiv
          not
          irv-majority-winner-satisfies-the-majority-loser-criterion
          (:rewrite acl2::consp-of-remove)
          (:rewrite consp-of-xs-from-len-of-candidate-ids)
          first-choice-of-majority-p-same-after-eliminate-candidate-helper-1
          irv-ballot-p
          sum-nats-majority-duplicity=1
          acl2::natp-posp)))))

(local
 (defthm majority-loser-loses-in-all-head-to-head-competition-helper
   (implies (and (< (majority (number-of-voters xs))
                    (acl2::duplicity l (make-nth-choice-list (last-place xs) xs)))
                 (not (member-equal l cids))
                 (subsetp-equal (cons l cids) (candidate-ids xs))
                 (natp l)
                 (< 1 (number-of-candidates xs))
                 (irv-ballot-p xs))
            (all-head-to-head-competition-loser-p l cids xs))
   :hints
   (("Goal"
     :induct (all-head-to-head-competition-loser-p l cids xs)
     :in-theory
     (e/d (all-head-to-head-competition-loser-p)
          (eliminate-other-candidates-equal-to-cids-under-set-equiv
           not
           irv-majority-winner-satisfies-the-majority-loser-criterion
           (:rewrite acl2::consp-of-remove)
           (:rewrite consp-of-xs-from-len-of-candidate-ids)
           first-choice-of-majority-p-same-after-eliminate-candidate-helper-1
           irv-ballot-p
           sum-nats-majority-duplicity=1
           acl2::natp-posp))))))

(defthm majority-loser-loses-in-all-head-to-head-competition
  (implies (and (< (majority (number-of-voters xs))
                   (acl2::duplicity l (make-nth-choice-list (last-place xs) xs)))
                (not (member-equal l cids))
                (acl2::set-equiv (cons l cids) (candidate-ids xs))
                (natp l)
                (< 1 (number-of-candidates xs))
                (irv-ballot-p xs))
           (all-head-to-head-competition-loser-p l cids xs))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (e/d (acl2::set-equiv)
         (eliminate-other-candidates-equal-to-cids-under-set-equiv
          not
          irv-majority-winner-satisfies-the-majority-loser-criterion
          (:rewrite acl2::consp-of-remove)
          (:rewrite consp-of-xs-from-len-of-candidate-ids)
          first-choice-of-majority-p-same-after-eliminate-candidate-helper-1
          irv-ballot-p
          sum-nats-majority-duplicity=1
          acl2::natp-posp)))))

(defthmd subsetp-member-cons-remove-equal-lemma-1
  (implies (member-equal id cids)
           (subsetp-equal (cons id (remove-equal id cids))
                          cids))
  :hints (("Goal"
           :in-theory (e/d (remove-equal
                            subsetp-equal)
                           ()))))

(defthmd subsetp-member-cons-remove-equal-lemma-2
  (implies (member-equal id cids)
           (subsetp-equal cids
                          (cons id (remove-equal id cids))))
  :hints (("Goal"
           :in-theory (e/d (remove-equal
                            subsetp-equal)
                           ()))))

(defthmd set-equiv-member-cons-remove-equal-lemma
  (implies (member-equal id cids)
           (acl2::set-equiv  cids
                             (cons id (remove-equal id cids))))
  :hints (("Goal"
           :in-theory (e/d (acl2::set-equiv
                            subsetp-member-cons-remove-equal-lemma-1
                            subsetp-member-cons-remove-equal-lemma-2)
                           ()))))

(defthmd set-equiv-of-cons-irv-remove-irv-lemma
  (implies (and (irv-ballot-p xs)
                (consp xs))
           (acl2::set-equiv
            (cons (irv xs)
                  (remove-equal (irv xs)
                                (candidate-ids xs)))
            (candidate-ids xs)))
  :hints (("Goal"
           :use ((:instance irv-winner-is-a-member-of-initial-candidate-ids)
                 (:instance set-equiv-member-cons-remove-equal-lemma
                            (id (irv xs))
                            (cids (candidate-ids xs))))
           :in-theory (e/d (acl2::set-equiv
                            subsetp-equal)
                           (irv-winner-is-a-member-of-initial-candidate-ids)))))

(defthmd no-duplicatesp-equal-of-cons-remove-equal-lemma
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (cons i (remove-equal i x))))
  :hints (("Goal" :in-theory (e/d (no-duplicatesp-equal remove-equal) ()))))

(defthm irv-satisfies-the-majority-loser-criterion
  (implies (and (< (majority (number-of-voters xs))
                   (acl2::duplicity l (make-nth-choice-list (last-place xs) xs)))
                (< 1 (number-of-candidates xs))
                (irv-ballot-p xs))
           (not (equal (irv xs) l)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance irv-satisfies-the-condorcet-loser-criterion
                            (l l)
                            (cids (remove-equal l (candidate-ids xs))))
                 (:instance majority-loser-loses-in-all-head-to-head-competition
                            (l l)
                            (cids (remove-equal l (candidate-ids xs))))
                 (:instance set-equiv-of-cons-irv-remove-irv-lemma))
           :in-theory (e/d (number-of-candidates
                            no-duplicatesp-equal-of-cons-remove-equal-lemma)
                           (majority-loser-loses-in-all-head-to-head-competition
                            irv-satisfies-the-condorcet-loser-criterion
                            irv-ballot-p
                            no-duplicatesp-equal
                            condorcet-loser-is-not-a-member-of-cids)))))

;; ----------------------------------------------------------------------

(define irv-alt ((xs irv-ballot-p))
  :parents (instant-runoff-voting)
  :short "An alternative (but equivalent) definition of @(see irv),
  with the majority step removed"
  :long "<p>The following theorem says that @(tsee irv-alt) and @(tsee
  irv) can be used interchangeably.</p>

  @(def irv-alt-equiv-to-irv)"

  :measure (number-of-candidates xs)
  (if (mbt (irv-ballot-p xs))

      (if (endp xs)
          nil
        (b* ((cids (candidate-ids xs)) ;; sorted CIDs.
             ;; (step-1-candidate (first-choice-of-majority-p cids xs))
             ;; ((when (natp step-1-candidate))
             ;;  step-1-candidate)
             ((if (equal (len cids) 1))
              (car cids))
             (step-2-candidate-to-remove
              (candidate-with-least-nth-place-votes
               0    ;; First preference
               cids ;; List of relevant candidates
               xs))
             (new-xs (eliminate-candidate step-2-candidate-to-remove xs)))
          (irv-alt new-xs)))

    nil)

  ///

  (local
   (defthm irv-same-after-eliminate-candidate-majority-winner
     (implies
      (and (equal cids (candidate-ids xs))
           (not (equal id (first-choice-of-majority-p cids xs)))
           (natp (first-choice-of-majority-p cids xs))
           (< 1 (number-of-candidates xs))
           (irv-ballot-p xs))
      (equal
       (irv (eliminate-candidate id xs))
       (irv xs)))
     :hints
     (("Goal"
       :do-not-induct t
       :expand ((irv xs)
                (irv (eliminate-candidate id xs)))
       :use ((:instance first-choice-of-majority-p-same-after-eliminate-candidate
                        (cids (candidate-ids xs))))
       :in-theory (e/d (eliminate-candidate)
                       (first-choice-of-majority-p-same-after-eliminate-candidate
                        first-choice-of-majority-p-in-terms-of-candidate-duplicity
                        first-choice-of-majority-p-is-in-cids
                        irv-ballot-p))))))

  (local
   (defthmd irv-alt-helper-1
     (implies
      (and
       (irv-ballot-p xs)
       (natp (first-choice-of-majority-p (candidate-ids xs)
                                         xs)))
      (equal (irv xs)
             (first-choice-of-majority-p (candidate-ids xs)
                                         xs)))
     :hints (("Goal"
              :in-theory (e/d () (irv-ballot-p))
              :expand ((irv xs))))))

  (encapsulate
    ()

    (local
     (defthmd unequal-rassoc-equal-helper
       (implies (and (not (equal (cdr pair) val))
                     (member-equal pair alst)
                     (alistp alst))
                (not (equal (rassoc-equal val alst) pair)))))

    (local
     (defthm unequal-rassoc-equal
       (implies (and (not (equal val1 val2))
                     (no-duplicatesp-equal (strip-cars alst))
                     (member-equal val2 (strip-cdrs alst))
                     (alistp alst))
                (not (equal (rassoc-equal val1 alst)
                            (rassoc-equal val2 alst))))
       :hints (("Goal" :induct (cons (rassoc-equal val1 alst)
                                     (rassoc-equal val2 alst))
                :in-theory (e/d ()
                                ((:induction alistp)
                                 (:induction true-listp)
                                 (:induction member-equal)
                                 (:induction no-duplicatesp-equal))))
               ("Subgoal *1/3"
                :use ((:instance unequal-rassoc-equal-helper
                                 (pair (car alst))
                                 (val val2)
                                 (alst alst)))))))

    (local
     (defthm unequal-car-of-rassoc-equal
       (implies (and (not (equal val1 val2))
                     (no-duplicatesp-equal (strip-cars alst))
                     (member-equal val2 (strip-cdrs alst))
                     (nat-listp (strip-cars alst)))
                (not (equal (car (rassoc-equal val1 alst))
                            (car (rassoc-equal val2 alst)))))
       :hints (("Goal" :induct (cons (rassoc-equal val1 alst)
                                     (rassoc-equal val2 alst))
                :in-theory (e/d ()
                                ((:induction alistp)
                                 (:induction true-listp)
                                 (:induction member-equal)
                                 (:induction no-duplicatesp-equal)))))))


    (local
     (defthm rassoc-equal-key-member
       ;; Also see MEMBER-EQUAL-OF-CAR-OF-RASSOC-EQUAL.
       (implies (rassoc-equal val alst)
                (member-equal (car (rassoc-equal val alst))
                              (strip-cars alst)))))

    (local
     (defthm len-of-remove1-assoc-equal
       (implies (member-equal key (strip-cars alst))
                (< (len (remove1-assoc-equal key alst))
                   (len alst)))))

    (local
     (define all-keys-ind-hint (val1 val2 alst)
       :measure (len alst)
       :hints (("Goal" :do-not-induct t))
       :enabled t
       :verify-guards nil
       (if (or (endp alst) (equal val1 val2))
           nil
         (b* ((pair1 (rassoc-equal val1 alst))
              (pair2 (rassoc-equal val2 alst)))
           (if pair1
               (and (not (equal pair1 pair2))
                    (all-keys-ind-hint val1 val2
                                       (remove1-assoc-equal (car pair1) alst)))
             (if pair2
                 (not (equal pair1 pair2))
               ;; if both are nil:
               nil))))))

    (local
     (defthm no-duplicatesp-equal-of-strip-cars-remove1-assoc-equal
       (implies (no-duplicatesp-equal (strip-cars alst))
                (no-duplicatesp-equal (strip-cars (remove1-assoc-equal key alst))))))

    (local
     (defthm alistp-of-remove1-assoc-equal
       (implies (alistp alst)
                (alistp (remove1-assoc-equal key alst)))))

    (local
     (defthm nat-listp-of-strip-cars-remove1-assoc-equal
       (implies (nat-listp (strip-cars alst))
                (nat-listp (strip-cars (remove1-assoc-equal key alst))))))

    (local
     (defthm member-equal-of-strip-cdrs-remove1-assoc-equal
       (implies (and
                 (not (equal val1 val2))
                 (no-duplicatesp-equal (strip-cars alst))
                 (nat-listp (strip-cars alst))
                 (member-equal val2 (strip-cdrs alst)))
                (member-equal
                 val2
                 (strip-cdrs (remove1-assoc-equal
                              (car (rassoc-equal val1 alst))
                              alst))))))

    (local
     (defthm rassoc-equal-of-remove1-assoc-equal
       (implies (not (equal key (car (rassoc-equal val2 alst))))
                (equal (rassoc-equal val2 (remove1-assoc-equal key alst))
                       (rassoc-equal val2 alst)))))

    (local
     (defthm keys-of-all-keys
       (implies (and (not (equal val1 val2))
                     (no-duplicatesp-equal (strip-cars alst))
                     (nat-listp (strip-cars alst))
                     (member-equal val2 (strip-cdrs alst))
                     (alistp alst))
                (not (member-equal (car (rassoc-equal val2 alst))
                                   (all-keys val1 alst))))
       :hints (("Goal"
                :induct (all-keys-ind-hint val1 val2 alst)
                :in-theory (e/d (all-keys)
                                (acl2::member-of-cons
                                 (:definition endp)
                                 (:definition not)
                                 (:definition member-equal))))
               ("Subgoal *1/2"
                :use ((:instance unequal-car-of-rassoc-equal
                                 (val1 val1)
                                 (val2 val2)
                                 (alst alst)))
                :in-theory (e/d (all-keys)
                                (unequal-car-of-rassoc-equal))))))

    ;; (defthm min-nats-+-max-nats-<=-sum-nats
    ;;   (implies (and (nat-listp x)
    ;;                 (< 1 (len x)))
    ;;            (<= (+ (min-nats x) (max-nats x))
    ;;                (sum-nats x)))
    ;;   :hints (("Goal" :in-theory (e/d (min-nats max-nats sum-nats) ()))))

    ;; (defthm foo
    ;;   (implies (and (equal (min-nats x) (max-nats x))
    ;;                 (nat-listp x)
    ;;                 (< 1 (len x)))
    ;;            (<= (max-nats x) (majority (sum-nats x))))
    ;;   :hints (("Goal" :in-theory (e/d (min-nats max-nats) ()))))


    ;; (local
    ;;  (defthmd sum-nats->-majority-is-unique-1-alt-helper-1
    ;;    (implies (and (member-equal j x)
    ;;                  (member-equal i x)
    ;;                  (not (equal i j))
    ;;                  (< 1 (len x))
    ;;                  (nat-listp x))
    ;;             (<= (+ i j) (sum-nats x)))
    ;;    :rule-classes :linear))

    (local
     (encapsulate
       ()
       (local (include-book "arithmetic-5/top" :dir :system))

       (defthm sum-nats->-majority-is-unique-1-alt
         (implies (and (< (majority (sum-nats x)) j)
                       ;; (equal (acl2::duplicity j x) 1)
                       (member-equal j x)
                       (member-equal i x)
                       (not (equal i j))
                       (nat-listp x)
                       (natp j))
                  (< i j))
         :hints (("Goal"
                  :in-theory (e/d (majority sum-nats)
                                  ())))
         :rule-classes nil)))

    ;; (defthm max-nats-is-greater-than-any-other-list-element
    ;;   (implies (and (member-equal e x)
    ;;                 (not (equal e (max-nats x)))
    ;;                 (nat-listp x))
    ;;            (< e (max-nats x)))
    ;;   :hints (("goal" :in-theory (e/d (max-nats) nil)))
    ;;   :rule-classes :linear)

    ;; (defthm foo
    ;;   (implies (and (equal (acl2::duplicity (max-nats lst) lst) 1)
    ;;                 (nat-listp lst) (< 1 (len lst))
    ;;                 (not (< (car lst) (max-nats lst))))
    ;;            (< (cadr lst) (max-nats lst))))

    (defthm min-nats-is-<=-than-any-other-list-element
      (implies (and (member-equal e x)
                    (nat-listp x))
               (<= (min-nats x) e))
      :hints (("goal" :in-theory (e/d (min-nats) nil)))
      :rule-classes :linear)

    (defthm max-nats-is->=-than-any-other-list-element
      (implies (and (member-equal e x)
                    (nat-listp x))
               (<= e (max-nats x)))
      :hints (("goal" :in-theory (e/d (max-nats) nil)))
      :rule-classes :linear)

    (local
     (defthmd cadr-of-x-is-not-e
       (implies (and (equal (acl2::duplicity e x) 1)
                     (equal (car x) e)
                     (nat-listp x))
                (not (equal (cadr x) e)))
       :hints (("Goal" :in-theory (e/d (acl2::duplicity) ())))))

    (local
     (defthmd consp-cdr-strip-cdrs-lemma
       (implies (and (count-alistp count-alst)
                     (< 1 (len count-alst)))
                (consp (cdr (strip-cdrs count-alst))))
       :hints (("Goal" :in-theory (e/d (count-alistp) ())))))

    (local
     (defthmd dumb-forcing-lemma
       (implies (count-alistp count-alst)
                (not (< (majority (sum-nats (cdr (strip-cdrs count-alst)))) 0)))
       :hints (("goal" :in-theory (e/d ()
                                       (natp-of-sum-nats
                                        natp-of-majority))
                :use ((:instance natp-of-sum-nats
                                 (lst (cdr (strip-cdrs count-alst))))
                      (:instance natp-of-majority
                                 (n (sum-nats (cdr (strip-cdrs count-alst))))))))))

    (local
     (defthmd min-nats-max-nats-contradiction-helper
       (implies
        (and (equal (acl2::duplicity (max-nats (strip-cdrs count-alst))
                                     (strip-cdrs count-alst))
                    1)
             (equal (min-nats (strip-cdrs count-alst))
                    (max-nats (strip-cdrs count-alst)))
             (< (majority (sum-nats (strip-cdrs count-alst)))
                (max-nats (strip-cdrs count-alst)))
             (< 1 (len count-alst))
             (count-alistp count-alst))
        (not (member-equal (car (rassoc-equal (max-nats (strip-cdrs count-alst))
                                              count-alst))
                           (all-keys (max-nats (strip-cdrs count-alst))
                                     count-alst))))
       :hints (("Goal"
                :do-not-induct t
                :cases ((equal (car (strip-cdrs count-alst))
                               (max-nats (strip-cdrs count-alst)))))
               ("Subgoal 2"
                :do-not-induct t
                :use ((:instance min-nats-is-<=-than-any-other-list-element
                                 (e (car (strip-cdrs count-alst)))
                                 (x (strip-cdrs count-alst)))
                      (:instance max-nats-is-greater-than-any-other-list-element
                                 (e (car (strip-cdrs count-alst)))
                                 (x (strip-cdrs count-alst))))
                :in-theory (e/d () (min-nats-is-<=-than-any-other-list-element
                                    max-nats-is-greater-than-any-other-list-element)))
               ("Subgoal 1"
                :do-not-induct t
                :use ((:instance cadr-of-x-is-not-e
                                 (e (max-nats (strip-cdrs count-alst)))
                                 (x (strip-cdrs count-alst)))
                      (:instance min-nats-is-<=-than-any-other-list-element
                                 (e (cadr (strip-cdrs count-alst)))
                                 (x (strip-cdrs count-alst)))
                      (:instance max-nats-is->=-than-any-other-list-element
                                 (e (cadr (strip-cdrs count-alst)))
                                 (x (strip-cdrs count-alst))))
                :in-theory (e/d (consp-cdr-strip-cdrs-lemma)
                                (min-nats-is-<=-than-any-other-list-element
                                 max-nats-is-greater-than-any-other-list-element)))
               (if (and (consp id)
                        (consp (car id))
                        (equal (caar id) 1))
                   ;; Top-level goals in a forcing round:
                   '(:use ((:instance dumb-forcing-lemma)))
                 nil))))



    (local
     (defthmd max-nats-key-not-a-member-of-min-nats-keys
       (implies
        (and (< (majority (sum-nats (strip-cdrs count-alst))) (max-nats (strip-cdrs count-alst)))
             (< 1 (len count-alst))
             (no-duplicatesp-equal (strip-cars count-alst))
             (count-alistp count-alst))
        (not
         (member-equal
          (car (rassoc-equal (max-nats (strip-cdrs count-alst)) count-alst))
          (all-keys (min-nats (strip-cdrs count-alst)) count-alst))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (min-nats-max-nats-contradiction-helper)
                                (keys-of-all-keys))
                :use ((:instance sum-nats-majority-duplicity=1
                                 (lst (strip-cdrs count-alst))
                                 (e (max-nats (strip-cdrs count-alst))))
                      (:instance sum-nats->-majority-is-unique-1-alt
                                 (x (strip-cdrs count-alst))
                                 (j (max-nats (strip-cdrs count-alst)))
                                 (i (min-nats (strip-cdrs count-alst))))
                      (:instance keys-of-all-keys
                                 (val1 (min-nats (strip-cdrs count-alst)))
                                 (val2 (max-nats (strip-cdrs count-alst)))
                                 (alst count-alst)))))))

    (defthmd first-choice-of-majority-p-cannot-be-candidates-with-min-votes
      (implies (and (equal m (first-choice-of-majority-p (candidate-ids xs) xs))
                    ;; number of voters should be greater than one, else the
                    ;; first-choice-of-majority-p and candidates-with-min-votes can
                    ;; be the same.
                    (< 1 (number-of-candidates xs))
                    (irv-ballot-p xs))
               (not (member-equal
                     m
                     (candidates-with-min-votes
                      (create-nth-choice-count-alist 0 (candidate-ids xs) xs)))))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance max-nats-key-not-a-member-of-min-nats-keys
                                (count-alst (create-count-alist
                                             (candidate-ids xs)
                                             (make-nth-choice-list 0 xs)))))
               :in-theory (e/d (first-choice-of-majority-p
                                candidates-with-min-votes
                                create-nth-choice-count-alist
                                number-of-candidates)
                               (irv-ballot-p)))))

    (defthmd candidate-with-least-nth-place-votes-member-of-candidates-with-min-votes-0th-place
      (implies
       (and (< 1 (number-of-candidates xs))
            (irv-ballot-p xs))
       (member-equal
        (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs)
        (candidates-with-min-votes (create-nth-choice-count-alist 0 (candidate-ids xs) xs))))
      :hints (("Goal"
               :do-not-induct t
               :expand ((candidate-with-least-nth-place-votes 0 cids xs))
               :use ((:instance pick-candidate-returns-a-member-of-cids
                                (cids (candidate-ids xs))))
               :in-theory (e/d (candidate-with-least-nth-place-votes
                                number-of-candidates)
                               (pick-candidate-returns-a-member-of-cids)))))

    (defthmd first-choice-of-majority-p-and-candidate-with-least-nth-place-votes-are-different
      (implies
       (and (< 1 (number-of-candidates xs))
            (irv-ballot-p xs))
       (not
        (equal (first-choice-of-majority-p (candidate-ids xs) xs)
               (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs))))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance first-choice-of-majority-p-cannot-be-candidates-with-min-votes
                                (m (first-choice-of-majority-p (candidate-ids xs) xs)))
                     (:instance
                      candidate-with-least-nth-place-votes-member-of-candidates-with-min-votes-0th-place))
               :in-theory (e/d ()
                               (irv-ballot-p))))))

  (local
   (defthmd irv-alt-helper-2
     (implies
      (and
       (equal (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs)
              (first-choice-of-majority-p (candidate-ids xs) xs))
       (irv-ballot-p xs)
       (not (equal (len (candidate-ids xs)) 1))
       (equal
        (irv-alt
         (eliminate-candidate (first-choice-of-majority-p (candidate-ids xs)
                                                          xs)
                              xs))
        (irv (eliminate-candidate (first-choice-of-majority-p (candidate-ids xs)
                                                              xs)
                                  xs)))
       (natp (first-choice-of-majority-p (candidate-ids xs)
                                         xs)))
      (equal
       (irv (eliminate-candidate (first-choice-of-majority-p (candidate-ids xs)
                                                             xs)
                                 xs))
       (first-choice-of-majority-p (candidate-ids xs)
                                   xs)))
     :hints
     (("goal"
       :use
       ((:instance
         first-choice-of-majority-p-and-candidate-with-least-nth-place-votes-are-different))
       :in-theory (e/d (number-of-candidates)
                       (consp-of-xs-from-len-of-candidate-ids
                        member-equal
                        irv-ballot-p
                        irv-satisfies-the-majority-loser-criterion
                        acl2::duplicity-when-non-member-equal))))))

  (local
   (defthmd irv-alt-equiv-to-irv-helper
     (implies
      (and (irv-ballot-p xs)
           (not (equal (len (candidate-ids xs)) 1))
           (equal
            (irv-alt
             (eliminate-candidate
              (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs)
              xs))
            (irv
             (eliminate-candidate
              (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs)
              xs)))
           (natp (first-choice-of-majority-p (candidate-ids xs) xs)))
      (equal
       (irv (eliminate-candidate
             (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs) xs))
       (first-choice-of-majority-p (candidate-ids xs) xs)))
     :hints
     (("Goal"
       :in-theory (e/d (irv-alt-helper-1
                        irv-alt-helper-2
                        number-of-candidates)
                       (irv-same-after-eliminate-candidate-majority-winner
                        irv-satisfies-the-majority-loser-criterion
                        acl2::duplicity-when-non-member-equal
                        id-not-in-xs-implies-id-not-in-choice-list
                        duplicity->-majority-is-unique
                        member-equal
                        irv-ballot-p))
       :use
       ((:instance irv-same-after-eliminate-candidate-majority-winner
                   (cids (candidate-ids xs))
                   (id (candidate-with-least-nth-place-votes 0 (candidate-ids xs) xs))))))))

  (defthmd irv-alt-equiv-to-irv
    (equal (irv-alt xs) (irv xs))
    :hints (("Goal"
             :induct (irv-alt xs)
             :in-theory (e/d (irv irv-alt-equiv-to-irv-helper)
                             (irv-ballot-p))))))

;; ----------------------------------------------------------------------

;; Independence of Clones:

(define adjacent-p ((clone natp)
                    (c natp)
                    (x nat-listp))
  :parents (clone-p)
  :guard (no-duplicatesp-equal x)
  ;; If one of c or clone is ranked by a voter, then the other should
  ;; follow immediately in that voter's preferences.
  (cond ((endp x) t)
        ((equal (car x) clone)
         (if (cdr x)
             (equal (car (cdr x)) c)
           nil))
        ((equal (car x) c)
         (if (cdr x)
             (equal (car (cdr x)) clone)
           nil))
        (t
         (adjacent-p clone c (cdr x))))

  ///

  (defthm adjacent-p-of-absent-elements
    (implies (and (not (member-equal c x))
                  (not (member-equal clone x)))
             (adjacent-p clone c x)))

  (defthm adjacent-p-reflexive
    (implies (adjacent-p c clone x)
             (adjacent-p clone c x)))

  (defthm remove-equal-preserves-adjacent-p
    (implies (and (adjacent-p clone c x)
                  (true-listp x)
                  (not (equal id c))
                  (not (equal id clone)))
             (adjacent-p clone c (remove-equal id x)))
    :hints (("Goal" :in-theory (e/d (remove-equal subsetp-equal) ())))))


(define clone-p
  ((clone natp
          "Candidate in @('xs') who is a possible clone of candidate @('c')")
   (c     natp "Candidate in @('xs')")
   (xs    irv-ballot-p))

  :short "Is @('clone') a clone of @('c') in @('xs')?"

  :guard (not (equal clone c))

  (if (endp xs)
      t
    (and (adjacent-p clone c (car xs))
         (clone-p clone c (cdr xs))))

  ///

  (defthm clone-p-reflexive
    (implies (clone-p c clone xs)
             (clone-p clone c xs)))

  (defthm eliminate-candidate-preserves-clone-p
    (implies (and
              (clone-p clone c xs)
              (not (equal id c))
              (not (equal id clone))
              (irv-ballot-p xs))
             (clone-p clone c (eliminate-candidate id xs)))
    :hints (("Goal" :in-theory (e/d (eliminate-candidate
                                     clone-p)
                                    ())))))

(defthm irv-satisfies-the-independence-of-clones-criterion-majority-winner
  ;; Of course, we can remove some hyps. --- this theorem will look
  ;; like first-choice-of-majority-p-same-after-eliminate-candidate
  ;; then.
  (implies (and (natp (first-choice-of-majority-p (candidate-ids xs) xs))
                (equal w (irv xs))
                (clone-p clone c xs)
                (not (equal w c))
                (not (equal w clone))
                (irv-ballot-p xs))
           (equal (irv (eliminate-candidate clone xs)) w))
  :hints (("Goal"
           :do-not-induct t
           :expand ((irv xs))
           :use ((:instance first-choice-of-majority-p-same-after-eliminate-candidate
                            (cids (candidate-ids xs))
                            (id clone)))
           :in-theory (e/d ()
                           (first-choice-of-majority-p-same-after-eliminate-candidate
                            irv-ballot-p)))))

;; ----------------------------------------------------------------------
