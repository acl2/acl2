; Copyright (C) 2016 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/lists/list-defuns" :dir :system) ;; for prefixp


;; Suppose you have a big hairy proof and you're only interested in one
;; subgoal, say Subgoal *1/1.3.5''.  You might want to skip over any goals that
;; are not on the way to that one.  You can do this with a computed hint --
;; (and (not (on-my-way-to-or-beneath id "Subgoal *1/1.3.5''")) '(:by nil)) --
;; but on-my-way-to-or-beneath isn't defined.  Here we provide subgoalp and
;; non-subgoal-p.

;; The reason non-subgoal-p is not just (not (subgoalp x)): the fuzziness of
;; inductive pools and forcing rounds, which sometimes make it impossible to
;; know for sure whether one goal is descended from another.  For example,
;; "Subgoal *1/1" may or may not be descended from "Subgoal 2" -- the clause
;; IDs don't track that dependency across induction or forcing rounds.  So:

;;  (subgoalp A B) means: A is definitely descended from B, provided A and B
;;  are both produced in the same proof.  (Subtlety: (subgoalp "Subgoal 1'''"
;;  "Subgoal 1.1") is true, but a given proof may not reach "Subgoal 1'''"
;;  before reaching "Subgoal 1.1").

;;  (non-subgoal-p A B) means A is definitely NOT descended from B.

;; So the proper computed hint for the use case above is:
;; (and (non-subgoal-p "Subgoal *1/1.3.5''" id)     ;; "not on my way to...
;;      (not (subgoalp id "Subgoal *1/1.3.5''"))    ;; "not beneath..."
;;      '(:by nil))

;; We arrange that either string or clause-id forms of inputs are usable in
;; both slots for subgoal-p and non-subgoal-p.



(defun subgoalp-ids (id1 id2)
  (and
   ;; Can't tell for sure that one is descended from another unless they are in
   ;; the same forcing-round and induction level.
   (equal (access clause-id id1 :forcing-round)
          (access clause-id id2 :forcing-round))
   (equal (access clause-id id1 :pool-lst)
          (access clause-id id2 :pool-lst))
   (let* ((case-lst1 (access clause-id id1 :case-lst))
          (case-lst2 (access clause-id id2 :case-lst)))
     (and (prefixp case-lst2 case-lst1)
          (or (not (equal case-lst1 case-lst2))
              (<= (access clause-id id2 :primes)
                  (access clause-id id1 :primes)))))))

(defun non-subgoal-p-ids (id1 id2)
  (let* ((forcing-round1 (access clause-id id1 :forcing-round))
         (forcing-round2 (access clause-id id2 :forcing-round)))
    (or
     ;; id1 is definitely not descended from id2 if id1 is in an earlier forcing round.
     (< forcing-round1 forcing-round2)
     ;; Otherwise, we only can know for sure if they're in the same forcing round:
     (and (equal forcing-round1 forcing-round2)
          (let* ((pool-lst1 (access clause-id id1 :pool-lst))
                 (pool-lst2 (access clause-id id2 :pool-lst)))
            ;; id1 is definitely not descended from id2 unless id2's pool list is a prefix of id1's.
            (or (not (prefixp pool-lst2 pool-lst1))
                ;; Otherwise, we only can know for sure if they're in the same induction round:
                (and (equal pool-lst2 pool-lst1)
                     (let* ((case-lst1 (access clause-id id1 :case-lst))
                            (case-lst2 (access clause-id id2 :case-lst)))
                       ;; same sort of thing for case-lst as for pool-lst
                       (or (not (prefixp case-lst2 case-lst1))
                           ;; Otherwise, we only can know for sure if they're in the same induction round:
                           (and (equal case-lst2 case-lst1)
                                ;; finally, id1 is not descended from id2 if id2 is a later prime:
                                (< (access clause-id id1 :primes)
                                   (access clause-id id2 :primes))))))))))))


(local (defthm prefixp-self
         (prefixp x x)
         :hints(("Goal" :in-theory (enable prefixp)))))

(local (defthm non-subgoal-p-ids-implies-not-subgoalp-ids
         (implies (non-subgoal-p-ids id1 id2)
                  (not (subgoalp-ids id1 id2)))))


(program)


(defun subgoalp (goal1 goal2)
  (subgoalp-ids (if (stringp goal1)
                    (parse-clause-id goal1)
                  goal1)
                (if (stringp goal2)
                    (parse-clause-id goal2)
                  goal2)))

(defun non-subgoal-p (goal1 goal2)
  (non-subgoal-p-ids (if (stringp goal1)
                         (parse-clause-id goal1)
                       goal1)
                     (if (stringp goal2)
                         (parse-clause-id goal2)
                       goal2)))

(assert-event      (non-subgoal-p "Goal"             "Subgoal 1"))
(assert-event (not (non-subgoal-p "Subgoal 1"        "Goal")))

(assert-event      (non-subgoal-p "Subgoal 1"        "Subgoal *1/1"))
(assert-event (not (non-subgoal-p "Subgoal *1/1"     "Subgoal 1")))

(assert-event      (non-subgoal-p "Subgoal *2/2"     "Subgoal *1/2"))
(assert-event      (non-subgoal-p "Subgoal *1/2"     "Subgoal *2/2"))

(assert-event      (non-subgoal-p "Goal"             "[1]Goal"))
(assert-event (not (non-subgoal-p "[1]Goal"          "Goal")))

(assert-event (not (non-subgoal-p "Subgoal 1.2"      "Subgoal 1")))
(assert-event      (non-subgoal-p "Subgoal 1"        "Subgoal 1.2"))

(assert-event      (non-subgoal-p "Subgoal 1.3"      "Subgoal 1.2"))


(defun irrelevant-subgoal-p (curr-goal target-goal)
  ;; Returns T if curr-goal is not either a potential ancestor or potential
  ;; descendant of target-goal.
  (and (non-subgoal-p target-goal curr-goal)    ;; Not an ancestor
       (not (subgoalp curr-goal target-goal)))) ;; Not a descendant.
