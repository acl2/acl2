(in-package "ACL2")

#|

  partial-correctness.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Tue Dec 14 09:06:19 2004

Here is an idea of John Matthews that I implement in ACL2. The idea is to drive
assertions (and well-founded measures) at cutpoints, and then ACL2
automatically proves them at the exitpoints if all exitpoints are reachable
from cutpoints.

Note added Thu Oct 6 18:33:10 2005: Lee Pike pointed out problems with my
previous hacks where I was using both arithmetic-2 and
ordinals-without-arithmetic (Thanks, Lee). It seems that the ordinals do not
quite go well with arithmetic-2 (or arithmetic-3) but only with arithmetic. I
have now fixed everything so that such issues are resolved, by just using
ordinals which means ordinals and the arithmetic library. At some point I need
to talk to Pete and Daron and ask them so as to make the ordinals robust so
that they do not depend much on which arithmetic library is included.

|#

(include-book "misc/defpun" :dir :system)
(include-book "ordinals/ordinals" :dir :system)

(defstub nextt (*) => *)
(defun run (s n) (if (zp n) s (run (nextt s) (1- n))))



(encapsulate

 ;; The encapsulation here shows that the user needs to do. Once the user has
 ;; defined the functions below and proven their (exported) properties, the
 ;; main theorem of the book can be automatically proved by functional
 ;; instantiation for the user's program.

 (((cutpoint *) => *)
  ((exitpoint *) => *)
  ((pre *) => *)
  ((assertion *) => *)
  ((post *) => *)
  ((default-state) => *))

 (local (defun cutpoint (s) (equal s nil)))
 (local (defun exitpoint (s) (equal s nil)))
 (local (defun pre (s) (declare (ignore s)) nil))
 (local (defun assertion (s) (declare (ignore s)) nil))
 (local (defun post (s) (declare (ignore s)) nil))
 (local (defun default-state () t))

 ;; The constraints imposed are specified as theorems with names enclosed
 ;; within vertical bars, namely as |some theorem|.

 ;; Note to myself: The constraint below merely specifies that default
 ;; state is not a cutpoint. In some respects this is probably too
 ;; weak. For example there is no reason why one cannot reach a
 ;; cutpoint from that state. I would think that the stronger theorem
 ;; (not (cutpoint (run (default-state) n)) should have been more
 ;; appropriate. But I would like the weaker constraint if that can
 ;; get our job done.

 ;; Actually I have managed to get the proof through without requiring
 ;; the following condition. That is great!

;;  (defthm |default state is not cutpoint|
;;    (equal (cutpoint (default-state))
;;           nil))

 (defthm |every exitpoint is a cutpoint|
   (implies (exitpoint s)
            (cutpoint s))
   :rule-classes :forward-chaining)

 (defthm |precondition implies assertion|
   (implies (pre s)
            (assertion s)))

 (defthm |precondition implies cutpoint|
   (implies (pre s)
            (cutpoint s)))

 (defthm |assertion at exitpoint implies postcondition|
   (implies (and (assertion s)
                 (exitpoint s))
            (post s)))

 ;; The three constraints above guarantee that if somehow we can go
 ;; from one cutpoint to the nextt by maintaining the invariant that
 ;; the assertion holds until we hit the first exitpoint, then the
 ;; first exitpoint must satisfy the postcondition. But how do we go
 ;; from one cutpoint to the nextt? The number of steps to do so has
 ;; been specified by the function steps-to-cutpoint below.


 (defpun steps-to-cutpoint-tail (s i)
   (if (cutpoint s)
       i
     (steps-to-cutpoint-tail (nextt s) (1+ i))))

 (defun steps-to-cutpoint (s)
   (let ((steps (steps-to-cutpoint-tail s 0)))
     (if (cutpoint (run s steps))
         steps
       (omega))))

 ;; (nextt-cutpoint s) is simply the closest cutpoint reachable from s.

 (defun nextt-cutpoint (s)
   (let ((steps (steps-to-cutpoint s)))
     (if (natp steps)
         (run s steps)
       (default-state))))

 ;; Finally the constraint below says that if s is a cutpoint and not
 ;; an exitpoint and it satisfies the assertion then the cutpoint
 ;; reachable from (nextt s) also satisfies the assertion.

 (defthm  |assertion invariant over cutpoints|
   (implies (and (cutpoint s)
                 (not (exitpoint s))
                 (assertion s))
            (assertion (nextt-cutpoint (nextt s)))))
)

;; We start with a collection of definitions. steps-to-exitpoint below
;; is the number of steps to reach the first exitpoint, if one is
;; reachable. Otherwise it is (omega).

(defpun steps-to-exitpoint-tail (s i)
  (if (exitpoint s)
      i
    (steps-to-exitpoint-tail (nextt s) (1+ i))))

(defun steps-to-exitpoint (s)
  (let ((steps (steps-to-exitpoint-tail s 0)))
    (if (exitpoint (run s steps))
        steps
      (omega))))

;; Our first job is to show that (steps-to-cutpoint s) is the minimum
;; distance cutpoint reachable from s.

;; The following induction scheme is useful, as is the collection of events
;; inside the encapsulate below. In the encapsulate I summarize the theorems
;; about steps-to-cutpoint.

(local
 (defun cutpoint-induction (k steps s)
   (if (zp k) (list k steps s)
     (cutpoint-induction (1- k) (1+ steps) (nextt s)))))


(local
 (encapsulate
 ()

;; The following theorem is proven by induction and is about everything that we
;; need to know about steps-to-cutpoint-tail.

 (local
  (defthmd steps-to-cutpoint-tail-inv
    (implies (and (cutpoint (run s k))
                  (natp steps))
             (let* ((result  (steps-to-cutpoint-tail s steps))
                    (cutpoint-steps (- result steps)))
               (and (natp result)
                    (natp cutpoint-steps)
                    (implies (natp k)
                             (<= cutpoint-steps k))
                    (cutpoint (run s cutpoint-steps)))))
    :hints (("Goal"
             :in-theory (enable natp)
             :induct (cutpoint-induction k steps s)))))

 ;; OK, so what do we know about steps-to-cutpoint? That it is either
 ;; a natural number or (omega), and if some cutpoint exits then it is
 ;; a natural number and the minimum number of steps to reach the
 ;; cutpoint.

 (defthm steps-to-cutpoint-is-ordinal
  (implies (not (natp (steps-to-cutpoint s)))
           (equal (steps-to-cutpoint s) (omega)))
  :rule-classes :forward-chaining)

 ;; Notice that most of the theorems I deal with have a free variable in the
 ;; hypothesis. This is unfortunate but necessary. As a result I presume that
 ;; most of the theorems will not be proved by ACL2 automatically but often
 ;; require :use hints.

 (defthm steps-to-cutpoint-is-natp
  (implies (cutpoint (run s k))
           (natp (steps-to-cutpoint s)))
  :rule-classes (:rewrite :forward-chaining :type-prescription)
  :hints (("Goal"
           :use ((:instance steps-to-cutpoint-tail-inv
                            (steps 0))))))

 (defthm steps-to-cutpoint-provide-cutpoint
   (implies (cutpoint (run s k))
            (cutpoint (run s (steps-to-cutpoint s))))
   :hints (("Goal"
            :use ((:instance steps-to-cutpoint-tail-inv
                             (steps 0))))))

 (defthm steps-to-cutpoint-is-minimal
  (implies (and (cutpoint (run s k))
                (natp k))
           (<= (steps-to-cutpoint s)
               k))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance steps-to-cutpoint-tail-inv
                            (steps 0))))))))

(local (in-theory (disable steps-to-cutpoint)))

;; I now prove similar theorems about steps-to-exitpoint. The
;; encapsulate below is a verbatim copy of the one above with
;; cutpoints changed to exitpoints.

(local
 (encapsulate
  ()

;; The following theorem is proven by induction and is about everything that we
;; need to know about steps-to-exitpoint-tail.

 (local
  (defthmd steps-to-exitpoint-tail-inv
    (implies (and (exitpoint (run s k))
                  (natp steps))
             (let* ((result  (steps-to-exitpoint-tail s steps))
                    (exitpoint-steps (- result steps)))
               (and (natp result)
                    (natp exitpoint-steps)
                    (implies (natp k)
                             (<= exitpoint-steps k))
                    (exitpoint (run s exitpoint-steps)))))
    :hints (("Goal"
             :in-theory (enable natp)
             :induct (cutpoint-induction k steps s)))))

 ;; OK, so what do we know about steps-to-exitpoint? That it is either
 ;; a natural number or (omega), and if some exitpoint exits then it is
 ;; a natural number and the minimum number of steps to reach the
 ;; exitpoint.

 (defthm steps-to-exitpoint-is-ordinal
  (implies (not (natp (steps-to-exitpoint s)))
           (equal (steps-to-exitpoint s) (omega)))
  :rule-classes :forward-chaining)

 ;; Notice that most of the theorems I deal with has a free variable
 ;; in the hypothesis. This is unfortunate but necessary. As a result
 ;; I presume that most of the theorems will not be proved by ACL2
 ;; automatically but often require :use hints. This suggests the
 ;; proliferation of such hints in this book. For my first-cut pass at
 ;; this book, I will therefore not even try to remove :use hints but
 ;; just keep a note of them.

 (defthm steps-to-exitpoint-is-natp
  (implies (exitpoint (run s k))
           (natp (steps-to-exitpoint s)))
  :rule-classes (:rewrite :forward-chaining :type-prescription)
  :hints (("Goal"
           :use ((:instance steps-to-exitpoint-tail-inv
                            (steps 0))))))

 (defthm steps-to-exitpoint-provide-exitpoint
   (implies (exitpoint (run s k))
            (exitpoint (run s (steps-to-exitpoint s))))
   :hints (("Goal"
            :use ((:instance steps-to-exitpoint-tail-inv
                             (steps 0))))))

 (defthm steps-to-exitpoint-is-minimal
  (implies (and (exitpoint (run s k))
                (natp k))
           (<= (steps-to-exitpoint s)
               k))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance steps-to-exitpoint-tail-inv
                            (steps 0))))))))

(local
 (in-theory (disable steps-to-exitpoint)))

;; Let us now step back and see what we have got. We know that if
;; there is an exitpoint from s, then (steps-to-exitpoint s) gives the
;; minimum number of steps to reach such an exitpoint. We also know
;; that every exitpoint is a cutpoint, and if once one starts at a
;; cutpoint with assertion then the assertion holds until one hits the
;; first exitpoint by jumping from cutpoint to cutpoint. Well, we
;; start now by simply formalizing the last idea. The function
;; big-step-run below formalizes the idea of "jumping" along
;; cutpoints.

(local
 (defun big-step-run (s k)
   (if (zp k) s
     (big-step-run (nextt-cutpoint (nextt s))
                   (1- k)))))


;; We will use big-step semantics only under the condition that some
;; interesting point (cut or exit) is present after l steps. Thus the
;; function big-step-induction below is an appropriate induction
;; scheme rather than big-step-run itself.

(local
 (defun big-step-induction (s k l)
   (if (zp k) (list s k l)
     (big-step-induction (nextt-cutpoint (nextt s))
                         (1- k)
                         (- l (1+ (steps-to-cutpoint (nextt s))))))))


;; We throw in the theorem that we can normalize run of runs. Note to
;; myself: Notice that I have thrown in a force in the hypothesis of
;; the theorem. This is because I always expect this rule to fire, but
;; (presumably since most rewrite rules in the context have free
;; variables) the rule might not always fire because of problems with
;; relieving hypothesis. I am "forcing" ACL2 to always use the rule so
;; that in the end I can see what hypothesis it could not
;; relieve. This also means that I might have to deal with hints
;; attached to subgoals like look like "[1]Subgoal 1". I will deal
;; with that issue later.

(local
 (defthm run+-reduction
   (implies (force (and (natp m)
                        (natp n)))
            (equal (run (run s m) n)
                   (run s (+ m n))))))

;; The nextt rule is an ugly hack and I am almost doing it assuming I
;; know what I am doing. If I dont use this theorem, the definition of
;; run does not expand in circumstances I want it to. The theorem
;; always expands expressions of the form (run <some state> l) whereas
;; if it is not l the theorem does not fire. My intention here is that
;; when I expect to expand run anyways then I will use l as the second
;; argument of run. Admittedly a pretty dirty hack.

(local
 (defthm run-always-expands
   (implies (syntaxp (equal l 'l))
            (equal (run s l)
                   (if (zp l) s (run (nextt s) (1- l)))))))

;; All right so let's get back to business. My idea of the proof is as
;; follows. If there is an exitpoint reachable from s, then
;; big-step-run finds it. Thus big-step-run finds the first exitpoint
;; reachable from s as well. Let k be the number of steps in which
;; big-step-run finds the first exitpoint. Then running for each l <
;; k, running for l big steps will lead to a state that is not an
;; exitpoint. However, since an exitpoint and hence a cutpoint is
;; reachable, (namely after k big steps), each of these steps must
;; lead to a cutpoint. We should then know that the assertion holds
;; for each of these points (including and up to k). But then running
;; for k steps would take me to an exitpoint which has the assertion,
;; and hence it must satisfy the postcondition!

;; Let us see how to formalize the outline above. We first prove that
;; assertion is invariant over big-step runs until the first exitpoint
;; it encounters. That part of the proof should be pretty simple.

;; The function no-big-exitpoint below specifies that big steps do not
;; encounter an exitpoint up to the first k steps.

(local
 (defun no-big-exitpoint (s k)
   (declare (xargs :measure (nfix k)))
   (if (zp k) (not (exitpoint s))
     (and (not (exitpoint s))
          (no-big-exitpoint (nextt-cutpoint (nextt s)) (1- k))))))

(local
 (defthmd cutpoint-implies-assertion
   (implies (and (cutpoint s)
                 (natp k)
                 (assertion s)
                 (exitpoint (run s l))
                 (no-big-exitpoint s k))
            (assertion (big-step-run s k)))
   :hints (("Goal"
            :induct (big-step-induction s k l))
           ("Subgoal *1/2.1"
            :in-theory (disable |assertion invariant over cutpoints|)
            :use ((:instance |assertion invariant over cutpoints|)))
           ("[1]Goal"
            :in-theory (enable natp)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- l))
                             (s (nextt s)))
                  (:instance steps-to-cutpoint-is-natp
                             (k (1- l))
                             (s (nextt s))))))))

;; The nextt thing to do is to show that the assertions are also true
;; for the nextt step, that is (possibly) the first exitpoint. Why is
;; this true? Well, assertion holds till the last point big steps have
;; seen. Then it should be a simple matter of applying the constrained
;; invariant again. However, to do this, we must know that big-steps
;; is returning a cutpoint, since that is when the assertion can be
;; carried over to the nextt step.

(local
 (defthmd big-step-is-always-a-cutpoint
   (implies (and (cutpoint s)
                 (natp k)
                 (no-big-exitpoint s k)
                 (exitpoint (run s l)))
            (cutpoint (big-step-run s k)))
   :hints (("Goal"
            :induct (big-step-induction s k l))
           ("[1]Goal"
            :in-theory (enable natp)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- l))
                             (s (nextt s)))
                  (:instance steps-to-cutpoint-is-natp
                             (k (1- l))
                             (s (nextt s))))))))

;; Now just apply the above two theorems to get the one we want. Note
;; the

(local
 (encapsulate
  ()

  (local
   (defthm no-exitpoint-means-not-exitpoint
     (implies  (no-big-exitpoint s k)
               (not (exitpoint (big-step-run s k))))))

  (local
   (defthm big-steps-alternate-definition
     (equal (big-step-run s k)
            (if (zp k) s (nextt-cutpoint
                          (nextt (big-step-run s (1- k))))))
    :rule-classes :definition))

 (local
  (in-theory (disable big-step-run)))

 (defthm first-exitpoint-has-assertion-too
   (implies (and (cutpoint s)
                 (assertion s)
                 (natp k)
                 (natp m)
                 (exitpoint (run s m))
                 (no-big-exitpoint s k))
            (assertion (big-step-run s (1+ k))))
    :hints (("Goal"
             :in-theory (disable |assertion invariant over cutpoints|)
             :use ((:instance cutpoint-implies-assertion (l m))
                   (:instance big-step-is-always-a-cutpoint
                              (l m))
                   (:instance |assertion invariant over cutpoints|
                              (s (big-step-run s k)))))))))

;; OK so I have proved that the first exitpoint ever hit by big steps
;; satisfies the assertion. Now the rest of the book I will try to
;; prove that the first exitpoint hit by "little steps" is the same as
;; the first exitpoint hit by big steps. Well, to do this, I define
;; some functions that correspond big step semantics to little step
;; semantics.

(local
 (defun big-steps (s l)
   (declare (xargs :measure (nfix l)
                   :hints (("Goal"
                            :use ((:instance
                                   steps-to-cutpoint-is-ordinal
                                   (s (nextt s))))))))
   (if (zp l) 0
     (1+ (big-steps (nextt-cutpoint (nextt s))
                    (1- (- l (steps-to-cutpoint (nextt s)))))))))

(local
 (defun little-steps (s k)
   (if (zp k) 0
     (+ (1+ (steps-to-cutpoint (nextt s)))
        (little-steps (nextt-cutpoint (nextt s)) (1- k))))))

(local
 (defthm big-steps-is-natp
   (natp (big-steps s l))
   :rule-classes :type-prescription))

(local
 (defthm little-steps-is-natp
   (natp (little-steps s k))
   :rule-classes :type-prescription))

;; OK so let us prove that every cutpoint is big-step-run of some
;; number.

(local
 (defthmd cutpoint-is-hit-by-big-steps
   (implies (and (cutpoint (run s l))
                 (natp l))
            (equal (big-step-run s (big-steps s l))
                   (run s l)))
   :hints (("Goal"
            :induct (big-steps s l))
           ("Subgoal *1/2.3"
            :in-theory (enable natp)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- l))
                             (s (nextt s)))))
           ("[1]Subgoal 1"
            :in-theory (enable natp)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- l))
                             (s (nextt s)))))
           ("[1]Subgoal 2"
            :in-theory (enable natp)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- l))
                             (s (nextt s)))))
           ("[1]Subgoal 3"
            :in-theory (enable natp)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- l))
                             (s (nextt s))))))))

;; OK so we have proved that every reachable cutpoint is hit by big
;; steps. Presumably then, the first exitpoint will also be hit by big
;; steps. Let us prove that and then we will think about the rest.

(local
 (defthmd first-exitpoint-is-hit-by-big-steps
   (implies (exitpoint (run s m))
            (equal (run s (steps-to-exitpoint s))
                   (big-step-run s
                                 (big-steps s (steps-to-exitpoint
                                               s)))))
   :hints (("Goal"
            :in-theory (disable steps-to-exitpoint-provide-exitpoint)
            :use ((:instance cutpoint-is-hit-by-big-steps
                             (l (steps-to-exitpoint s)))
                  (:instance steps-to-exitpoint-provide-exitpoint
                             (k m)))))))

;; Now I know that the first exitpoint is hit by big-step-run. That is
;; great. The nextt thing I need to prove is that every state hit by
;; big-step-run *before* this first exitpoint, must not be an
;; exitpoint. Why is this true? Well, because those states are not
;; exitpoints themselves. This is formalized by the function
;; no-exitpoint below.

(local
 (defun no-exitpoint (s m)
   (declare (xargs :measure (nfix m)))
   (if (zp m) (not (exitpoint s))
     (and (not (exitpoint s))
          (no-exitpoint (nextt s) (1- m))))))

;; Of course a state reachable in <= m steps from s is not an
;; exitpoint from this definition.

(local
 (defthm no-exitpoint-implies-not-exitpoint
   (implies (and (no-exitpoint s m)
                 (natp m)
                 (natp n)
                 (<= n m))
            (not (exitpoint (run s n))))))

;; which in particular means (no-exitpoint s n)

(local
 (defthm no-exitpoint-means-no-exitpoint
   (implies (and (no-exitpoint s m)
                 (natp m)
                 (natp n)
                 (<= n m))
            (no-exitpoint s n))))

;; Plus no exitpoint holds for (run s n) up to (- n m).

(local
 (defthm no-exitpoint-for-run
   (implies (and (no-exitpoint s m)
                 (natp m)
                 (natp n)
                 (<= n m))
            (no-exitpoint (run s n) (- m n)))))

;; Let us now prove that every big step is actually matched by some
;; little steps. How is that useful? Well, the idea is that if we
;; consider some k < m where m is the number of big steps to reach the
;; first exitpoint, then I want to say that (big-step-run s k) is not
;; an exitpoint. How would I say that? I would consider two cases: (a)
;; that state is not a cutpoint. Of course then it is not an
;; exitpoint. Otherwise it is some cutpoint. In that case, I should
;; know that it is reachable by some little steps l < n where k =
;; (big-steps s n). Then I should be able to claim that since n is the
;; first time some exitpoint is seen, the state (big-step-run s k) is
;; not an exitpoint.


(local
 (defthm little-big-inverse
   (implies (and (cutpoint (run s r))
                 (natp r))
            (equal (little-steps s (big-steps s r))
                   r))
   :hints (("Goal"
            :induct (big-steps s r))
           ("Subgoal *1/2.4"
            :in-theory (e/d (natp) (steps-to-cutpoint-is-minimal))
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- r))
                             (s (nextt s)))))
           ("[1]Goal"
            :in-theory (e/d (natp) (steps-to-cutpoint-is-minimal))
            :use ((:instance steps-to-cutpoint-is-minimal
                             (k (1- r))
                             (s (nextt s))))))))

;; OK so we know that little-step is an inverse of big-step as long as
;; we are looking only at a cutpoint. Now let us prove that any number
;; of big steps can be matched by little steps.

(local
 (defthm little-steps-bit-steps
   (implies (zp (little-steps s k))
            (equal (big-step-run s k) s))))

(local
 (defthmd big-steps-is-little-steps
   (implies (and (natp l)
                 (cutpoint (run s l))
                 (<= (little-steps s k) l))
            (equal (big-step-run s k)
                   (run s (little-steps s k))))
   :hints (("Goal"
            :induct (big-step-induction s k l)))))

;; Finally, let us also prove that the notion of little-steps is
;; monotonic with respect to k. Then we will be able to say that if
;; a state is reachable by fewer big steps then it is also reachable
;; by fewer little steps.

(local
 (defthm little-is-monotonic
   (implies (and (natp m) (natp n) (< m n))
            (< (little-steps s m) (little-steps s n)))
   :rule-classes :linear))

;; OK, so we believe we have every little piece. We now want to prove
;; the key technical lemma. This lemma specifies that if we look at a
;; state reached by big steps before the first exitpoint is seen, then
;; it must not be an exitpoint. Why? Let (big-steps s m) be the state
;; reached by big steps for the first exitpoint. Then, (little-steps s
;; (big-steps s m)) must be m, by a previous lemma. Now consider a k <
;; (big-steps s m). Then (little-steps s k) < m. But (run s m) is the
;; first exit point, and hence (run s (little-steps s k)) must not be
;; an exitpoint.

(local
 (defthm big-step-encounters-no-exitpoint
   (implies (and (exitpoint (run s k))
                 (natp m)
                 (natp k)
                 (< m (big-steps s (steps-to-exitpoint s))))
            (not (exitpoint (big-step-run s m))))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :do-not '(eliminate-destructors generalize fertilize)
            :in-theory (disable little-big-inverse
                                big-steps-is-little-steps
                                steps-to-exitpoint-is-minimal
                                little-is-monotonic
                                steps-to-exitpoint-provide-exitpoint)
            :use ((:instance little-big-inverse
                             (r (steps-to-exitpoint s)))
                  (:instance big-steps-is-little-steps
                             (k m)
                             (l (steps-to-exitpoint s)))
                  (:instance little-is-monotonic
                             (n (big-steps s (steps-to-exitpoint s))))
                  (:instance steps-to-exitpoint-is-minimal
                             (k (little-steps s m)))
                  (:instance steps-to-exitpoint-provide-exitpoint))))))

;; OK so I am now done with the bulk of the proof. I have shown that
;; for m < (steps-to-exitpoint s), (big-steps s m) is not an ;;
;; exitpoint. I have also shown that if (no-big-exitpoint s m) holds
;; for a certain number m of steps, then assertion holds for the nextt
;; state. The theorem above guarantees that no-big-exitpoint actually
;; holds for all steps < (big-steps (steps-to-exitpoint s)). But in
;; order to deal with the quantifier-free aspect of ACL2, I need a few
;; more tricks. Notice that I am trying hard here to curb my natural
;; tendencies and just introduce a defun-sk. I dont do it since I dont
;; see that necessary.

;; The trick that I am doing is to define a function falsifier that
;; finds an exitpoint if one exists. Then I know that no such guy
;; exists by the previous theorem.

(local
 (defun falsifier-no-exitpoint (s n)
   (declare (xargs :measure (acl2-count n)))
   (if (zp n) (if (exitpoint s) 0 (omega))
     (if (exitpoint s) 0
       (let ((false (falsifier-no-exitpoint (nextt-cutpoint (nextt s)) (1- n))))
         (if (natp false) (+ 1 false) (omega)))))))

(local
 (defthm falsifier-is-natp-or-omega
   (implies (not (natp (falsifier-no-exitpoint s n)))
            (equal (falsifier-no-exitpoint s n) (omega)))))

(local
 (defthm falsifier-if-natp-is-less-than-n
   (implies (and (natp (falsifier-no-exitpoint s n))
                 (natp n))
            (<= (falsifier-no-exitpoint s n)
                n))
   :rule-classes :linear))

(local
 (defthm falsifier-falsifies-1
   (implies (not (natp (falsifier-no-exitpoint s n)))
            (no-big-exitpoint s n))))

(local
 (defthm falsifier-falsifies-2
   (implies (and (natp (falsifier-no-exitpoint s n))
                 (natp n))
            (exitpoint (big-step-run s (falsifier-no-exitpoint s n))))
   :hints (("Goal"
            :induct (falsifier-no-exitpoint s n)))))

;; Here is the main justification.

(local
 (defthm less-than-exitpoint-implies-no-exitpoint
   (implies (and (exitpoint (run s k))
                 (natp m)
                 (natp k)
                 (< m (big-steps s (steps-to-exitpoint s))))
            (no-big-exitpoint s m))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable falsifier-falsifies-1
                                falsifier-falsifies-2)
            :use ((:instance falsifier-falsifies-1
                             (n m))
                  (:instance falsifier-falsifies-2
                             (n m)))))))


;; At last, here is the final theorem. I am surprised it really took
;; me 5 hours to get this one. But I think I am done now.

(local
 (defthm not-exitpoint-to-steps-natp
   (implies (and (exitpoint (run s n))
                 (not (exitpoint s)))
            (natp (1- (steps-to-exitpoint s))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (natp)
                            (steps-to-exitpoint-is-natp
                             steps-to-exitpoint-provide-exitpoint))
            :use ((:instance steps-to-exitpoint-is-natp (k n))
                  (:instance steps-to-exitpoint-provide-exitpoint
                             (k n)))))))

(local
 (defthm big-steps-is-natp->0
  (implies (force (and (natp n)
                       (> n 0)))
          (natp (1- (big-steps s n))))))


;; The final theorem is a CAPITAL defthm.

(DEFTHM |partial correctness|
  (implies (and (pre s)
                (exitpoint (run s n)))
           (let ((steps (steps-to-exitpoint s)))
             (post (run s steps))))
  :hints (("Goal"
           :cases ((not (natp n)) (exitpoint s)))
          ("Subgoal 1"
           :in-theory (disable steps-to-exitpoint-is-minimal)
           :use ((:instance steps-to-exitpoint-is-minimal (k 0))))
           ("Subgoal 2"
           :in-theory (disable steps-to-exitpoint-is-minimal)
           :use ((:instance steps-to-exitpoint-is-minimal (k 0))))
          ("Subgoal 3"
           :in-theory (disable
                       first-exitpoint-is-hit-by-big-steps
                       |assertion at exitpoint implies postcondition|
                       first-exitpoint-has-assertion-too
                       less-than-exitpoint-implies-no-exitpoint)
           :use ((:instance
                  |assertion at exitpoint implies postcondition|
                  (s (run s (steps-to-exitpoint s))))
                 (:instance first-exitpoint-has-assertion-too
                            (k (1- (big-steps s (steps-to-exitpoint s))))
                            (m n))
                 (:instance first-exitpoint-is-hit-by-big-steps
                            (m n))
                 (:instance less-than-exitpoint-implies-no-exitpoint
                            (k n)
                            (m (1- (big-steps s (steps-to-exitpoint s)))))))))
