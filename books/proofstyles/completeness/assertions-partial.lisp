(in-package "ACL2")

#|

 assertions-partial.lisp
 ~~~~~~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Mon Oct  9 07:06:12 2006


In this book, we explore if the reasoning of a VCG is complete.  In particular,
we are interested in the following question: If a program is partially correct,
is there always a VCG proof showing that it is partially correct?

The answer turns out to be "yes".  To prove this, assume that we have a proof
of partial correctness and also assume that we are given some cutpoints that
include the initial (i.e. pre) and final (i.e. exitpoint) states.  We then show
how to define the assertions so that we can derive the VCG obligations.

|#

(include-book "misc/defpun" :dir :system)
(include-book "ordinals/ordinals" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Constraints for correctness proof and cutpoint definitions   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We assume (without loss of generality) that we have a clock
;; function proof of correctness of the program.  We also assume that
;; we are given a set of cutpoints that include the initial (pre) and
;; final (exitpoint) states.

(include-book "stepwise-invariants-partial")

(encapsulate
 (((cutpoint *) => *))

 (local
  (defun cutpoint (s)
    (or (pre s)
        (exitpoint s))))

 (defthm |pre implies cutpoint|
   (implies (pre s)
            (cutpoint s)))

 (defthm |exitpoint implies cutpoint|
   (implies (exitpoint s)
            (cutpoint s))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2:  Defining the assertions                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; So then what is the assertion that we will want to attach to each cutpoint.
;; The assertion we wish to attach at s is that there exists a pre state p such
;; that this is s is reachable from p and there is no exitpoint in the path
;; from p to s.

;; So I now define what is meant by there is no exitpoint along a path.  The
;; predicate no-exitpoint below says that there is no exitpoint from p within a
;; distance less than n.

;; Then we define the predicate we wanted via quantification.

;; (defun-sk exists-some-exitpoint (s)
;;   (exists alpha (exitpoint (run-fn s alpha))))


(local (in-theory (disable exists-some-exitpoint
                           exists-some-exitpoint-suff)))


;; (defun-sk exists-pre-state (s)
;;   (exists (p m)
;;           (and (pre p)
;;                (natp m)
;;                (equal s (run-fn p m))
;;                (implies (exists-some-exitpoint p)
;;                         (<= m (clock-fn p))))))


;; Here is the definition of assertions.  The only reason why we put the nil
;; case later is because we intend to define the assertions so that it holds
;; only for cutpoints, since that's one of the conditions we propounded in the
;; paper.

(defun assertion (s)
  (if (cutpoint s)
      (inv s)
    nil))



(defpun steps-to-cutpoint-tail (s i)
  (if (cutpoint s)
      i
    (steps-to-cutpoint-tail (step-fn s) (1+ i))))

(defun steps-to-cutpoint (s)
  (let ((steps (steps-to-cutpoint-tail s 0)))
    (if (cutpoint (run-fn s steps))
        steps
      (omega))))

;; (step-fn-cutpoint s) is simply the closest cutpoint reachable from s.

(defchoose default-state (s) ()
  (not (cutpoint s)))


(defun step-fn-cutpoint (s)
  (let ((steps (steps-to-cutpoint s)))
    (if (cutpoint (run-fn s steps))
        (run-fn s steps)
      (default-state))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3:  The crux of the proof                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; OK now we start.  The first theorem is that assertion implies cutpoint.
;; This is trivial, so let me get that out of the way.

(local
 (defthm assertion-implies-cutpoint
  (implies (assertion s) (cutpoint s))))


;; We now do the same proof for clock-fn that we've done over and over
;; again for tail-recursive functions.


(local
 (defun cutpoint-induction (k steps s)
   (if (zp k) (list k steps s)
     (cutpoint-induction (1- k) (1+ steps) (step-fn s)))))


(local
 (defthmd clock-fn-tail-inv
   (implies (and (exitpoint (run-fn s k))
                 (natp steps))
            (let* ((result  (clock-fn-tail s steps))
                   (exitpoint-steps (- result steps)))
              (and (natp result)
                   (natp exitpoint-steps)
                   (implies (natp k)
                            (<= exitpoint-steps k))
                   (exitpoint (run-fn s exitpoint-steps)))))
   :hints (("Goal"
            :induct (cutpoint-induction k steps s)))))

;; (local
;;  (defthm clock-fn-is-ordinal
;;    (implies (not (natp (clock-fn s)))
;;             (equal (clock-fn s) (omega)))
;;    :rule-classes :forward-chaining))


(local
 (defthm clock-fn-is-natp
   (implies (exitpoint (run-fn s k))
            (natp (clock-fn s)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal"
            :use ((:instance clock-fn-tail-inv
                             (steps 0)))))))

(local
 (defthm clock-fn-provide-exitpoint
   (implies (exitpoint (run-fn s k))
            (exitpoint (run-fn s (clock-fn s))))
   :hints (("Goal"
            :use ((:instance clock-fn-tail-inv
                             (steps 0)))))))

(local
 (defthm clock-fn-is-minimal
   (implies (and (exitpoint (run-fn s k))
                 (natp k))
            (<= (clock-fn s)
                k))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance clock-fn-tail-inv
                            (steps 0)))))))

(local (in-theory (disable clock-fn)))


;; The other condition is that if s is a pre state then assertion must hold for
;; s.  This is easy to prove from the definition of assertion above.  The only
;; real trick to to see why (clock-fn s) >= 0.  The reason is that it
;; is either a natural number or omega.  And this quantity is >= 0.

(local (in-theory (disable inv inv-suff)))

(local
 (defthm pre-s-implies-inv
   (implies (pre s)
            (inv s))
   :hints (("Goal"
            :in-theory (disable inv-suff)
            :use ((:instance  inv-suff
                              (p s)
                              (m 0))
                  (:instance (:definition exists-some-exitpoint))
                  (:instance clock-fn-is-natp
                             (k (exists-some-exitpoint-witness s))))))))

(local
 (defthm pre-implies-assertion
   (implies (pre s) (assertion s))
   :hints (("Goal"
            :in-theory (disable inv)))))



;; Now we are going to prove the more interesting VCG theorems from this
;; definition of the assertions.  In particular, we need to show that if an
;; exitpoint satisfies assertions then it also implies the postcondition, and
;; if a non-exit cutpoint satisfies assertion then the assertions also hold for
;; the step-fn cutpoint.  We start with the first one.  So why do we believe this?
;; Here is an informal argument.  Since the assertions hold at an exitpoint s,
;; there must be a pre state p from which s is reachable and no exitpoint is
;; encountered in the path from p to s.  Therefore s = (step-fn-exitpoint p).
;; Hence the theorem holds from the condition for partial correectness.



;; The following theorem is proven by induction and is about everything that we
;; need to know about steps-to-cutpoint-tail.

(local
 (defthmd steps-to-cutpoint-tail-inv
   (implies (and (cutpoint (run-fn s k))
                 (natp steps))
            (let* ((result  (steps-to-cutpoint-tail s steps))
                   (cutpoint-steps (- result steps)))
              (and (natp result)
                   (natp cutpoint-steps)
                   (implies (natp k)
                            (<= cutpoint-steps k))
                   (cutpoint (run-fn s cutpoint-steps)))))
   :hints (("Goal"
            ;; :in-theory (enable natp)
            :induct (cutpoint-induction k steps s)))))

 ;; OK, so what do we know about steps-to-cutpoint? That it is either
 ;; a natural number or (omega), and if some cutpoint exits then it is
 ;; a natural number and the minimum number of steps to reach the
 ;; cutpoint.

(local
 (defthm steps-to-cutpoint-is-ordinal
   (implies (not (natp (steps-to-cutpoint s)))
            (equal (steps-to-cutpoint s) (omega)))
   :rule-classes :forward-chaining))

;; Notice that most of the theorems I deal with have a free variable in the
;; hypothesis. This is unfortunate but necessary. As a result I presume that
;; most of the theorems will not be proved by ACL2 automatically but often
;; require :use hints.

(local
 (defthm steps-to-cutpoint-is-natp
   (implies (cutpoint (run-fn s k))
            (natp (steps-to-cutpoint s)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal"
            :use ((:instance steps-to-cutpoint-tail-inv
                             (steps 0)))))))

(local
 (defthm steps-to-cutpoint-provide-cutpoint
   (implies (cutpoint (run-fn s k))
            (cutpoint (run-fn s (steps-to-cutpoint s))))
   :hints (("Goal"
            :use ((:instance steps-to-cutpoint-tail-inv
                             (steps 0)))))))

(local
 (defthm steps-to-cutpoint-is-minimal
   (implies (and (cutpoint (run-fn s k))
                 (natp k))
            (<= (steps-to-cutpoint s)
                k))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance steps-to-cutpoint-tail-inv
                            (steps 0)))))))

(local (in-theory (disable steps-to-cutpoint)))


;; So now we know the requisite properties of clock-fn and
;; steps-to-cutpoint, together with the fact that every exitpoint is a
;; cutpoint.  We now dive into the proof of the fact that if the assertion
;; holds and we are at an exitpoint then the postcondition holds too.  Now to
;; prove this we must show that the exitpoint satisfying the assertion is the
;; (unique) step-fn-exitpoint of the witnessing pre state.

(local
 (defthmd exitpoint-implies-s=step-fn-exitpoint
   (implies (and (equal s (run-fn p n))
                 (natp n)
                 (exitpoint s)
                 (<= n (clock-fn p)))
            (equal (clock-fn p) n))))

(local
 (defthm exitpoint-and-assertion-implies-post
   (implies (and (exitpoint s)
                 (assertion s))
            (post s))
   :otf-flg t
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize fertilize)
           :in-theory (disable |clock fn produces postcondition|
                               |clock fn produces exitpoint|)
           :use ((:instance |clock fn produces exitpoint|
                            (s (car (inv-witness s)))
                            (n (mv-nth 1 (inv-witness s))))))
          ("Subgoal 1"
           :use ((:instance (:definition inv))))
          ("Subgoal 2"
           :use ((:instance |clock fn produces postcondition|
                            (s (car (inv-witness s)))
                            (n (mv-nth 1 (inv-witness
                                          s))))
                 (:instance (:definition inv))))
          ("Subgoal 2.4.1"
           :use ((:instance
                  exists-some-exitpoint-suff
                  (s (car (inv-witness s)))
                  (alpha (mv-nth 1 (inv-witness s))))
                 (:instance (:definition inv))))
          ("Subgoal 2.4.2"
           :use ((:instance
                  clock-fn-is-natp
                  (s (car (inv-witness s)))
                  (k (mv-nth 1 (inv-witness s))))
                 (:instance exitpoint-implies-s=step-fn-exitpoint
                            (p (car (inv-witness s)))
                            (n (mv-nth 1 (inv-witness s))))))
          ("Subgoal 3"
           :use ((:instance (:definition inv)))))))

;; The only theorem that is left is that if the assertion holds for a state s
;; that is not an exitpoint then it holds for the step-fn-cutpoint of s.  That
;; will finish the VCG proof since these are the only proof obligations for a
;; VCG (in case of partial correctness).  Now what do we need to prove? We need
;; to prove that if there is some pre state p before s then there must be some
;; pre state p' before (step-fn-cutpoint (step-fn s)).  To prove this, we need some
;; theorems about clock-fn.  In particular, we need to prove that if
;; n< (clock-fn p) and (run-fn p n) is a non-exit cutpoint, then n <=
;; (+ (clock-fn p) 1 (steps-to-cutpoint (step-fn (run-fn p n))).  To do all
 ;; this, we first need the following trivial property of run-fn, which I've
 ;; probably proved many many times.

(local
 (defun execute-fn (s n)
   (if (zp n) s (execute-fn (step-fn s) (1- n)))))

(local
 (defthm execute-fn=run-fn
   (equal (run-fn s n) (execute-fn s n))))

(local
 (defthm run-fn-+-reduction
   (implies (and (natp m)
                 (natp n))
            (equal (run-fn (run-fn s m) n)
                   (run-fn s (+ m n))))))

(local (in-theory (disable execute-fn=run-fn)))

;; Now we will use this theorem to compose run-fns.  We will need several
;; auxiliary lemmas.  First we prove that if s is not an exitpoint and if n < 1
;; + (steps-to-cutpoint (step-fn s)) then (run-fn s n) is not an exitpoint.  This is
;; easy since we know that there is no cutpoint (and hence no exitpoint)
;; between s and (step-fn-cutpoint (step-fn s)).

(local
 (defthmd not-exitpoint-implies-not-exitpoint-+cutpoint
   (implies (and (not (exitpoint s))
                 (< n (1+ (steps-to-cutpoint (step-fn s)))))
            (not (exitpoint (run-fn s n))))
   :hints (("Goal"
            :in-theory (disable steps-to-cutpoint-is-minimal)
            :use ((:instance steps-to-cutpoint-is-minimal
                             (s (step-fn s))
                             (k (1- n))))))))

;; Now we essentially lift this lemma for run-fn.  In other words we prove that if
;; we have not reached an exitpoint from p (think of p as the witnessing pre
;; state of s) then we will not see any exitpoint until the step-fn cutpoint of s.

(local
 (defthm clock-fn-steps-to-cutpoint
   (implies (and (natp m)
                 (< m (clock-fn p))
                 (natp n)
                 (< n (+ m 1 (steps-to-cutpoint (step-fn (run-fn p m))))))
            (not (exitpoint (run-fn p n))))
   :hints (("Goal"
            :in-theory (disable run-fn)
            :cases ((<= n m)))
           ("Subgoal 2"
            :in-theory (disable clock-fn-is-minimal run-fn)
            :use ((:instance not-exitpoint-implies-not-exitpoint-+cutpoint
                             (s (run-fn p m))
                             (n (- n m)))
                  (:instance clock-fn-is-minimal
                             (s p)
                             (k m)))))))



;; Now we put all of these together to prove the key lemma.  The lemma says
;; that (clock-fn p) must be larger than the distance from p to the
;; step-fn cutpoint of s.  This is because we know that there is no exitpoint in
;; between and so (and since there is some exitpoint from p)
;; (clock-fn p) must be encountered later in the execution.

(local
 (defthm clock-fn-larger-than-steps-to-cutpoint
   (implies (and (natp m)
                 (< m (clock-fn p))
                 (exitpoint (run-fn p n))
                 (not (exitpoint (run-fn p m))))
            (<= (+ m 1 (steps-to-cutpoint (step-fn (run-fn p m))))
                (clock-fn p)))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (disable clock-fn-steps-to-cutpoint)
            :use ((:instance clock-fn-steps-to-cutpoint
                             (n (clock-fn p))))))))



;; The following two lemmas are just little technicalities.  They just show how
;; to normalize run-fn expressions and proves that the step-fn-cutpoint of (step-fn s)
;; are cutpoints.  The second is necessary to show that (steps-to-cutpoint
;; (step-fn s)) is natp.

(local
 (defthm step-fn-run-fn-=-run-fn-1+
   (implies (natp m)
            (equal (step-fn (run-fn s m))
                   (run-fn s (1+ m))))
   :hints (("Goal"
            :in-theory (enable execute-fn=run-fn)))))


(local
 (defthm exitpoint-and-not-exitpoint-implies-cutpoint
   (implies (and (exitpoint (run-fn s k))
                 (not (exitpoint s)))
            (cutpoint (run-fn (step-fn s) (steps-to-cutpoint (step-fn s)))))
   :hints (("Goal"
            :in-theory (disable steps-to-cutpoint-provide-cutpoint)
            :use ((:instance steps-to-cutpoint-provide-cutpoint
                             (k (1- k))
                             (s (step-fn s))))))))


;; And here we prove this natp property.

(local
 (defthmd exitpoint-and-not-exitpoint-implies-natp
   (implies (and (exitpoint (run-fn s k))
                 (not (exitpoint s)))
            (natp (steps-to-cutpoint (step-fn s))))
   :hints (("Goal"
            :in-theory (disable steps-to-cutpoint-is-natp)
            :use ((:instance steps-to-cutpoint-is-natp
                             (s (step-fn s))
                             (k (1- k))))))))


;; Now we can of course just lift the whole thing up to a run-fn function.  We do
;; so since our assertions always essentially require us to prove a theorem in
;; terms of run-fn.

(local
 (defthmd <=-steps-implies-step-fn-cutpoint-natp
   (implies (and (natp m)
                 (exitpoint (run-fn p n))
                 (< m (clock-fn p)))
            (natp (steps-to-cutpoint (step-fn (run-fn p m)))))
   :hints (("Goal"
            :in-theory (disable run-fn-+-reduction)
            :use ((:instance run-fn-+-reduction
                             (s p)
                             (n (- (clock-fn p) m))
                             (m m))
                  (:instance exitpoint-and-not-exitpoint-implies-natp
                             (k (- (clock-fn p) m))
                             (s (run-fn p m))))))))


(local (in-theory (disable run-fn)))

;; This theorem is a kind of stupid theorem.  The reason we need this forward
;; chaining rule is the theorem assertion-implies-assertion-step-fn where we are
;; hitting a free variable n.  I don't use it as a rewrite rule because of free
;; variables.

(local
 (defthm exitpoint-and-not-exitpoint-implies-n-natp
   (implies (and (not (exitpoint s))
                 (exitpoint (run-fn s n)))
            (natp n))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (enable run-fn)))))


(local
 (defthmd run-fn-step-fn-=-run-fn-1+
   (implies (natp n)
            (equal (run-fn (step-fn s) n)
                   (run-fn s (1+ n))))
   :hints (("Goal"
           :in-theory (enable run-fn)))))


;; Finally we are done.  This has a huge collection of hints since I like to
;; instantiate quantifiers carefully.  But the main thigs have been proven
;; before.  What we do is we case-plit on whether there is any transition left
;; before (clock-fn p) is hit.  If not, then we can get contradictory
;; hypothesis since we know that we are not at an exitpoint.  If yes, then we
;; can simply use the previous theorems showing that there must be a pre-state
;; (namely p itself) which can serve as the witness to the assertion for the
;; step-fn cutpoint.

(local
 (defthm assertion-implies-assertion-step-fn
   (implies (and (assertion s)
                 (exitpoint (run-fn s n))
                 (not (exitpoint s)))
            (assertion (step-fn-cutpoint (step-fn s))))
   :hints (("Goal"
            :do-not '(eliminate-destructors generalize fertilize)
            :do-not-induct t
            :in-theory (disable inv-suff (force)
                                clock-fn-provide-exitpoint
                                run-fn-+-reduction
                                inv)
            :cases ((< (mv-nth 1 (inv-witness s))
                       (clock-fn
                        (car (inv-witness s))))))
           ("Subgoal 2"
            :use ((:instance inv)
                  (:instance clock-fn-provide-exitpoint
                             (s (car (inv-witness s)))
                             (k (+ (mv-nth 1 (inv-witness s))
                                   n)))
                  (:instance run-fn-+-reduction
                             (s (car (inv-witness s)))
                             (m (mv-nth 1 (inv-witness s)))
                             (n n))))
           ("Subgoal 2.3.1"
           :use ((:instance
                  exists-some-exitpoint-suff
                  (s (car (inv-witness s)))
                  (alpha (+ N
                            (MV-NTH 1 (INV-WITNESS S)))))
                 (:instance (:definition inv))))

           ("Subgoal 1"
            :use ((:instance inv)
                  (:instance inv-suff
                             (p (car (inv-witness s)))
                             (m (+ (mv-nth 1 (inv-witness s))
                                   1
                                   (steps-to-cutpoint (step-fn s))))
                             (s (run-fn (step-fn s) (steps-to-cutpoint (step-fn s)))))
                  (:instance clock-fn-larger-than-steps-to-cutpoint
                             (p (car (inv-witness s)))
                             (n (+ N (mv-nth 1
                                             (inv-witness s))))
                             (m (mv-nth 1 (inv-witness s))))
                  (:instance run-fn-step-fn-=-run-fn-1+
                             (n (steps-to-cutpoint (step-fn s))))
                  (:instance exitpoint-and-not-exitpoint-implies-natp
                             (k n))
                  (:instance run-fn-+-reduction
                             (s (car (inv-witness s)))
                             (m (mv-nth 1 (inv-witness s)))
                             (n (1+ (steps-to-cutpoint (step-fn s)))))))
           ("Subgoal 1.4"
            :use ((:instance run-fn-+-reduction
                             (s (car (inv-witness s)))
                             (m (mv-nth 1 (inv-witness s)))))))))



;; OK so we are done.  We disable all the definitions since we have proved
;; everything.

(local (in-theory (disable assertion step-fn-cutpoint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4:  The final theorems                                          ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In this section we just recapitulate all the proofs we have done before so
;; that everything is in one place.  All the theorems should go through without
;; hints since we have already proven the theorems.

(defthm |pre implies assertion|
  (implies (pre s) (assertion s)))

(defthm |assertion implies cutpoint|
  (implies (assertion s) (cutpoint s)))

(defthm |exitpoint and assertion implies post|
  (implies (and (exitpoint s)
                (assertion s))
           (post s)))

(defthm |assertion and not exitpoint implies assertion|
  (implies (and (assertion s)
                (not (exitpoint s))
                (exitpoint (run-fn s n)))
           (assertion (step-fn-cutpoint (step-fn s)))))
