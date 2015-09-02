(in-package "ACL2")

;;; RBK: Names such as next, run, and modify-main are much to valuable
;;; to be used here, so I changed them.  This was done blindly with
;;; emacs, so may be overly aggressive in some places

#||

 extended-partial-correctness.lisp
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Fri Aug 11 14:49:55 2006

This book is a part of a two-book series to develop a generic theory that
allows us to compose partial correctness proofs efficiently.  Here I briefly
discuss the problem and the solution.

  [Uninteresting aside: I use mathematical notations rather than Lisp in the
   description below as much as possible since emacs gets confused about syntax
   highlighting if I use s-expressions in a comment that is delineated by a
   "block comment" rather than a "line comment".]

The Problem (and some Background)
---------------------------------

Recall that a partial correctness proof looks like the following:

o   pre(s) /\ exists-exitpoint (s) => run(s,clock(s)) = modify(s)

Assume that we have proven this theorem about a subroutine Q, and we now are
interested in proving the correctness of some caller P of Q.  While verifying P
we want to of course not re-verify Q but reuse the work in its verification by
making use of the correctness theorem above.  More concretely, consider using
the cutpoint methodology (and the inductive assertions method) to prove the
correctness of P.  The crucial step in the method is to prove the following
theorem:


o  cut(s) /\ assert(s) /\ exists-cut (s) => assert(nextc(next(s)))

In defsimulate this was proven by just symbolically simulating the machine from
each cutpoint until the next cutpoint is reached.  But the process might cause
repeated symbolic simulation of an already verified subroutine Q.  We prefer
instead to invoke the correctness theorem of Q when symbolic simulation
encounters an invocation of Q.  That is, consider symbolically simulating the
machine starting from a cutpoint s of P.  When we encounter a state s'
involving an invocation of Q, we want to then look for the next cutpoint of s
from the state modify s.

It would have been nice if we could have proven a theorem of the form pre-Q(s)
=> nextc-p(s) = nextc-p(modify(s)).  Unfortunately, given the definition of
nextc (in partial-correctness.lisp and total-correctness.lisp) and the
correctness of Q above, this is not a theorem when Q is proven partially
correct.  The theorem is something like:

o  pre-Q(s) /\ exists-exitpoint-Q (s) => nextc-p (s) = nextc-p (modify (s))

But now we get into trouble.  We want to do the symbolic simulation in order to
prove the persistence of assertions over cutpoints.  In that context we know
exists-cut (s) for each cutpoint s of P (from the hypothesis of the theorem we
want to prove).  This hypothesis, together with some hypothesis of the
well-formedness of the subroutine Q, will be sufficient to derive
exists-exitpoint-Q (s) and hence apply the subroutine correctness theorem
above.  But we do not know exists-cut (s) for the state s that is poised at the
invocation of Q.  Rather, we know it only at the previous cutpoint before the
invocation.  Of course by "construction" we know that (a) the hypothesis was
there for a previous state, and (b) no cutpoint was encountered from that
previous state to the invocation point; therefore the hypothesis must be true
for the invocation point.  But to apply this argument we need either some
memoizing term simplifier that memoizes each of the intermediate symbolic
states (and the fact that exists-cutpoint holds for each of those), which of
course, ACL2 is not, or we must symbolically simulate the machine twice, once
for actually proving the inductive assertions and the other for advancing the
exists-cutpoint predicate, the second being a completely unnecessary one).  In
a previous version of these books, I had managed to get rid of the double
simulation by creating a number of cludges involving the use of hide.  But such
optimizations are purely ACL2-specific and no more than "dirty hacks".  The
challenge therefore is to solve the problem in a clean way.

|#


(include-book "misc/defp" :dir :system)
;;; RBK: try different ordinal books, to prevent problems with
;;; arithmetic-5 compatibility.
(include-book "ordinals/limits" :dir :system)
(in-theory (disable o< o+ o- o* o^))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(encapsulate
 (((epc-next *) => *)
  ((epc-in-sub *) => *)
  ((epc-pre-sub *) => *)
  ((epc-modify-sub *) => *)
  ((epc-pre-main *) => *)
  ((epc-cutpoint-main *) => *)
  ((epc-in-main *) => *)
  ((epc-modify-main *) => *)
  ((epc-assertion-main * *) => *))


 (local (defun epc-next (s) s))
 (defun epc-run (s n) (if (zp n) s (epc-run (epc-next s) (1- n))))

 (local (defun epc-in-sub (s) (declare (ignore s)) nil))
 (local (defun epc-pre-sub (s) (declare (ignore s)) nil))
 (local (defun epc-modify-sub (s) s))
 (defun-sk epc-exists-exitpoint-sub (s) (exists n (not (epc-in-sub (epc-run s n)))))

 (defp epc-steps-to-exitpoint-tail-sub (s i)
   (if (not (epc-in-sub s))
       i
     (epc-steps-to-exitpoint-tail-sub (epc-next s) (1+ i))))

 (defun epc-steps-to-exitpoint-sub (s)
   (let ((steps (epc-steps-to-exitpoint-tail-sub s 0)))
     (if (not (epc-in-sub (epc-run s steps)))
         steps
       (omega))))

 (defun epc-next-exitpoint-sub (s) (epc-run s (epc-steps-to-exitpoint-sub s)))

 (defthm |correctness of epc-sub|
   (implies (and (epc-pre-sub s)
                 (epc-exists-exitpoint-sub s))
            (equal (epc-next-exitpoint-sub s)
                   (epc-modify-sub s))))

 (local (defun epc-pre-main (s) (declare (ignore s)) nil))
 (local (defun epc-in-main (s) (declare (ignore s)) t))
 (local (defun epc-cutpoint-main (s) (declare (ignore s)) nil))
 (local (defun epc-assertion-main (s0 s) (declare (ignore s0 s)) nil))
 (local (defun epc-modify-main (s) s))

 (defp epc-next-epc-cutpoint-main (s)
   (if (or (epc-cutpoint-main s)
           (not (epc-in-main s)))
       s
     (epc-next-epc-cutpoint-main (if (epc-pre-sub s) (epc-modify-sub s) (epc-next s)))))

 (defun-sk exists-epc-next-cutpoint (s) (exists n (epc-cutpoint-main (epc-run s n))))

 (defthm |no main cutpoint in epc-sub|
   (implies (epc-in-sub s)
            (not (epc-cutpoint-main s))))

 (defthm |epc-in-main implies in epc-sub|
   (implies (epc-in-sub s)
            (epc-in-main s)))

 (defthm |epc-pre-sub is epc-in-sub|
   (implies (epc-pre-sub s) (epc-in-sub s)))


 ;; Here we add all the other constraints on assertions.

 (defthm |epc-assertion implies cutpoint|
   (implies (epc-assertion-main s0 s)
            (or (epc-cutpoint-main s)
                (not (epc-in-main s))))
   :rule-classes :forward-chaining)

 (defthm |epc-pre main implies assertion|
   (implies (epc-pre-main s)
            (epc-assertion-main s s)))

 (defthm |epc-assertion main implies post|
   (implies (and (epc-assertion-main s0 s)
                 (not (epc-in-main s)))
            (equal s (epc-modify-main s0)))
   :rule-classes nil)

 (defthm |epc-assertions for cutpoint definition|
   (implies (and (epc-assertion-main s0 s)
                 (epc-in-main s)
                 (not (epc-in-main (epc-run s n))))
            (epc-assertion-main s0 (epc-next-epc-cutpoint-main (epc-next s)))))
)

(local
 (defthm |definition of epc-next cutpoint|
   (equal (epc-next-epc-cutpoint-main s)
          (if (epc-pre-sub s)
              (epc-next-epc-cutpoint-main (epc-modify-sub s))
            (if (or (epc-cutpoint-main s)
                    (not (epc-in-main s)))
                s
              (epc-next-epc-cutpoint-main (epc-next s)))))
  :rule-classes :definition))


;; OK, so we need to prove that from the above we can prove the same
;; assertions-invariant theorem for the epc-next-cutpoint definition that we are
;; used to in partial correctness.  That will let us reuse the
;; partial-correctness result.

;; [ Maybe it is worth thinking whether we want to just use the above definition
;;   of epc-next-cutpoints for proving partial correctness theorem in the generic
;;   theory.  The reason why I do not do that is because the above definition only
;;   works for partial correctness, not total correctness.  Why?  Because for
;;   total correctness we need to know that the epc-next-cutpoint is a reachable
;;   state, and we do not have the extra hypothesis that some cutpoint is
;;   reachable.  But suppose no cutpoint is actually reachable from state s.  The
;;   above definition of epc-next-cutpoint may still produce a cutpoint (the
;;   definition is tail-recursive and we do not know what the definition produces
;;   when no cutpoint is reachable) and the cutpoint-measure of that cutpoint
;;   might even decrease, but that does not guarantee total correctness (since no
;;   cutpoint is reachable from a state, and hence no exitpoint).  And I just
;;   preferred to have the same "golden" definition of epc-next-cutpoint rather than
;;   two different ones.  So I just use this definition as a proof rule in order
;;   to compositionally prove partial correctness or more precisely, the original
;;   assertion-invariant theorem. ]

;; OK so we first introduce the original cutpoint definition.

(local (defstub default-aux-epc-state () => *))

(local
 (defp o-steps-to-cutpoint-tail-main (s i)
   (if (or (epc-cutpoint-main s)
           (not (epc-in-main s)))
       i
     (o-steps-to-cutpoint-tail-main (epc-next s) (1+ i)))))

(local
 (defun o-steps-to-epc-cutpoint-main (s)
   (let ((steps (o-steps-to-cutpoint-tail-main s 0)))
     (if (or (epc-cutpoint-main (epc-run s steps))
             (not (epc-in-main (epc-run s steps))))
         steps
       (omega)))))

 ;; (epc-next-state-cutpoint s) is simply the closest cutpoint reachable from s.

(local
 (defun o-epc-next-epc-cutpoint-main (s)
   (let ((steps (o-steps-to-epc-cutpoint-main s)))
     (if (natp steps)
         (epc-run s steps)
       (default-aux-epc-state)))))

;; OK we need to deal with both forms of epc-next-cutpoint definition.  To do this,
;; I first prove the standard theorem about epc-steps-to-exitpoint-sub.

(local
 (defun cutpoint-induction (k steps s)
   (if (zp k) (list k steps s)
     (cutpoint-induction (1- k) (1+ steps) (epc-next s)))))

(local
 (encapsulate
  ()

  (local
   (defthmd steps-to-exitpoint-tail-inv
     (implies (and (not (epc-in-sub (epc-run s k)))
                   (natp steps))
              (let* ((result  (epc-steps-to-exitpoint-tail-sub s steps))
                     (exitpoint-steps (- result steps)))
                (and (natp result)
                     (natp exitpoint-steps)
                     (implies (natp k)
                              (<= exitpoint-steps k))
                     (not (epc-in-sub (epc-run s exitpoint-steps))))))
     :hints (("Goal"
              :in-theory (enable natp)
              :induct (cutpoint-induction k steps s)))))

 (defthm steps-to-exitpoint-is-ordinal
  (implies (not (natp (epc-steps-to-exitpoint-sub s)))
           (equal (epc-steps-to-exitpoint-sub s) (omega)))
  :rule-classes :forward-chaining)

 ;; Notice that most of the theorems I deal with has a free variable in the
 ;; hypothesis. This is unfortunate but necessary.  As a result I presume that
 ;; most of the theorems will not be proved by ACL2 automatically but often
 ;; require :use hints.  This is the reason for the proliferation of such hints
 ;; in this book.

 (defthm steps-to-exitpoint-is-natp
   (implies (not (epc-in-sub (epc-run s k)))
            (natp (epc-steps-to-exitpoint-sub s)))
  :rule-classes (:rewrite :forward-chaining :type-prescription)
  :hints (("Goal"
           :use ((:instance steps-to-exitpoint-tail-inv
                            (steps 0))))))

 (defthm steps-to-exitpoint-provide-exitpoint
   (implies (not (epc-in-sub (epc-run s k)))
            (not (epc-in-sub (epc-run s (epc-steps-to-exitpoint-sub s)))))
   :hints (("Goal"
            :use ((:instance steps-to-exitpoint-tail-inv
                             (steps 0))))))

 (defthm steps-to-exitpoint-is-minimal
  (implies (and (not (epc-in-sub (epc-run s k)))
                (natp k))
           (<= (epc-steps-to-exitpoint-sub s)
               k))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance steps-to-exitpoint-tail-inv
                            (steps 0))))))))

(local
 (in-theory (disable epc-steps-to-exitpoint-sub)))


;; The key thing that I am going to prove is that if some cutpoint is reachable
;; from s, then epc-next-epc-cutpoint-main is the same as o-epc-next-epc-cutpoint-main.  That
;; will imply the theorem since we know some cutpoint is reachable from s as
;; the hypothesis of our desired theorem.  Now to prove this above fact, what
;; I'll do is essentially say that if some cutpoint is reachable then both
;; definitions give the minimum reachable cutpoint from s.  As such from
;; minimality they must be equal.  So the trick is to relate the new definition
;; of epc-next-cutpoint with some form of definition of steps-to-cutpoint.

;; This is a feedback lemma (that is, proven after I saw ACL2 could not reduce
;; o< to <).  This lemma should really be in the ordinal books, and is one of
;; the most obvious application of ordinals.

(local
 (defthm natp-implies-o<=<
   (implies (and (natp x)
                 (natp y))
            (equal (o< x y)
                   (< x y)))
   :hints (("Goal"
            :in-theory (enable o<)))))

;; We now prove that exitsteps indeed takes you to an exitpoint of the
;; subroutine.  This might have been better to be put in the encapsulation,
;; with the other properties, but it is so trivial that it does not matter.

(local
 (defthmd exitsteps-natp-implies-not-in
   (implies (natp (epc-steps-to-exitpoint-sub s))
            (not (epc-in-sub (epc-run s (epc-steps-to-exitpoint-sub s)))))
  :hints (("Goal"
           :in-theory (e/d (epc-steps-to-exitpoint-sub)
                           (epc-steps-to-exitpoint-tail-sub$def))))))

;; Notice that the above theorem does not take care of the 0 case, for a subtle
;; reason.  The subtle reason is that when (epc-steps-to-exitpoint-sub s) is 0, we
;; want the epc-run term to collapse to s, and that does not unify.  So we add
;; another lemma.

(local
 (defthm exitsteps-0-implies-not-in
   (implies (equal 0 (epc-steps-to-exitpoint-sub s))
            (not (epc-in-sub s)))
   :hints (("Goal"
            :use exitsteps-natp-implies-not-in))))

;; Now we define the induction function for compositional reasoning.  The
;; induction here is just a generalization of cutpoint-induction.  In
;; particular, we just add another case in which the control is poised to be at
;; the entry-point of the subroutine.  Notice that the induction function is
;; not easy to admit.

(local
 (defun comp-cutpoint-induction (s k)
   (declare
    (xargs
     :measure (nfix k)
     :hints (("Subgoal 1.1"
              :in-theory (disable |epc-pre-sub is epc-in-sub|
                                  steps-to-exitpoint-is-natp)
              :use ((:instance |epc-pre-sub is epc-in-sub|)
                    (:instance steps-to-exitpoint-is-natp
                               (k (epc-exists-exitpoint-sub-witness s))))))))

  (if (zp k) (list s k)
    (if (and (epc-pre-sub s) (epc-exists-exitpoint-sub s))
        (comp-cutpoint-induction (epc-modify-sub s)
                            (- k (epc-steps-to-exitpoint-sub s)))
      (comp-cutpoint-induction (epc-next s) (1- k))))))


;; The epc-next important concept is that of no-cutpoint.  This says that there is
;; no cutpoint in less than n steps from s.  This definition is used to define
;; the first reachable cutpoint from s (if one exists).

(local
 (defun no-cutpoint (s n)
   (if (zp n) t
     (let* ((n (1- n)))
       (and (not (or (epc-cutpoint-main (epc-run s n))
                     (not (epc-in-main (epc-run s n)))))
            (no-cutpoint s n))))))

;; Now we prove that no-cutpoint indeed implies there is no cutpoint.

(local
 (defthm no-cutpoint-implies-not-cutpoint
   (implies (and (no-cutpoint s n)
                 (natp n)
                 (natp k)
                 (< k n))
            (and (epc-in-main (epc-run s k))
                 (not (epc-cutpoint-main (epc-run s k)))))
   :hints (("Goal"
            :induct (no-cutpoint s n)
            :do-not-induct t))))


;; Now for the converse of the theorem above.  We have to prove that if there
;; is no cutpoint reachable in less than n steps then no-cutpoint holds.  We do
;; that by the standard trick of defining the witnessing cutpoint if
;; no-cutpoint does not hold.  This is a standard and (I believe) well
;; documented trick with ACL2.

(local
 (defun no-cutpoint-witness (s n)
   (if (zp n) 0
     (if (or (epc-cutpoint-main (epc-run s n))
             (not (epc-in-main (epc-run s n))))
         n
       (no-cutpoint-witness s (1- n))))))

;; After defining the witness function we now need to prove these epc-next couple
;; of theorems.  These theorems are obvious ones, and easily provable by
;; induction.

(local
 (defthm cutpoint-implies-no-cut-2
   (implies (and (not (epc-cutpoint-main (epc-run s (no-cutpoint-witness s n))))
                 (epc-in-main (epc-run s (no-cutpoint-witness s n))))
            (no-cutpoint s n))))

(local
 (defthm no-cutpoint-witness-is-<=-n
   (implies (natp n)
            (<= (no-cutpoint-witness s n) n))
   :rule-classes :linear))

;; OK now we prove that if we epc-run for a number of steps k <
;; (epc-steps-to-exitpoint-sub s) then we cannot hit a epc-cutpoint-main. This is
;; because there is no epc-cutpoint-main as long as we are epc-in-main.

(local
 (defthm not-cutpoint-epc-pre-sub
   (implies (and (natp k)
                 (< k (epc-steps-to-exitpoint-sub s)))
            (and (not (epc-cutpoint-main (epc-run s k)))
                 (epc-in-main (epc-run s k))))
   :hints (("Goal"
            :in-theory (disable |no main cutpoint in epc-sub|)
            :use ((:instance |no main cutpoint in epc-sub|
                             (s (epc-run s k)))
                  (:instance |epc-in-main implies in epc-sub|
                             (s (epc-run s k))))))))

;; We can then use this theorem to prove that (no-cutpoint s k) holds for each
;; k <= (epc-steps-to-exitpoint-sub s).  Notice that we get <= here instead of <
;; since we count from 1 less.

(local
 (defthm no-cutpoint-epc-pre-sub
   (implies (and (natp k)
                 (<= k (epc-steps-to-exitpoint-sub s)))
            (no-cutpoint s k))))


(local
 (defthm epc-cutpoint-main-implies-epc-next-cutpoint-s
   (implies (or (epc-cutpoint-main s)
                (not (epc-in-main s)))
            (equal (epc-next-epc-cutpoint-main s)
                   s))
   :hints (("Goal"
            :use ((:instance |definition of epc-next cutpoint|))))))


;; Now we get to a couple of hack lemmas that can be safely ignored.  First we
;; do not want to deal with (epc-next s) in the context of no-cutpoint.  So we
;; rewrite that term.

(local
 (defthm epc-next-no-cutpoint
   (implies (and (not (epc-cutpoint-main s))
                 (epc-in-main s)
                 (natp n))
            (equal (no-cutpoint (epc-next s) n)
                   (no-cutpoint s (1+ n))))))

(local
 (in-theory (disable epc-exists-exitpoint-sub-suff
                     epc-exists-exitpoint-sub)))

;; We also prove that if a cutpoint holds then no-cutpoint is nil.  This is
;; just orienting the rewriting.

(local
 (defthmd cutpoint-implies-not-nocut
   (implies (and (or (epc-cutpoint-main s)
                     (not (epc-in-main s)))
                 (natp n)
                 (> n 0))
            (equal (no-cutpoint s n) nil))))



(local
 (defthm cutpoint-implies-exists-exitpoint
   (implies (or (epc-cutpoint-main (epc-run s n))
                (not (epc-in-main (epc-run s n))))
            (epc-exists-exitpoint-sub s))
   :hints (("Goal"
            :in-theory (disable epc-exists-exitpoint-sub-suff)
            :use ((:instance epc-exists-exitpoint-sub-suff))))))


;; The reader might be surprised to see the epc-run-fnn (although they might have
;; seen this in some of the previous books designed by me).  The problem is
;; that epc-run has been defined within the encapsulate and therefore its induction
;; schemes are not exported.  For details about this issue, see :DOC
;; subversive-recursions.  So we define a new recursive epc-run-fnn, prove it is
;; equal to epc-run, and then use it when we need induction.


(local
 (defun epc-run-fnn (s n)
   (if (zp n) s (epc-run-fnn (epc-next s) (1- n)))))

;; The trigger is the obvious one, it rewrites epc-run to epc-run-fnn when we need it.

(local
 (defthmd epc-run-fnn-trigger
   (equal (epc-run s n)
          (epc-run-fnn s n))))

;; And this allows us to prove theorems about epc-run by induction, via proving
;; them about epc-run-fnn.

(local
 (defthm epc-run-plus-reduction
   (implies (and (natp m)
                 (natp n))
            (equal (epc-run (epc-run s m) n)
                  (epc-run s (+ m n))))
   :hints (("Goal"
            :in-theory (enable epc-run-fnn-trigger)))))


;; Now we get back, obviously, to no-cutpoint.  We prove that we can use
;; no-cutpoint with +.  Of course the way we prove it is that we prove the
;; theorem for (not (cutpoint ...)) and then lift the result for no-cutpoint.


(local
 (defthmd not-cutpoint-plus-reduction
   (implies (and (no-cutpoint s k)
                 (natp k)
                 (natp n)
                 (no-cutpoint (epc-run s k) n)
                 (< l (+ k n))
                 (natp l))
            (and (not (epc-cutpoint-main (epc-run s l)))
                 (epc-in-main (epc-run s l))))
   :hints (("Goal"
            :cases ((< l k)))
           ("Subgoal 2"
            :use ((:instance no-cutpoint-implies-not-cutpoint
                             (s (epc-run s k))
                             (k (- l k))))))))


(local
 (defthm no-cutpoint-plus-reduction
   (implies (and (no-cutpoint s k)
                 (natp k)
                 (natp n)
                 (no-cutpoint (epc-run s k) n)
                 (<= l (+ k n))
                 (natp l))
            (no-cutpoint s l))
   :hints (("Goal"
            :cases ((zp l)))
           ("Subgoal 2"
            :use ((:instance not-cutpoint-plus-reduction
                             (l (no-cutpoint-witness s (1- l)))))))))


;; Now we prove that if no-cutpoint holds for s and n then it also holds for
;; (epc-run s k) for n-k steps.

(local
 (defthmd no-cutpoint-epc-run-reduction
   (implies (and (no-cutpoint s n)
                 (natp n)
                 (natp k)
                 (<= k n))
            (no-cutpoint (epc-run s k) (- n k)))))

;; Therefore we know that if we are standing at a epc-pre-sub state then from the
;; epc-next-exitpoint, which is to say epc-modify-sub state it should be true from
;; n-steps steps, where n is the number of steps for the first cutpoint from s.

(local
 (defthmd pre-implies-no-cutpoint-s
   (implies (and (no-cutpoint s n)
                 (natp n)
                 (or (epc-cutpoint-main (epc-run s n))
                     (not (epc-in-main (epc-run s n))))
                 (epc-pre-sub s))
            (no-cutpoint (epc-modify-sub s) (- n (epc-steps-to-exitpoint-sub s))))
   :hints (("Goal"
            :in-theory (disable |correctness of epc-sub|)
            :use ((:instance |correctness of epc-sub|)
                  (:instance no-cutpoint-epc-run-reduction
                             (k (epc-steps-to-exitpoint-sub s))))))))



;; Thus we also know that by virtue of epc-run-plus-reduction we can prove that
;; (epc-run s n) is equal to (epc-run (epc-modify-sub s) (n - steps)).

(local
 (defthm pre-implies-epc-run-plus
   (implies (and (epc-pre-sub s)
                 (natp n)
                 (or (epc-cutpoint-main (epc-run s n))
                     (not (epc-in-main (epc-run s n)))))
            (equal (epc-run (epc-modify-sub s) (- n (epc-steps-to-exitpoint-sub s)))
                   (epc-run s n)))
   :hints (("Goal"
            :in-theory (disable |correctness of epc-sub|
                                epc-run-plus-reduction
                                steps-to-exitpoint-is-minimal
                                steps-to-exitpoint-is-natp)
            :use ((:instance epc-run-plus-reduction
                             (n (- n (epc-steps-to-exitpoint-sub s)))
                             (m (epc-steps-to-exitpoint-sub s)))
                  (:instance |correctness of epc-sub|)
                  (:instance epc-exists-exitpoint-sub-suff)
                  (:instance steps-to-exitpoint-is-natp
                             (k n))
                  (:instance steps-to-exitpoint-is-minimal
                             (k n)))))))

(local
 (defthm alternative-epc-next-cutpoint-property
   (implies (and (or (epc-cutpoint-main (epc-run s n))
                     (not (epc-in-main (epc-run s n))))
                 (no-cutpoint s n))
            (equal (epc-next-epc-cutpoint-main s)
                   (epc-run s n)))
   :hints (("Goal"
            :induct (comp-cutpoint-induction s n))
           ("Subgoal *1/3"
            :use ((:instance cutpoint-implies-not-nocut
                             (n (1- n)))))
           ("Subgoal *1/2"
            :use ((:instance pre-implies-no-cutpoint-s))))))


;; OK so I have just proved that if n is the first cutpoint from s, then
;; epc-next-cutpoint-returns state after n steps.  Now we consider the traditional
;; steps-to-cutpoint and prove that it returns the same thing.  But we will
;; start with the definition of the traditional epc-next-cutpoint first.

(local
 (encapsulate
  ()

  (local
   (defthmd steps-to-cutpoint-tail-inv
     (implies (and (or (epc-cutpoint-main (epc-run s k))
                       (not (epc-in-main (epc-run s k))))
                   (natp steps))
              (let* ((result  (o-steps-to-cutpoint-tail-main s steps))
                     (cutpoint-steps (- result steps)))
                (and (natp result)
                     (natp cutpoint-steps)
                     (implies (natp k)
                              (<= cutpoint-steps k))
                     (or (epc-cutpoint-main (epc-run s cutpoint-steps))
                         (not (epc-in-main (epc-run s cutpoint-steps)))))))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (enable natp)
              :induct (cutpoint-induction k steps s)))))

  (defthm steps-to-cutpoint-is-ordinal
    (implies (not (natp (o-steps-to-epc-cutpoint-main s)))
             (equal (o-steps-to-epc-cutpoint-main s) (omega)))
    :rule-classes :forward-chaining)

  (defthm steps-to-cutpoint-is-natp
    (implies (or (epc-cutpoint-main (epc-run s k))
                 (not (epc-in-main (epc-run s k))))
             (natp (o-steps-to-epc-cutpoint-main s)))
    :rule-classes (:rewrite :forward-chaining :type-prescription)
    :hints (("Goal"
             :use ((:instance steps-to-cutpoint-tail-inv
                              (steps 0))))))

  (defthm steps-to-cutpoint-provide-cutpoint
    (implies (or (epc-cutpoint-main (epc-run s k))
                 (not (epc-in-main (epc-run s k))))
             (or (epc-cutpoint-main (epc-run s (o-steps-to-epc-cutpoint-main s)))
                 (not (epc-in-main (epc-run s (o-steps-to-epc-cutpoint-main s))))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :use ((:instance steps-to-cutpoint-tail-inv
                              (steps 0))))))

  (defthm steps-to-cutpoint-is-minimal
    (implies (and (or (epc-cutpoint-main (epc-run s k))
                      (not (epc-in-main (epc-run s k))))
                  (natp k))
             (<= (o-steps-to-epc-cutpoint-main s)
                 k))
    :rule-classes :linear
    :hints (("Goal"
             :use ((:instance steps-to-cutpoint-tail-inv
                              (steps 0))))))))

(local (in-theory (disable o-steps-to-epc-cutpoint-main)))

;; From this I can prove that if some cutpoint is reachable then
;; o-epc-next-epc-cutpoint-main takes us to the first reachable cutpoint.  My strategy
;; now is that I will prove the result rather for the new cutpoint definition
;; than for the old one.  The reason is that it is much easier to reason in
;; abstract about steps-to-cutpoint than about epc-next-cutpoint and therefore we
;; must move from epc-next-cutpoint to steps-to-cutpoint in order to simplify the
;; proofs.

(local
 (defthm not-cutpoint-until-steps-to-cutpoint
   (implies (and (natp l)
                 (or (epc-cutpoint-main (epc-run s k))
                     (not (epc-in-main (epc-run s k))))
                 (< l (o-steps-to-epc-cutpoint-main s)))
            (and (not (epc-cutpoint-main (epc-run s l)))
                 (epc-in-main (epc-run s l))))
    :hints (("Goal"
             :use ((:instance steps-to-cutpoint-is-minimal
                              (k l)))))))

(local (in-theory (disable o-steps-to-epc-cutpoint-main)))

(local
 (defthm no-cutpoint-until-steps-to-cutpoint-aux
   (implies (and (natp l)
                 (or (epc-cutpoint-main (epc-run s k))
                     (not (epc-in-main (epc-run s k))))
                 (<= l (o-steps-to-epc-cutpoint-main s)))
             (no-cutpoint s l))
   :hints (("Goal"
            :induct (no-cutpoint s l))
           ("Subgoal *1/2"
            :in-theory (disable not-cutpoint-until-steps-to-cutpoint)
            :use ((:instance not-cutpoint-until-steps-to-cutpoint
                             (l (1- l))))))))

;; So we have essentially proven that for any l <= steps-to-cutpoint,
;; no-cutpoint holds for l steps.  We can then instantiate l with
;; steps-to-cutpoint itself and clean this up.  Note that we have already
;; proven that steps-to-cutpoint is a natp when a cutpoint is reachable from s.

(local
 (defthmd cutpoint-implies-no-cutpoint-steps
   (implies (or (epc-cutpoint-main (epc-run s k))
                (not (epc-in-main (epc-run s k))))
            (no-cutpoint s (o-steps-to-epc-cutpoint-main s)))
   :otf-flg t
   :hints (("Goal"
            :in-theory (disable steps-to-cutpoint-is-natp
                                cutpoint-implies-no-cut-2
                                not-cutpoint-until-steps-to-cutpoint
                                no-cutpoint-until-steps-to-cutpoint-aux)
            :use ((:instance steps-to-cutpoint-is-natp)
                  (:instance no-cutpoint-until-steps-to-cutpoint-aux
                             (l (o-steps-to-epc-cutpoint-main s))))))))

;; Therefore we should know that (epc-next-cutpoint s) is equal to (epc-run s
;; (o-steps-to-cutpoint s)).

(local
 (defthm epc-next-cutpoint-is-epc-run-of-steps
   (implies (or (epc-cutpoint-main (epc-run s k))
                (not (epc-in-main (epc-run s k))))
            (equal (epc-next-epc-cutpoint-main s)
                   (epc-run s (o-steps-to-epc-cutpoint-main s))))
   :hints (("Goal"
            :in-theory (disable alternative-epc-next-cutpoint-property)
            :use ((:instance cutpoint-implies-no-cutpoint-steps)
                  (:instance steps-to-cutpoint-provide-cutpoint)
                  (:instance alternative-epc-next-cutpoint-property
                             (n (o-steps-to-epc-cutpoint-main s))))))))

;; Now we only have to prove that if there is a cutpoint which is not an
;; exitpoint then there is a cutpoint reachable from (epc-next s)

(local
 (defthm epc-next-has-a-cutpoint
   (implies (and (epc-in-main s)
                 (not (epc-in-main (epc-run s k))))
            (or (epc-cutpoint-main (epc-run (epc-next s) (1- k)))
                (not (epc-in-main (epc-run (epc-next s) (1- k))))))
   :rule-classes nil
   :hints (("Goal"
            :expand (epc-run s k)))))


;; Now we can just prove that the epc-next-cutpoint  of (epc-next s) under the proper
;; condition is just the same as its traditional definition.

(local
 (defthm epc-next-cutpoint-matches
   (implies (and (epc-in-main s)
                 (not (epc-in-main (epc-run s k))))
            (equal (epc-run (epc-next s) (o-steps-to-epc-cutpoint-main (epc-next s)))
                   (epc-next-epc-cutpoint-main (epc-next s))))
   :hints (("Goal"
            :in-theory (disable epc-next-cutpoint-is-epc-run-of-steps)
            :use ((:instance epc-next-cutpoint-is-epc-run-of-steps
                             (s (epc-next s))
                             (k (1- k))))))))


;; Now we can of course just prove the final theorem since we know from the
;; encapsulation that assertion is inductive over the new definition of
;; epc-next-cutpoint.

(local
 (defthm |new cutpoint definition matches old|
   (implies (and (epc-assertion-main s0 s)
                 (epc-in-main s)
                 (not (epc-in-main (epc-run s n))))
            (epc-assertion-main s0 (o-epc-next-epc-cutpoint-main (epc-next s))))
   :hints (("Subgoal 1"
            :in-theory (disable steps-to-cutpoint-is-natp)
            :use ((:instance steps-to-cutpoint-is-natp
                             (k (1- n))
                             (s (epc-next s))))))))

(local (include-book "vanilla-partial-correctness"))

(defp epc-exitsteps-main-tail (s i)
  (if (not (epc-in-main s)) i
    (epc-exitsteps-main-tail (epc-next s) (1+ i))))

(defun epc-exitsteps-main (s)
  (let ((steps (epc-exitsteps-main-tail s 0)))
    (if (not (epc-in-main (epc-run s steps)))
        steps
      (omega))))

(defun-sk epc-exists-exitpoint-main (s)
  (exists n (not (epc-in-main (epc-run s n)))))


(defun epc-next-exitpoint-main (s)
  (epc-run s (epc-exitsteps-main s)))


(local (in-theory (theory 'minimal-theory)))

(local
 (defthmd composition-partial-aux
  (implies (and (epc-pre-main s)
                (equal s s0)
                (epc-exists-exitpoint-main s))
           (and (not (epc-in-main (epc-next-exitpoint-main s)))
                (equal (epc-next-exitpoint-main s)
                       (epc-modify-main s))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  (:functional-instance
                   |partial correctness|
                   (cutpoint
                    (lambda (s) (or (epc-cutpoint-main s) (not (epc-in-main s)))))
                   (assertion (lambda (s) (epc-assertion-main s0 s)))
                   (pre (lambda (s) (and (epc-pre-main s) (equal s0 s))))
                   (exitpoint (lambda (s) (not (epc-in-main s))))
                   (next-exitpoint (lambda (s) (epc-next-exitpoint-main s)))
                   (exists-exitpoint (lambda (s) (epc-exists-exitpoint-main s)))
                   (steps-to-exitpoint (lambda (s) (epc-exitsteps-main s)))
                   (steps-to-exitpoint-tail epc-exitsteps-main-tail)
                   (steps-to-cutpoint
                    (lambda (s) (o-steps-to-epc-cutpoint-main s)))
                   (steps-to-cutpoint-tail
                    (lambda (s i) (o-steps-to-cutpoint-tail-main s i)))
                   (next-state-cutpoint
                    (lambda (s) (o-epc-next-epc-cutpoint-main s)))
                   (post (lambda (s) (equal s (epc-modify-main s0))))
                   (default-state default-aux-epc-state)
                   (run-fn epc-run)
                   (exists-exitpoint-witness epc-exists-exitpoint-main-witness)
                   (next-state epc-next)))))
          ("Subgoal 14"
           :in-theory (enable epc-run))
         ("Subgoal 13"
          :use ((:instance |new cutpoint definition matches old|)))
          ("Subgoal 12"
           :use ((:instance o-steps-to-cutpoint-tail-main$def)))
          ("Subgoal 11"
          :use ((:instance |epc-assertion main implies post|)))
          ("Subgoal 10"
           :use ((:instance |epc-pre main implies assertion|)
                 (:instance |epc-assertion implies cutpoint|)))
          ("Subgoal 9"
           :use ((:instance |epc-pre main implies assertion|)))
          ("Subgoal 7"
           :use ((:instance (:definition o-epc-next-epc-cutpoint-main))))
          ("Subgoal 6"
           :use ((:instance (:definition o-steps-to-epc-cutpoint-main))))
          ("Subgoal 5"
           :use ((:instance (:definition epc-next-exitpoint-main))))
          ("Subgoal 4"
           :use ((:instance (:definition epc-exitsteps-main))))
          ("Subgoal 3"
           :use ((:instance epc-exitsteps-main-tail$def)))
         ("Subgoal 2"
          :use ((:instance epc-exists-exitpoint-main-suff)))
         ("Subgoal 1"
          :use ((:instance (:definition epc-exists-exitpoint-main)))))))

(DEFTHM |epc composite partial correctness|
  (implies (and (epc-pre-main s)
                (epc-exists-exitpoint-main s))
           (and (equal (epc-in-main (epc-next-exitpoint-main s)) nil)
                (equal (epc-next-exitpoint-main s)
                       (epc-modify-main s))))
  :hints (("Goal"
           :use ((:instance composition-partial-aux (s0 s))))))
