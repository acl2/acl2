(in-package "ACL2")

#||

  reflexive.lisp
  ~~~~~~~~~~~~~~

Authors: Sandip Ray and Matt Kaufmann
Date: Fri Jul 27 02:56:20 2007

This book presents a solution to an abstract generic version of the
while-language challenge provided by Bill Young.  The book formalizes
the version of the challenge specified by Matt kaufmann, and further
augmented by John Cowles.

Some History of the Challenge
-----------------------------

On Fri, 22 Jun 2007 17:31:10 -0500, Bill Young provided the following
challenge to the acl2-help mailing list:

Define a function run, which satisfies the following equation:

  (equal (run stmt mem)
         (case (op stmt)
            (skip     (run-skip stmt mem))
            (assign   (run-assignment stmt mem))
            (if       (if (zerop (evaluate (arg1 stmt) mem))
                          (run (arg3 stmt) mem)
                        (run (arg3 stmt) mem)))
            (while    (if (zerop (evaluate (arg1 stmt) mem))
                          mem
                        (run stmt
                             (run (arg2 stmt) mem))))
            (sequence (run (arg2 stmt)
                           (run (arg1 stmt) mem)))
            (otherwise mem)))

The problem with the definition is that it involves a reflexive call
of run.  Note the case for "while".  As a pre-history, J Moore and I
had thought some time in 2005 about such reflexive equations, and we
had not found a way to admit reflexive equations in general, even if
they are "tail-recursive" in some sense, that is, the outer call of
the equation returns the same value as the outer of the inner call, as
we see here: (run stmt mem) = (.... (run stmt (run (arg2 stmt) mem)))

The reason for that is as follows.  The typical approach for
introducing such functions is to first introduce a bounded version of
the equation, using an extra "clock" argument, and then eliminate the
call by the Skolem witness of a quantified predicate that says "the
function terminates".  But there is a problem here.  Say the inner
call does not terminate.  We should then have it that the main call
does not terminate.  But that's difficult to guarantee.  For instance,
say that the inner (run (arg2 stmt) mem) does not terminate and
therefore using a Skolem witness it returns 42.  But (run stmt 42)
might terminate, and hence the outer call does terminate even when the
inner call doesn't.  I had talked to John Matthews about this problem,
and he and I came to the opinion that it is possible to have the
equation if there is a (btm) value such that (run stmt (btm))=(btm).
Then of course we can signal non-termination by using a return value
of (btm).  In a certain sense this work is a realization of that
pre-historic discussion.

Back to the history, I mentioned to Bill that we need such a (btm),
but forgot completely why we needed it.  But subsequently, Matt
Kaufmann and I looked at the challenge again that day for a few
minutes, and we seemed to think that it might be possible to introduce
Bill's equation in ACL2 as is. (We were wrong, because of the above
reason.  But I remembered the reason only after John Cowles explained
it again very clearly to me in an email on Sat, 14 Jul 2007 13:33:08
-0600.)  Kaufmann then issued the following challenge:

  CHALLENGE PROBLEM: Extend or modify defpun to allow definitions
  having the form described (for f) above.

[That challenge, BTW, is still unanswered, but I think I can write a
macro answering that very easily now.]

Anyhow, after the initial discussion which involved John Matthews, me,
and Matt Kaufmann, I did not look at the challenge until today.
Meanwhile, Dave Greve and John Cowles came up with solutions for
Bill's challenge.

The theorem that Dave proved is the following: (I believe he proved
this some time before Thu, 12 Jul 2007 07:52:05 -0500 (when I got to
know it).

  (defthm run_spec
    (equal (run stmt mem)
           (if (run_terminates stmt mem)
               (case (op stmt)
                 (skip     (run-skip stmt mem))
                 (assign   (run-assignment stmt mem))
                 (if       (if (zerop (evaluate (arg1 stmt) mem))
                               (run (arg2 stmt) mem)
                             (run (arg3 stmt) mem)))
                 (while    (if (zerop (evaluate (arg1 stmt) mem))
                               mem
                             (run stmt
                                  (run (arg2 stmt) mem))))
                 (sequence (run (arg2 stmt)
                                (run (arg1 stmt) mem)))
                 (otherwise mem))
             mem))
    :rule-classes nil)

Note that the equation has the hypothesis (run_terminates stmt mem).

John Cowles, on Sat, 14 Jul 2007 11:41:59 -0600, proved the following
theorem, for Bill's language.

  (defthm
    Run-satisfies-specification
    (equal (run stmt mem)
	   (if (null mem)
	       nil
	       (case (op stmt)
		     (skip      mem)
		     (assign    (run-assignment stmt mem))
		     (sequence  (run (arg2 stmt)(run (arg1 stmt) mem)))
		     (if        (if (zerop (eval-expr (arg1 stmt) mem))
		       		    (run (arg3 stmt) mem)
				  (run (arg2 stmt) mem)))
		     (while       (if (zerop (eval-expr (arg1 stmt) mem))
				       mem
				    (run stmt (run (arg2 stmt) mem))))
		     (otherwise mem))))


This answers Bill's challenge, by noting that nil acts as the btm
here.  Subsequently, John Cowles made several improvements to his
book.

John Cowles' book (as also, I believe, Dave Greve's solution) are
based on the language that Bill Young originally proposed.  On Wed, 25
Jul 2007 17:58:54 -0500, Kaufmann suggested a significant
generalization as follows.  Given functions test1, test2, dst1, dst2,
finish, and stp, introduce run with the following property:

  (defthm run-thm
    (equal (run x st)
           (if (equal st (btm))
               st
             (if (test1 x st)
                 (finish x st)
               (if (test2 x st)
                   (run (dst1 x st) (stp x st))
                 (let ((st2 (run (dst1 x st) st)))
                   (run (dst2 x st st2) st2)))))))

He also suggested how to go about doing this.  On Thu, 26 Jul 2007
13:32:21 -0600, John Cowles suggested the following further
generalization.

  (defthm run-thm  ;; John's proposed change
    (equal (run x st)
           (if (equal st (btm))
               st
             (if (test1 x st)
                 (finish x st)
               (if (test2 x st)
                   (run (dst1 x st) (stp x st))
                 (let ((st2 (run (dst1 x st)(STP x st)))) ;;Replace st with (STP x st)
                   (run (dst2 x st st2) st2))))))).


This book provides a solution to the generalized challenge above, in
that it introduces the function generic-run and proves that it satisfies the
desired equation.

Approach
--------

See comments on the proof script below.  The key definitions are all
as suggested originally suggested by Kaufmann

Efforts Breakdown
-----------------

Total: 4 1/2 hours (or so)

- 1 hour: Writing the definitions, reading the relevant email and
digesting the problem

- 2 1/2 hours: Doing the proof (with some procrastination as I cut and
pasted the formulas from the prover output).

- 1 hour: Documentation


||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Generic stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In this section, we provide the encapsulated functions that we
;; assume are provided for the concrete language.  Note that most of
;; them are stubbed with the only condition necessary being that
;; generic-finish, on generic-btm, returns generic-btm.

(local
 (include-book "arithmetic/top-with-meta" :dir :system))


(defstub generic-test1 (x st) t)
(defstub generic-test2 (x st) t) ; normal recursion

(defstub generic-dst1 (x st) t) ; take part of x, perhaps based on st
(defstub generic-dst2 (x st1 st2) t) ; take part of x, perhaps based on st1 and st2
(defstub generic-step (x st) t) ; step

(encapsulate
 (((generic-btm) => *)
  ((generic-finish * *) => *))

 (local (defun generic-btm () nil))
 (local (defun generic-finish (x st) (declare (ignore x)) st))

 (defthm generic-finish-is-not-generic-btm
   (implies (not (equal st (generic-btm)))
            (not (equal (generic-finish x st) (generic-btm))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: The bounded version
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The bounded version does essentially the same thing that we want
;; out of the original version, but it makes use of an additional clk
;; argument to bound the number of recursive calls.  This idea of
;; course is not new, and was originally used in defpun, and in
;; several other places, including (probably) John C's paper on
;; introducing primitive recursive equations and (definitely) my
;; generalization of primitive recursive equations.

(defun generic-run-clk (x st clk)
  (declare (xargs :measure (nfix clk)))
  (cond ((zp clk) (generic-btm))
        ((equal st (generic-btm)) st)
        ((generic-test1 x st)
         (generic-finish x st))
        ((generic-test2 x st)
         (generic-run-clk (generic-dst1 x st) (generic-step x st) (1- clk)))
        (t (let ((st2 (generic-run-clk (generic-dst1 x st)
                                       (generic-step x st)
                                       (1- clk))))
             (if (equal st2 (generic-btm))
                 (generic-btm)
               (generic-run-clk (generic-dst2 x st st2) st2 (1- clk)))))))


;; Here is the key lemma (suggested by Matt Kaufmann).  It says that
;; if some bound c1 is sufficient then a larger bound c2 is also
;; sufficient.

(local
 (encapsulate
  ()

  (local
   (defthm generic-run-clk-divergence-helper
     (implies (and (not (equal (generic-run-clk x st c) (generic-btm)))
                   (natp c)
                   (natp i))
              (equal (generic-run-clk x st (+ c i)) (generic-run-clk x st c)))
     :rule-classes nil))


  (defthm generic-run-clk-divergence
    (implies (and (not (equal (generic-run-clk x st c1) (generic-btm)))
                  (natp c1)
                  (natp c2)
                  (<= c1 c2))
             (equal (generic-run-clk x st c2)
                    (generic-run-clk x st c1)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance generic-run-clk-divergence-helper
                              (c c1)
                              (i (- c2 c1)))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Eliminating the bound
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We now introduce the choice function, to eliminate the clk bound
;; above.  kaufmann's original version just introduced the clk via
;; defchoose.  I use defun-sk for no good reason except that I simply
;; cannot think clearly with defchoose directly, but always need to
;; think about quantification (and get Skolemization as a result).

(defun-sk exists-enough (x st)
  (exists clk
          (and (natp clk)
               (not (equal (generic-run-clk x st clk) (generic-btm))))))

;; And we introduce the function generic-run by providing a sufficient bound
;; if one exists.  The other (generic-btm) is perhaps not necessary, but
;; certainly is convenient.

(defun generic-run (x st)
  (if (exists-enough x st)
      (generic-run-clk x st (exists-enough-witness x st))
    (generic-btm)))

(local
 (in-theory (disable exists-enough exists-enough-suff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: The final proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Believe it or not, the remainder is rather trivial.  It is simply
;; the standard dance that we have to do when we have a quantified
;; hypothesis and a quantified conclusion.

;; Our goal is the following.  We will prove, separately, for each
;; kind of hypothesis, that generic-run satisfies the corresponding equation.
;; We then finally patch them together in a single theorem at the end.

;; In this section we prove the different cases for generic-run.  The first
;; two are trivial.


(local
 (defthm definition-of-generic-run-0
   (implies (equal st (generic-btm))
            (equal (generic-run x st) (generic-btm)))))

(local
 (defthm definition-of-generic-run-1
   (implies (and (not (equal st (generic-btm)))
                 (generic-test1 x st))
            (equal (generic-run x st)
                   (generic-finish x st)))
   :hints (("Goal"
            :in-theory (enable exists-enough)
            :use ((:instance exists-enough-suff
                             (clk 1)))))))


;; I now disable generic-run-clk, since I'm now in the realm of doing the
;; quantifier proof and I want to have complete control over the
;; proof.

(local (in-theory (disable generic-run-clk)))

;; I prove theorems of the form (exists x (P x y)) = (exists x (Q x
;; y)) by mutual implication.  But I like to have the equality around
;; when possible.  The reason is that when I do instantiate such
;; theorem in a :use hint I don't want to think about which direction
;; of the implication we really need.

(local
 (encapsulate
  ()

  (local
   (defthm generic-run-2-works-one-direction
     (implies (and (not (equal st (generic-btm)))
                   (not (generic-test1 x st))
                   (generic-test2 x st)
                   (exists-enough x st))
              (exists-enough (generic-dst1 x st) (generic-step x st)))
     :hints
     (("Goal"
       :use ((:instance exists-enough)
             (:instance (:definition generic-run-clk)
                        (clk (exists-enough-witness x st)))
             (:instance exists-enough-suff
                        (x (generic-dst1 x st))
                        (st (generic-step x st))
                        (clk (1- (exists-enough-witness x st)))))))))

  (local
   (defthm generic-run-2-works-other-direction
     (implies (and (not (equal st (generic-btm)))
                   (not (generic-test1 x st))
                   (generic-test2 x st)
                   (exists-enough (generic-dst1 x st) (generic-step x st)))
              (exists-enough x st))
     :hints (("Goal"
              :use ((:instance exists-enough
                               (x (generic-dst1 x st))
                               (st (generic-step x st)))
                    (:instance exists-enough-suff
                               (clk (1+ (exists-enough-witness
                                         (generic-dst1 x st)
                                         (generic-step x st)))))
                    (:instance (:definition generic-run-clk)
                               (clk (1+ (exists-enough-witness
                                         (generic-dst1 x st)
                                         (generic-step x st))))))))))

  (defthmd generic-run-2-exists-works
    (implies (and (not (equal st (generic-btm)))
                  (not (generic-test1 x st))
                  (generic-test2 x st))
             (equal (exists-enough (generic-dst1 x st) (generic-step x st))
                    (exists-enough x st)))
    :hints (("Goal"
             :cases ((exists-enough x st)
                     (exists-enough (generic-dst1 x st) (generic-step x st))))))))


;; OK.  Now that we have the equivalence of the two exists (one for
;; the outer call and one for the body) we will prove that generic-run
;; satisfies the equation in the generic-test2 case.  This is a very
;; standard proof although it does look complicated with lots of :use
;; hints.  I could have made them into lemmas, but this is a standard
;; dance of quantifiers that I need to do anyways, so I didn't bother.
;; The idea is simple.  I use the above lemma to justify the cases
;; when one existential quantifier holds and the other doesn't (that
;; is, the outer call terminates, but the inner doesn't and
;; vice-versa), opening up the definition of generic-run-call as
;; necessary.  Then we use the generic-run-clk-divergence lemma as
;; follows.  Notice that the outer call (LHS) expands to
;; (generic-run-clk x st (exists-enough-witness x st)), which then
;; expands (using the definition of generic-run-clk) to
;; (generic-run-clk (generic-dst1 x st) (generic-step x st) (1-
;; (exists-enough-witness x st))).  But the RHS (inner call) expands
;; to (generic-run-clk (generic-dst1 x st) (generic-step x st)
;; (exists-enough-witness (generic-dst1 x st) (generic-step x st))).
;; In order to show the equaliuty, we then do a case split on whether
;; the inner witness is smaller or larger than the outer witness.  In
;; each case, we replace one with the smaller one by the
;; generic-run-clk-divergence lemma.


(local
 (defthm definition-of-generic-run-2
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (generic-test2 x st))
            (equal (generic-run x st)
                   (generic-run (generic-dst1 x st) (generic-step x st))))
   :hints (("Goal"
            :cases ((and (exists-enough x st)
                         (exists-enough (generic-dst1 x st) (generic-step x st)))))
           ("Subgoal 2"
            :in-theory (enable generic-run-2-exists-works))
           ("Subgoal 1"
            :use ((:instance (:definition generic-run-clk)
                             (clk (exists-enough-witness x st)))
                  (:instance (:definition exists-enough))))
           ("Subgoal 1.2"
            :cases ((<= (exists-enough-witness x st)
                        (exists-enough-witness (generic-dst1 x st)
                                               (generic-step x st)))))
           ("Subgoal 1.2.1"
            :in-theory (enable exists-enough)
            :use ((:instance generic-run-clk-divergence
                             (x (generic-dst1 x st))
                             (st (generic-step x st))
                             (c1 (1- (exists-enough-witness x st)))
                             (c2 (exists-enough-witness (generic-dst1 x st)
                                                        (generic-step x st))))))
           ("Subgoal 1.2.2"
            :in-theory (enable generic-run-clk exists-enough)
            :use ((:instance generic-run-clk-divergence
                             (c1 (1+ (exists-enough-witness
                                      (generic-dst1 x st)
                                      (generic-step x st))))
                             (c2 (exists-enough-witness x st))))))))

;; OK so we got that case through.  Now is the final case, and that's
;; of course the most complicated one.  For this one I did not wrap
;; the existential quantifier equality theorem by encapsulate.  This
;; is because one of the lemmas, namely generic-run3-first-part, which
;; I need for that theorem is also necessary in the final definitional
;; equation proof.

;; I break this proof down into cases, since the second existence
;; proof (for the reflexive call) requires that the outer call witness
;; can be replaced by the witness for the inner (non-reflexive) call.


;; OK first prove that if we have enough clk for the outer call then
;; then that is enough for the inner (non-reflexive) call.

(local
 (defthm generic-run-3-works-one-direction-1
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (not (generic-test2 x st))
                 (exists-enough x st))
            (exists-enough (generic-dst1 x st) (generic-step x st)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable generic-run-clk)
            :use ((:instance (:definition exists-enough))
                  (:instance exists-enough-suff
                             (clk (1- (exists-enough-witness x st)))
                             (x (generic-dst1 x st))
                             (st (generic-step x st)))
                  (:instance (:definition generic-run-clk)
                             (clk (exists-enough-witness x st))))))))


;; So using the generic-run-clk-divergence lemma we know that we can
;; replace the witness of the inner call with the expansion of the
;; witness for the outer call.  This is the same dance using case
;; split and generic-run-clk-dvergence as I discussed in the comment
;; for the previous case above.

(local
 (defthmd generic-run3-first-part
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (not (generic-test2 x st))
                 (exists-enough x st))
            (equal (generic-run-clk (generic-dst1 x st) (generic-step x st)
                                    (exists-enough-witness (generic-dst1 x st)
                                                           (generic-step x st)))
                   (generic-run-clk (generic-dst1 x st) (generic-step x st)
                                    (1- (exists-enough-witness x st)))))

   :hints (("Goal"
            :in-theory (enable exists-enough generic-run-clk)
            :cases ((<= (exists-enough-witness x st)
                        (exists-enough-witness (generic-dst1 x st)
                                               (generic-step x st)))))
           ("Subgoal 1"
            :use ((:instance generic-run-3-works-one-direction-1)
                  (:instance generic-run-clk-divergence
                             (x (generic-dst1 x st))
                             (st (generic-step x st))
                             (c1 (1- (exists-enough-witness x st)))
                             (c2 (exists-enough-witness (generic-dst1 x st)
                                                        (generic-step x st))))))
           ("Subgoal 2"
            :use ((:instance generic-run-3-works-one-direction-1)
                  (:instance generic-run-clk-divergence
                             (x (generic-dst1 x st))
                             (st (generic-step x st))
                             (c2 (1- (exists-enough-witness x st)))
                             (c1 (exists-enough-witness (generic-dst1 x st)
                                                        (generic-step x st)))))))))


;; Now because of the above lemma, I can uniformly have the witness of
;; the inner (noin-reflexive) call to be the expansion of the witness
;; of the outer call.  Now use standard argument to justify that there
;; is enough for the reflexive call.

(local
 (defthm generic-run-3-works-second-part
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (not (generic-test2 x st))
                 (exists-enough x st))
            (let ((st2 (generic-run (generic-dst1 x st) (generic-step x st))))
              (exists-enough (generic-dst2 x st st2) st2)))
   :rule-classes nil
   :hints (("Goal"
            :do-not '(fertilize))
           ("Subgoal 1"
            :use generic-run-3-works-one-direction-1)
           ("Subgoal 2"
            :in-theory (enable generic-run3-first-part)
            :use
            ((:instance (:definition exists-enough))
             (:instance (:definition generic-run-clk)
                        (clk (exists-enough-witness x st)))
             (:instance
              exists-enough-suff
              (x (GENERIC-DST2 X ST
                               (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                                (GENERIC-STEP X ST)
                                                (+ -1
                                                   (EXISTS-ENOUGH-WITNESS X ST)))))
              (st (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                   (GENERIC-STEP X ST)
                                   (+ -1 (EXISTS-ENOUGH-WITNESS
                                          X ST))))
              (clk (1- (exists-enough-witness x st)))))))))

;; Now the other direction.  I don't know why I called this helper.
;; No special reason.  This *is* the other direction.  Nothing special
;; here; the standard way is to use the definition for the quantified
;; predicate in the hypothesis, and the suff lemma for the one in the
;; conclusion.  Then I apply the divergence lemma (and case split) to
;; allow myself to produce the right instantiation to match the
;; definitional equation.

(local
 (defthm generic-run-3-works-other-direction-helper
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (not (generic-test2 x st))
                 (exists-enough (generic-dst1 x st) (generic-step x st))
                 (let ((st2 (generic-run (generic-dst1 x st)
                                         (generic-step x st))))
                   (exists-enough (generic-dst2 x st st2) st2)))
            (exists-enough x st))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance (:definition exists-enough)
                      (x (generic-dst1 x st))
                      (st (generic-step x st)))
           (:instance (:definition exists-enough)
                      (x (let ((st2 (generic-run (generic-dst1 x st)
                                                 (generic-step x st))))
                           (generic-dst2 x st st2)))
                      (st (generic-run (generic-dst1 x st)
                                       (generic-step x st))))
           (:instance
            exists-enough-suff
            (clk (1+ (max (exists-enough-witness
                           (generic-dst1 x st)
                           (generic-step x st))
                          (exists-enough-witness
                           (let ((st2 (generic-run (generic-dst1 x st)
                                                   (generic-step x st))))
                             (generic-dst2 x st st2))
                           (generic-run (generic-dst1 x st)
                                        (generic-step x st)))))))))
    ("Subgoal 1"
     :use
     ((:instance
       (:definition generic-run-clk)
       (clk (+ 1
               (EXISTS-ENOUGH-WITNESS
                (GENERIC-DST2
                 X ST
                 (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                  (GENERIC-STEP X ST)
                                  (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                         (GENERIC-STEP X ST))))
                (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                 (GENERIC-STEP X ST)
                                 (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                        (GENERIC-STEP X ST)))))))
      (:instance
       generic-run-clk-divergence
       (x (generic-dst1 x st))
       (st (generic-step x st))
       (c1 (exists-enough-witness (generic-dst1 x st)
                                  (generic-step x st)))
       (c2 (EXISTS-ENOUGH-WITNESS
            (GENERIC-DST2 X ST
                          (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                           (GENERIC-STEP X ST)
                                           (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                                  (GENERIC-STEP X ST))))
            (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                             (GENERIC-STEP X ST)
                             (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                    (GENERIC-STEP X ST))))))))
    ("Subgoal 2"
     :use ((:instance
            (:definition generic-run-clk)
            (clk (+ 1
                    (EXISTS-ENOUGH-WITNESS (generic-dst1 x st) (generic-step x st)))))

           (:instance
            generic-run-clk-divergence
            (x (GENERIC-DST2
                X ST
                (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                 (GENERIC-STEP X ST)
                                 (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                        (GENERIC-STEP X
                                                                      ST)))))

            (st (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                 (GENERIC-STEP X ST)
                                 (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                        (GENERIC-STEP X ST))))

            (c2 (exists-enough-witness (generic-dst1 x st)
                                       (generic-step x st)))
            (c1 (EXISTS-ENOUGH-WITNESS
                 (GENERIC-DST2 X ST
                               (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                                (GENERIC-STEP X ST)
                                                (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                                       (GENERIC-STEP X ST))))
                 (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                  (GENERIC-STEP X ST)
                                  (EXISTS-ENOUGH-WITNESS (GENERIC-DST1 X ST)
                                                         (GENERIC-STEP X  ST)))))))))))

;; Now I wrap them together in an equality.

(local
 (defthm generic-run-3-works
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (not (generic-test2 x st)))
            (equal (exists-enough x st)
                   (and (exists-enough (generic-dst1 x st) (generic-step x st))
                        (let ((st2 (generic-run (generic-dst1 x st) (generic-step x st))))
                          (exists-enough (generic-dst2 x st st2) st2)))))
   :rule-classes nil
   :hints (("Goal"
            :cases ((exists-enough x st)
                    (and (exists-enough (generic-dst1 x st) (generic-step x st))
                         (let ((st2 (generic-run (generic-dst1 x st) (generic-step x st))))
                           (exists-enough (generic-dst2 x st st2) st2)))))
           ("Subgoal 2"
            :use ((:instance generic-run-3-works-one-direction-1)
                  (:instance generic-run-3-works-second-part)))
           ("Subgoal 1"
            :use ((:instance generic-run-3-works-other-direction-helper))))))

;; And now finally the definition for this case.  Again the standard
;; dance, apply the definition of generic-run-clk and exists-enough to rule
;; out trivial cases, and then apply the divergence lemma.


(local
 (defthm definition-of-generic-run-3
   (implies (and (not (equal st (generic-btm)))
                 (not (generic-test1 x st))
                 (not (generic-test2 x st)))
            (equal (generic-run x st)
                   (let ((st2 (generic-run (generic-dst1 x st) (generic-step x st))))
                     (generic-run (generic-dst2 x st st2) st2))))
   :hints (("Goal"
            :do-not '(fertilize))
           ("Subgoal 2"
            :use ((:instance generic-run-3-works)))
           ("Subgoal 3"
            :use ((:instance generic-run-3-works)))
           ("Subgoal 4.1"
            :use ((:instance generic-run-3-works)))
           ("Subgoal 4.2"
            :use ((:instance (:definition generic-run-clk)
                             (clk (exists-enough-witness x st)))
                  (:instance (:definition exists-enough))
                  (:instance generic-run3-first-part)))
           ("Subgoal 4.2.2"
            :cases ((<= (EXISTS-ENOUGH-WITNESS
                         (GENERIC-DST2
                          X ST
                          (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                           (GENERIC-STEP X ST)
                                           (+ -1 (EXISTS-ENOUGH-WITNESS X ST))))
                         (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                          (GENERIC-STEP X ST)
                                          (+ -1 (EXISTS-ENOUGH-WITNESS X ST))))
                        (+ -1 (EXISTS-ENOUGH-WITNESS X ST)))))
           ("Subgoal 4.2.2.2"
            :in-theory (enable exists-enough)
            :use
            ((:instance
              generic-run-clk-divergence
              (x (GENERIC-DST2
                  X ST
                  (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                   (GENERIC-STEP X ST)
                                   (+ -1
                                      (EXISTS-ENOUGH-WITNESS X ST)))))
              (st (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                   (GENERIC-STEP X ST)
                                   (+ -1 (EXISTS-ENOUGH-WITNESS
                                          X ST))))
              (c1 (+ -1 (EXISTS-ENOUGH-WITNESS X ST)))
              (c2 (EXISTS-ENOUGH-WITNESS
                   (GENERIC-DST2 X ST
                                 (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                                  (GENERIC-STEP X ST)
                                                  (+ -1 (EXISTS-ENOUGH-WITNESS X ST))))
                   (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                    (GENERIC-STEP X ST)
                                    (+ -1 (EXISTS-ENOUGH-WITNESS
                                           X ST))))))))
           ("Subgoal 4.2.2.1"
            :in-theory (enable exists-enough)
            :use
            ((:instance
              generic-run-clk-divergence
              (x (GENERIC-DST2
                  X ST
                  (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                   (GENERIC-STEP X ST)
                                   (+ -1
                                      (EXISTS-ENOUGH-WITNESS X ST)))))
              (st (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                   (GENERIC-STEP X ST)
                                   (+ -1 (EXISTS-ENOUGH-WITNESS
                                          X ST))))
              (c2 (+ -1 (EXISTS-ENOUGH-WITNESS X ST)))
              (c1 (EXISTS-ENOUGH-WITNESS
                   (GENERIC-DST2 X ST
                                 (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                                  (GENERIC-STEP X ST)
                                                  (+ -1 (EXISTS-ENOUGH-WITNESS X ST))))
                   (GENERIC-RUN-CLK (GENERIC-DST1 X ST)
                                    (GENERIC-STEP X ST)
                                    (+ -1 (EXISTS-ENOUGH-WITNESS X ST)))))))))))



(local (in-theory (disable generic-run)))

;; Now that we have done all the cases, the final theorem is trivial.

(defthm |definition of generic-run|
  (equal (generic-run x st)
         (cond ((equal st (generic-btm))
                (generic-btm))
               ((generic-test1 x st)
                (generic-finish x st))
               ((generic-test2 x st)
                (generic-run (generic-dst1 x st) (generic-step x st)))
               (t (let
                      ((st2 (generic-run (generic-dst1 x st)
                                         (generic-step x st))))
                    (generic-run (generic-dst2 x st st2) st2)))))
  :rule-classes :definition)






