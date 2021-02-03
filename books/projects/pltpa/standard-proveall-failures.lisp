                       ; An Analysis of the Two Theorems
                                   ; in the
                 ; Standard Proveall that PLTP(A) Cannot Prove

                              ; J Strother Moore
                                ; August, 2017

; Certification Instructions:
; (include-book "pltpa") ; just to get the PLTP package
; (certify-book "standard-proveall-failures" 1)

; Abstract:
; PLTP(A) fails to prove two theorems in the [THEOREMS] file from 2 September,
; 1973, (Listing I, page 3).  Recall that it is from [THEOREMS] that we have
; constructed the PLTP(A) file we call the ``standard proveall'' in this
; archive.

; The two failures are:

;  [T 8 1 *]::
;  [EQUAL [BINARYOF [PLUS N M]] [BINADD [BINARYOF N] [BINARYOF M]]]

; and

;  [T 8 3]::
;  [EQUAL [LINEAR [CDR [BINARYOF N]]] [HALF N]]

; There is no reason to believe this indicates a difference between PLTP and
; PLTP(A).  These two theorems are not included in the proveall output of 18
; July, 1973 (Listing-J in the archive) even though a proof of the theorem
; between these two, [T 8 2], is included in that output.  But the question
; naturally arises: could some version of PLTP have proved these theorems?  I
; argue in the negative here to that question.

; Some Historical Perspective:

; The following remarks, while meant to clarify the situation, probably do the
; opposite.  The 18 July, 1973, proveall output in Listing-J was not driven
; from same [THEOREMS] file from which we constructed the current
; standard-proveall.lsp.  That [THEOREMS] file dates from 2 September, 1973,
; and may well include theorems that were not in earlier versions of that file.
; Unfortunately, the only snapshot we have of the [THEOREMS] file is the 2
; September, 1973, one, several months after the proof output was listed.

; Furthermore, it was our convention back then to mark with `*' any theorem we
; knew PLTP could not prove and we worked on improving it to find proofs for
; those theorems.  The proveall process could skip theorems marked with `*'
; (see the handling of AVOIDSTAR in the 14 September, 1973, POP-2 source code
; listings-f-and-h.txt).  The 14 September, 1973, version of PLTP in fact
; proves some of the theorems marked with `*' in the 2 September, 1973
; [THEOREMS] file, as evidenced by the fact that those theorems are listed as
; proved in Moore's dissertation and the 1975 JACM paper:

;  [T 6 11 *]::
;  [EQUAL [MEMBER A [SORT B]] [MEMBER A B]]

;  [T 6 13 *]::
;  [EQUAL [COUNT A B] [COUNT A [SORT B]]]

;  [T 6 17 *]::
;  [EQUAL [EQUAL [SORT A] A] [ORDERED A]]

; Random Anectdote: In my oral exam, which included a demonstration of PLTP,
; the committee asked if PLTP had proved that [SORT B] is a permutation of B
; and I replied that it had not, even though I had demonstrated a proof that
; [SORT A] is ORDERED.  The committee then challenged me to try the permutation
; theorem, which we formalized in terms of COUNT and proved for the first time
; in the oral exam.

; It is curious that one of the current failures, [T 8 3] above, does not
; have a `*' in its name.  I cannot explain that and it is one of the reasons
; I undertook the work here.

; The Argument:

; I am convinced that no version of PLTP could prove [T 8 1 *] or [T 8 3].  The
; basic reason is that the only proofs I can think of involve steps that PLTP
; was incapable of taking.  There are two basic difficulties with these
; theorems.

; First, both theorems involve BINADD, a binary addition algorithm.  BINADD is
; used explicitly in (T 8 1 *) and is involved in the definition of BINARYOF,
; which is used explicitly in (T 8 3).  Most problematically, BINADD is defined
; as a ``reflexive function'': when the algorithm needs to carry into a higher
; position it does the addition of the higher bits without carrying and then
; calls itself again on that partial sum and the binary representation of 1.
; No induction that PLTP could do could unwind this recursion adequately.

; Second, both proofs involve the knowledge that BINARYOF returns a well-formed
; binary number, i.e., a list of 1s and 0s.  Such knowledge can only be
; captured in PLTP by its inference of type functions.  But BINADD, which is
; used in the definition of BINARYOF, returns a well-formed binary number only
; if its inputs are well-formed and PLTP could not infer type functions that
; were dependent on the types of the actuals.

; A less principled argument that PLTP could not do these proofs is that ACL2
; cannot prove the ``corresponding'' theorems automatically without help from
; the user.  This is significant since ACL2 is, many senses, our current ``best
; effort'' at improving PLTP!

; This file is actually a certified ACL2 book.  To explore the issues raised in
; these two PLTP proof attempts, I formalize the notion of the
; ``corresponding'' ACL2 theorems, show that ACL2 cannot prove them
; automatically, then guide ACL2 to proofs with a few well-chosen lemmas, and
; and observe that the proofs involve steps beyond those known to PLTP.

; But it is, of course, possible that there is a PLTP-reachable proof that I'm
; not seeing!

; SO I INVITE THE READER OF THIS DOCUMENT TO TRY TO FIND SIMPLER ACL2 PROOFS OF
; THESE EXACT THEOREMS WITH THESE EXACT DEFINITIONS.

; By ``corresponding'' theorems I mean ACL2 formulas and functions that are
; restricted to the PLTP universe of CONS-trees built from NIL.  This universe
; is recognized by pltp-objectp defined below.  I'm willing to stipulate that
; this universe is closed under PLTP functions and to provide that information
; to ACL2 ``for free'' in the sense that I don't expect ACL2 to discover that.
; Each time I introduce the ACL2 correspondent of a PLTP function I will state
; and have ACL2 prove that it stays in the PLTP universe and make that
; available as both a :rewrite rule and a :generalize rule.

; The ACL2 correspondent of a PLTP function definition

; (DEFINE (f (LAMBDA (v1 ... vn) body)))

; will be

; (defun f (v1 ... vn)
;  (if (and (pltp-objectp v1) ... (pltp-objectp vn))
;      body'
;      '???))

; where body' is the simplified body stored by PLTP(A)'s DEFINE.  This is the
; same body stored by the 1973 PLTP DEFINE for functions in the standard
; proveall since it ``normalates'' the definitions.

; The correspondent of a theorem is just the PLTP formula with the additional
; hypotheses that the variables are pltp-objects (and if the variables are
; ``numeric'' then we also add those hypotheses explicitly).  The closure
; theorems insure that the ??? exits on all the functions are never taken.

(in-package "PLTP")
(include-book "std/testing/must-fail" :dir :system)

(defun pltp-objectp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (pltp-objectp (car x))
           (pltp-objectp (cdr x)))
      (eq x nil)))

(defconst *pltp-zero* nil)
(defconst *pltp-one* (cons nil nil))
(defconst *pltp-t* (cons nil nil))

; Here is the ACL2 correspondent of PLTP's NUMBERP, which is implicit in the
; two theorems.

; I have to use a different name for NUMBERP since that is a Common Lisp
; function and cannot be redefined in ACL2.  I use pltp-numberp.

; The uppercase expressions below are taken directly from the stored DEFN
; properties of the functions concerned.  E.g. see (props NUMBERP) after doing
; (proveall :standard).

#||
PLTP !>(props numberp)
((ARITY 1)
 (DEFN (LAMBDA (X)
               (IF X (IF (CAR X) NIL (NUMBERP (CDR X)))
                   (CONS NIL NIL))))
 (BOOLEAN T)
 (NUMERIC T)
 (TYPEFN NUMBERPTYPE))
||#

(defun pltp-numberp (x)
  (declare (xargs :guard t))
  (if (pltp-objectp x)
      (IF X (IF (CAR X) NIL (PLTP-NUMBERP (CDR X)))
          (CONS NIL NIL))
      '???))

(defthm universe-closed-pltp-numberp
  (implies (pltp-objectp x)
           (pltp-objectp (pltp-numberp x)))
  :rule-classes (:rewrite :generalize))

; -----------------------------------------------------------------

#||
(PROVE
 (T 8 1 *)
 (implies (and (numberp n)
               (numberp m))
          (EQUAL (BINARYOF (PLUS N M))
                 (BINADD (BINARYOF N) (BINARYOF M)))))
||#

; Analysis of (T 8 1 *)

; ACL2 cannot prove the correspondent of this formula automatically but it can
; do so if it knows that BINADD returns a binary number when given two binary
; numbers and that BINARYOF produces a binary number.  If that information is
; required for every proof then there was no way PLTP could have proved this
; theorem because its type inference was context-free: it could not express the
; idea (as a TYPEFN) that the type of a function's output depended on the type
; of its input.

(defun binadd (x y)
  (declare (xargs :guard t
                  :measure (+ (len x) (len y))))
  (if (and (pltp-objectp x)
           (pltp-objectp y))
      (IF X
          (IF Y
              (IF (CAR X)
                  (IF (CAR Y)
                      (if (mbt (< (+ 1 (len (binadd (cdr x) (cdr y))))
                                  (+ (len x) (len y))))
                          (CONS NIL
                                (BINADD (CONS (CONS NIL NIL) NIL)
                                        (BINADD (CDR X) (CDR Y))))
                          '???)
                      (CONS (CONS NIL NIL)
                            (BINADD (CDR X) (CDR Y))))
                  (CONS (CAR Y) (BINADD (CDR X) (CDR Y))))
              X)
          Y)
      '???))

; The following fact was proved during the guard proof of binadd above.  But it
; is also needed explicitly later so I state it as a :linear rule.

(defthm eliminate-the-mbt-in-binadd
  (implies (and (pltp-objectp x) (pltp-objectp y))
           (< (+ 1 (len (binadd x y)))
              (+ 2 (len x) (len y))))
  :rule-classes :linear)

(defthm universe-closed-binadd
  (implies (and (pltp-objectp x)
                (pltp-objectp y))
           (pltp-objectp (binadd x y)))
  :rule-classes (:rewrite :generalize))

(defun binaryof (x)
  (declare (xargs :guard t))
  (if (pltp-objectp x)
      (IF X
          (BINADD (CONS (CONS NIL NIL) NIL)
                  (BINARYOF (CDR X)))
          NIL)
      '???))

(defthm universe-closed-binaryof
  (implies (pltp-objectp x)
           (pltp-objectp (binaryof x)))
  :rule-classes (:rewrite :generalize))

(defun plus (x y)
  (declare (xargs :guard t))
  (if (and (pltp-objectp x)
           (pltp-objectp y))
      (IF X (CONS NIL (PLUS (CDR X) Y)) Y)
      '???))

(defthm universe-closed-plus
  (implies (and (pltp-objectp x)
                (pltp-objectp y))
           (pltp-objectp (plus x y)))
  :rule-classes (:rewrite :generalize))

; This demonstrates that ACL2 cannot prove (T 8 1 *) automatically -- at least
; in fewer than a million steps.

(acl2::must-fail
 (with-prover-step-limit
  1000000
  (defthm t-8-1-*
    (implies (and (pltp-objectp n)
                  (pltp-objectp m)
                  (pltp-numberp n)
                  (pltp-numberp m))
             (EQUAL (BINARYOF (PLUS N M))
                    (BINADD (BINARYOF N) (BINARYOF M)))))))

; But here is a user-directed proof:

; If we introduce the PLTP predicate BINARYP:

#||
PLTP !>(DEFINE
         (BINARYP
          (LAMBDA (X)
                  (IF X
                      (IF (OR (EQUAL (CAR X) 1)
                              (EQUAL (CAR X) 0))
                          (BINARYP (CDR X))
                          NIL)
                      T))))

BINARYP
PLTP !>(props BINARYP)
((ARITY 1)
 (DEFN (LAMBDA (X)
               (IF X
                   (IF (IF (CAR X)
                           (EQUAL (CAR X) (CONS NIL NIL))
                           (CONS NIL NIL))
                       (BINARYP (CDR X))
                       NIL)
                   (CONS NIL NIL))))
 (BOOLEAN T)
 (NUMERIC T)
 (TYPEFN BINARYPTYPE))
||#

(defun binaryp (x)
  (declare (xargs :guard t))
  (if (pltp-objectp x)
      (IF X
          (IF (IF (CAR X)
                  (EQUAL (CAR X) (CONS NIL NIL))
                  (CONS NIL NIL))
              (BINARYP (CDR X))
              NIL)
          (CONS NIL NIL))
      '???))

(defthm universe-closed-binaryp
  (implies (pltp-objectp x)
           (pltp-objectp (binaryp x)))
  :rule-classes (:rewrite :generalize))

(defthm binaryp-binaryof
  (implies (pltp-objectp x)
           (binaryp (binaryof x)))
  :rule-classes (:rewrite :generalize))

(defthm binaryp-binadd
  (implies (and (pltp-objectp m)
                (pltp-objectp n)
                (pltp-numberp m)
                (pltp-numberp n))
           (binaryp (binadd m n)))
  :rule-classes (:rewrite :generalize))

; One way to prove t-8-1-* now is to add the hint

; (("Goal" :in-theory (disable (:GENERALIZE UNIVERSE-CLOSED-BINARYOF))))

; because if you add the extra PLTP-OBJECTP hyp that the generalize rule
; introduces during generalization the system does the wrong induction on a
; subgoal.

; Alternatively, you can leave that enabled but hint the right induction

; (("Subgoal *1/6'7'" :induct (BINADD BF0 BF)))

; But a more robust approach is to prove the general fact:

(defthm binadd-associative-instance
  (implies (and (pltp-objectp y)
                (pltp-objectp z)
                (binaryp y)
                (binaryp z))
           (equal (binadd (binadd '((NIL)) y) z)
                  (binadd '((NIL)) (binadd y z)))))

(defthm t-8-1-*
  (implies (and (pltp-objectp n)
                (pltp-objectp m)
                (pltp-numberp n)
                (pltp-numberp m))
           (EQUAL (BINARYOF (PLUS N M))
                  (BINADD (BINARYOF N) (BINARYOF M))))
  :rule-classes nil)

#||

; Interestingly, PLTP can prove the three lemmas we use above.

(prove binaryp-binaryof
       (binaryp (binaryof x)))

(prove binaryp-binadd
  (implies (and (numberp m)
                (numberp n))
           (binaryp (binadd m n))))

(prove binadd-associative-instance
  (implies (and (binaryp y)
                (binaryp z))
           (equal (binadd (binadd (cons 1 nil) y) z)
                  (binadd (cons 1 nil) (binadd y z)))))

; The induction used on T-8-1-* is ``suggested by (PLTP-OBJECTP N),
; but modified to accommodate (PLUS N M).''  However, the simpler
; induction suggested by (PLUS N M) alone suffices for ACL2, and
; PLTP would choose that induction.  So (T 8 1 *) was probably in
; reach of PLTP had it been able to use lemmas!
; That didn't happen until around 1977 with

; A Lemma Driven Automatic Theorem Prover for Recursive Function Theory,
; R.S. Boyer and J S. Moore. Proceedings of the 5th International Joint
; Conference on Artificial Intelligence, 1977, pp. 511-519.

||#

;-----------------------------------------------------------------
#||
(PROVE
 (T 8 3)
 (EQUAL (LINEAR (CDR (BINARYOF N)))
        (HALF N)))
||#

; LINEAR is defined in terms of DOUBLE, so we must introduce
; the correspondent of DOUBLE:

(defun double (x)
  (declare (xargs :guard t))
  (if (pltp-objectp x)
      (IF X (CONS NIL (CONS NIL (DOUBLE (CDR X))))
          NIL)
      '???))

(defthm universe-closed-double
  (implies (pltp-objectp x)
           (pltp-objectp (double x)))
  :rule-classes (:rewrite :generalize))

(defun linear (x)
  (declare (xargs :guard t))
  (if (pltp-objectp x)
      (IF X
          (IF (CAR X)
              (CONS NIL (DOUBLE (LINEAR (CDR X))))
              (DOUBLE (LINEAR (CDR X))))
          NIL)
      '???))

(defthm universe-closed-linear
  (implies (pltp-objectp x)
           (pltp-objectp (linear x)))
  :rule-classes (:rewrite :generalize))


(defun half (x)
  (declare (xargs :guard t))
  (if (pltp-objectp x)
      (IF X
          (IF (CDR X)
              (CONS NIL (HALF (CDR (CDR X))))
              NIL)
          NIL)
      '???))

(defthm universe-closed-half
  (implies (pltp-objectp x)
           (pltp-objectp (half x)))
  :hints (("Goal" :induct (half x)))
  :rule-classes (:rewrite :generalize))

; I have no idea why this proof attempt loops indefinitely when the lemma
; mentioned below is available!

(acl2::must-fail
 (with-prover-step-limit
  1000000
  (defthm t-8-3
    (implies (and (pltp-objectp n)
                  (pltp-numberp n))
             (EQUAL (LINEAR (CDR (BINARYOF N)))
                    (HALF N)))
    :hints (("Goal" :in-theory (disable universe-closed-linear))))))

; And here is a user-directed proof:

; This happens to be in the standard proveall:
(defthm t-8-2
  (implies (and (pltp-objectp n)
                (pltp-numberp n))
           (EQUAL (LINEAR (BINARYOF N)) N)))

; The presence of the pltp-objectp and pltp-numberp fool ACL2 into picking the
; wrong induction, so I have to tell it to induct on (half n).  Interestingly,
; PLTP(A) can prove, automatically, its version of both of the theorems below:

(defthm binaryof-half
  (implies (and (pltp-objectp n)
                (pltp-numberp n)
                )
           (EQUAL (CDR (BINARYOF N))
                  (BINARYOF (HALF N))))
  :hints (("Goal" :induct (half n))))

(defthm pltp-numberp-half
  (implies (and (pltp-objectp n)
                (pltp-numberp n))
           (PLTP-NUMBERP (HALF N)))
  :hints (("Goal" :induct (half n))))

(defthm t-8-3
   (implies (and (pltp-objectp n)
                 (pltp-numberp n))
            (EQUAL (LINEAR (CDR (BINARYOF N)))
                   (HALF N)))
   :hints (("Goal" :do-not-induct t))
   :rule-classes nil)

; The :do-not-induct hint just makes clear to the reader that the proof is just
; rewriting now: replace (CDR (BINARYOF N)) by (BINARYOF (HALF N)) and then
; apply T-8-2 to rewrite (LINEAR (BINARYOF (HALF N))) to (HALF N).

; Again, PLTP can prove the two lemmas we used:

#||
(prove binaryof-half
       (implies (numberp n)
                (EQUAL (CDR (BINARYOF N))
                       (BINARYOF (HALF N)))))

(prove numberp-half
       (implies (numberp n)
                (NUMBERP (HALF N))))
||#


; There is another, more direct, proof of T-8-3.  Note that we tell ACL2 to
; induct on (HALF N) and we disable the lemmas we proved a moment ago.

(defthm t-8-3-direct
  (implies (and (pltp-objectp n)
                (pltp-numberp n))
           (EQUAL (LINEAR (CDR (BINARYOF N)))
                  (HALF N)))
  :hints (("Goal"
           :induct (HALF N)
           :in-theory (disable binaryof-half
                               pltp-numberp-half)))
  :rule-classes nil)

; However, the proof above crucially relies on the ACL2 generalization lemma
; that BINARYOF returns a BINARYP result.  The proof fails and generates a NIL
; subgoal if this generalization lemma is unavailable:

(acl2::must-fail
 (defthm t-8-3-direct-without-binaryp-binaryof
   (implies (and (pltp-objectp n)
                 (pltp-numberp n))
            (EQUAL (LINEAR (CDR (BINARYOF N)))
                   (HALF N)))
   :hints (("Goal"
            :induct (HALF N)
            :in-theory (disable binaryof-half
                                pltp-numberp-half
                                (:GENERALIZE BINARYP-BINARYOF))))))

; But this raises an interesting possibility: Perhaps [T 8 3] was proved by
; PLTP (hence, no `*' in its name) because PLTP could infer BINARYP as the
; TYPEFN for BINARYOF.  Here is the definition of BINARYOF:

; (DEFINE
;   (BINARYOF
;    (LAMBDA (X) (COND X (BINADD (CONS 1 NIL) (BINARYOF (CDR X))) NIL))))

; PLTP(A) infers the TYPEFN CONSTTRUE, i.e., PLTP(A) can't infer any
; restriction on the output of BINARYOF.  Clearly, given the way
; type-expr works, PLTP would have had to write BINARYP as the TYPEFN
; of BINADD in order to infer it for BINARYOF.  So here's BINADD:

; (DEFINE
;   (BINADD
;    (LAMBDA
;     (X Y)
;     (COND
;      X
;      (COND Y
;            (COND (CAR X)
;                  (COND (CAR Y)
;                        (CONS 0 (BINADD (CONS 1 NIL) (BINADD (CDR X) (CDR Y))))
;                        (CONS 1 (BINADD (CDR X) (CDR Y))))
;                  (CONS (CAR Y) (BINADD (CDR X) (CDR Y))))
;            X)
;      Y))))

; But this function sometimes returns one of arguments, X or Y.  And so the
; ONLY way the output could satisfy BINARYP is if the arguments are.  And PLTP
; had no way to express that idea... unless the definition of BINADD were
; changed somehow to coerce those outputs.  I've tried several versions of BINADD
; and BINARYOF without success.
