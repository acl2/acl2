; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "simplify-under-hyps")

; How to Use Simplify-Clause1 to Simplify a Term under Some Hypotheses
; J Strother Moore
; June, 2013

; (See the list of possible improvements below.)

; Suppose we want to simplify some term, term, under some hyps.  Create the
; clausal form of (IMPLIES (AND . hyps) (IF-TRACKER NIL term)) and repeatedly
; simplify it with simplify-clause1.  The result is a set of clauses, each of
; which contains a final IF-TRACKER literal.  All other literals in all the
; clauses are irrelevant simplifications of parts of hyp.

; The Term Recovery Algorithm

; How can we recover a simplified version of term under hyps from the
; simplified clauses returned by iterating the simplification via
; simplify-clause1 of the clausal form of (IMPLIES (AND hyps) (p term))?

; The answer is in three parts.  First, we introduce a new undefined function
; that enjoys the following property:

; if-tracker-rule:
; (IF-TRACKER rtests (IF a b c))
; =
; (IF a
;     (IF-TRACKER (CONS (HIDE a) rtests) b)
;     (IF-TRACKER (CONS (HIDE (NOT a)) rtests) c))

; Note on the HIDE: Why do we HIDE the test, a?  If we did not hide it, it
; would ALWAYS be replaced by T or NIL because of the governing occurrence of a
; in the test of the right-hand side IF.  But these are the tests we'll
; reassemble into an IF later; therefore, it would have been nice if they were
; fully simplified.  But, in general, they'll have been only partially
; simplified, namely from rewriting that produces the (IF a b c), before the a
; is lifted out.

; Second, we repeatedly simplify the clausal form of

; (IMPLIES (AND . hyps) (IF-TRACKER NIL term))

; to obtain a set of clauses and we grab from them the concluding IF-TRACKER
; terms.  From these terms we create a list of ``IF-tracker triple'' or
; ITTs.  The ITT obtained from

; (IF-TRACKER (CONS (HIDE a1) ... (CONS (HIDE ak) NIL)...) terma)

; is (k (a1 ... ak) terma).  We call k the ``size'' of the ITT, the ai
; are the ``tests'' and terma is the ``result.''

; Third, given a set of ITTs, we apply the following algorithm to produce
; a term or an error.  We first define two new notions on ITTs.

; Let x and y be two ITTs:
; x: (k (a1 ... ak) terma)
; y: (j (b1 ... bj) termb)

; Without loss of generality, let x be the smaller of the two, i.e., suppose
; k <= j.

; We say that x and y are ``complementary'' iff k > 0,
; a1 is the complement of b1, and every other ai is among the bi.
; The result of ``fusing'' x with a complementary y is:

; (k-1 (b2 ... bj) (IF a1 terma termb))  -- if a1 is positive
; (k-1 (b2 ... bj) (IF b1 termb terma))  -- if a1 is negative

; Note that we use the larger of the set of tests in the fusion.

; Fusing should, additionally, apply (if x y y) to eliminate unnecessary
; tests.

; The term recovery algorithm operates on a list of ITTs, iteratively
; applying the rules below.

; ITT Rule 0a:  Delete duplicate ITTs from the list.

; ITT Rule 0b: Delete all pure tests from the list (i.e., tests that only occur
; in one parity).

; ITT Rule 1: If there is a complementary pair of ITTs, fuse the smaller
; with each of its complement in the list and replace all of the ITT
; involved by their fusions.  Note that this rule decreases by one the
; number of ITTs in the set.

; ITT Rule 2: If there are no complementary pairs, select the ITT with the
; largest size and if the size is greater than 0, decrement the size by 1 and
; delete the leading test (a1).  That is, replace the selected ITT by the
; reduced one.  Note that its size has decreased.

; Thus, every step reduces the sum of the sizes of the ITTs in the set.
; Eventually, there will be no applicable rule.  If the set of ITTs then has
; one element and its size is 0, the recovered term is the result term of that
; surviving ITT.  Otherwise, an error is caused.

; Note that ITT Rule 1 is justified as follows: if A --> p and -A B --> q, then
; B --> (if A p q).

; Note that if ITT Rule 2 is applicable, then the selected ITT has no
; complement in the set.  But since the IF-tracker-rule in fact did introduce a
; complement, the only way an uncomplemented ITT can arise is if one of the
; generated clauses was proved.  (This observation also relies on the fact that
; we cannot prove an IF-TRACKER term, even by substituting a constant for its
; second argument, and we did not eliminate the literal with the (if x y y)
; reduction because the uncomplemented literal survived.)  Let's assume the
; uncomplemented ITT is positive.  Thus, the if-tracker-rule added the two
; clauses:

; {-hyp1 ... -hypj -a1 (IF-TRACKER (CONS (HIDE a1) rtests) b)}
; {-hyp1 ... -hypj  a1 (IF-TRACKER (CONS (HIDE (NOT a1)) rtests) c)}

; Furthermore, lets assume that the second clause was proved.  Hence, we know
; that hyps --> a1.  This justifies ITT Rule 2.  However, to prove that the
; term produced by Rule 2 is actually equivalent to the input term, it might be
; necessary to force the prover to split on a, as happened when if-tracker-rule
; fired.  We could do that by making Rule 2 produce the new ITT

;  (k-1 (a2 ... ak) (IF a1 terma :DONT-CARE))

; But I don't want to introduce a spurious apparent value into the
; IF-expression being built.  So I'll wait to modify Rule 2 until this case
; arises.

; Possible Improvements

; Here I record a couple of ideas someone might want to pursue to improve this
; utility/

; (1) If you're looking for a new approach, try the idea of putting markers in
; the clause, so that (if-tracker (IF a b c)) rewrites to

; (if (marker (hide a)) (if-tracker (IF a b 't)) (if-tracker (IF a 't c)))

; Note that clausifying this (assuming if-tracke is the id fn):

; (clausify '(if (marker (hide a)) (IF a b 't) (IF a 't c)) nil nil nil)
; =
; (((NOT (MARKER (HIDE A))) (NOT A) B)
;  ((MARKER (HIDE A)) A C))
; So it is possible to have MARKERs in the clause with the acutal simplified
; literals in between.  The last literal will be a codewalker-tip of some sort so each
; final clause will look like

; {+/-(MARKER hyp1) <simplified cases of hyp1>
;  +/-(MARKER hyp2) <simplified cases of hyp2>
;  ...
;  +/-(MARKER hypk) <simplified cases of hypk>
;  (TIP concl)}

; (2) I am not totally convinced we need Rule 2.  I think we do, because it
; eliminates tests that originally had a "bogus" match that has since been
; eliminated by Rule 1.  But it deserves thought.

(in-package "ACL2")

(include-book "if-tracker")

(program)
(set-state-ok t)

(mutual-recursion

(defun simplify-clause1* (top-clause hist rcnst wrld state step-limit n ans forcing-occurredp)

; This just applies simplify-clause1 repeatedly until no change occurs (or a
; max of n iterations is done).  We accumulate all the simplified clauses into
; ans, which must initially consist entirely of fully simplified clauses (and
; is usually initially nil).  We return the final set of clauses.  If ans was
; initially nil and the resulting set is a singleton containing top-clause,
; then nothing happened.

  (cond
   ((zp n)
    (mv (cons top-clause ans) forcing-occurredp))
   (t
    (mv-let
     (step-limit1 signal1 new-clauses ttree1)
     (simplify-clause1 top-clause hist rcnst wrld state step-limit)
     (declare (ignore step-limit1 signal1))
     (cond ((and (consp new-clauses)
                 (equal (cdr new-clauses) nil)
                 (equal (car new-clauses) top-clause))
            (mv (cons top-clause ans) forcing-occurredp))
           (t (simplify-clause1*-lst new-clauses
                                     hist rcnst wrld state
                                     step-limit
                                     (- n 1) ans
                                     (or forcing-occurredp
                                         (contains-assumptionp ttree1)))))))))

(defun simplify-clause1*-lst (clauses hist rcnst wrld state step-limit n ans forcing-occurredp)
  (cond ((endp clauses)
         (mv ans forcing-occurredp))
        (t (mv-let (ans forcing-occurredp)
                   (simplify-clause1* (car clauses)
                                      hist rcnst wrld state step-limit n
                                      ans forcing-occurredp)
                   (simplify-clause1*-lst
                    (cdr clauses)
                    hist rcnst wrld state step-limit n
                    ans forcing-occurredp))))))

(defrec itt (size rtests result) t)

(defun strip-cons-hides (term)

; Term is of the form

; (CONS (HIDE lit1) (CONS (HIDE lit2) ... (CONS (HIDE litk) 'NIL)...))

; representing a true-list of liti values.  We return the list of liti, (lit1
; lit2 ... litk).  If we see anything unusual -- meaning term is not of the
; expected form -- we just quit looking.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        (t (case-match term
             (('CONS ('HIDE ('NOT x)) rest)
              (cons `(NOT ,x) (strip-cons-hides rest)))
             (('CONS ('HIDE x) rest)
              (cons x (strip-cons-hides rest)))
             (&

; If term is something unusual.

              nil)))))

(defun convert-if-tracker-term-to-itt (term)
  (let ((rtests (strip-cons-hides (fargn term 1))))
    (make itt
          :size (length rtests)
          :rtests rtests
          :result (fargn term 2))))

(defun collect-if-tracker-triples (clauses)

; We collect the ITTs corresponding to those IF-TRACKER literals occuring last
; in each clause of clauses.  We cause an error if some clause does not
; conclude with a IF-TRACKER literal.  Such clauses shouldn't exist!

  (cond
   ((endp clauses) nil)
   (t (let ((lit (car (last (car clauses)))))
        (cond
         ((and (nvariablep lit)
               (not (fquotep lit))
               (eq (ffn-symb lit) 'if-tracker))
          (add-to-set-equal
           (convert-if-tracker-term-to-itt lit)
           (collect-if-tracker-triples (cdr clauses))))
         (t (er hard 'collect-if-tracker-triples
                "It was thought every simplified IF-TRACKER clause ~
                 concluded with a final IF-TRACKER literal, but the ~
                 following clause does not!  ~X01"
                (car clauses)
                nil)))))))

(defun pure-litp (lit all-lits)

; A literal is pure in a set if the only occurrence of its atom is always with
; a fixed sign.  For example, in (A B -B -C D -D), both A and C are pure.  We
; know that lit occurs in all-lits.  So if its negation also occurs, the
; lit is not pure.  Note:  This definition of "pure literal" is similar to
; but not the same as the notion from resolution, where a literal is pure
; with respect to a set of clauses (a set of sets of literals) and must always
; appear with the same sign in any clause containing the atom of the literal.

  (not (member-equal (dumb-negate-lit lit) all-lits)))

(defun delete-pure-tests-from-lst (tests all-lits)
  (cond ((endp tests) nil)
        ((pure-litp (car tests) all-lits)
         (delete-pure-tests-from-lst (cdr tests) all-lits))
        (t (cons (car tests)
                 (delete-pure-tests-from-lst (cdr tests) all-lits)))))

(defun delete-pure-tests-from-itt (itt all-lits)
  (let ((rtests (delete-pure-tests-from-lst (access itt itt :rtests)
                                            all-lits)))
    (make itt
          :size (len rtests)
          :rtests rtests
          :result (access itt itt :result))))

(defun delete-pure-tests-from-itt-lst1 (itt-lst all-lits)
  (cond
   ((endp itt-lst) nil)
   (t (add-to-set-equal
       (delete-pure-tests-from-itt (car itt-lst) all-lits)
       (delete-pure-tests-from-itt-lst1 (cdr itt-lst) all-lits)))))

(defun collect-all-tests-from-itts (itt-lst)
  (cond ((endp itt-lst) nil)
        (t (union-equal (access itt (car itt-lst) :rtests)
                        (collect-all-tests-from-itts (cdr itt-lst))))))

(defun delete-pure-tests-from-itt-lst (itt-lst)
  (delete-pure-tests-from-itt-lst1
   itt-lst
   (collect-all-tests-from-itts itt-lst)))

(defun asymmetric-complementary-ittsp (itt1 itt2)

; Two itts are complementary if the leading tests are complementary, and the
; remaining tests of the smaller are a subset of those of the larger.  For
; example, (-A B D) ==> x and (A B C D -E) ==> y are complementary.  This
; function is, in addition, asymmetric: it only returns T if itt1 is the
; smaller of the two.  That is, while the notion of complementarity is
; symmetric, asymmetric-complementary is not.  If itt1 and itt2 are
; complementary, then either (asymmetric-complementary-ittsp itt1 itt2) or
; (asymmetric-complementary-ittsp itt2 itt1) holds.  (Both could hold.)

  (and (<= (access itt itt1 :size) (access itt itt2 :size))
       (not (eql (access itt itt1 :size) 0))
       (complementaryp (car (access itt itt1 :rtests))
                       (car (access itt itt2 :rtests)))
       (subsetp-equal (cdr (access itt itt1 :rtests))
                      (cdr (access itt itt2 :rtests)))))

(defun find-matching-itts1 (itt1 itt-lst)

; Return every itt in itt-lst that asymmetrically complementary to itt1.  The
; itts in the resulting list are all at least as large as itt1.

  (cond
   ((endp itt-lst) nil)
   ((asymmetric-complementary-ittsp itt1 (car itt-lst))
    (cons (car itt-lst)
          (find-matching-itts1 itt1 (cdr itt-lst))))
   (t (find-matching-itts1 itt1 (cdr itt-lst)))))

(defun find-matching-itts2 (candidates itt-lst)

; We look for any itt1 in candidates that is asymmetrically complementary with
; a (weakly larger) itt2 in itt-lst.  We return (mv itt1 itt2-lst), where
; itt2-lst is the list of all itt2 found.  Note: the fact that itt1 may be in
; itt-lst is of no concern since it is not complementary to itself.

  (cond
   ((endp candidates) (mv nil nil))
   (t (let* ((itt1 (car candidates))
             (itt2-lst (find-matching-itts1 itt1 itt-lst)))
        (if itt2-lst
            (mv itt1 itt2-lst)
            (find-matching-itts2 (cdr candidates) itt-lst))))))


(defun find-matching-itts (itt-lst)

; If there are two itts, itt1 and itt2, in itt-lst that are complementary, we
; return (mv itt1 itt2-lst), where itt2-lst is the list of all itts in itt-lst
; that are asymmetrically complementary to itt1 and itt1 is the smaller of itts
; concerned.

  (find-matching-itts2 itt-lst itt-lst))

(defun fuse-complementary-itts (itt1 itt2)

; We fuse itt1 and itt2, which are asymmetrically complementary.  Itt1 is the
; smaller.

  (let ((new-size (- (access itt itt2 :size) 1))
        (lit1 (car (access itt itt1 :rtests)))
        (lit2 (car (access itt itt2 :rtests)))
        (new-rtests (cdr (access itt itt2 :rtests)))
        (result1 (access itt itt1 :result))
        (result2 (access itt itt2 :result)))
    (cond ((and (nvariablep lit2)
                (not (fquotep lit2))
                (eq (ffn-symb lit2) 'NOT))
           (make itt
                 :size new-size
                 :rtests new-rtests
                 :result (if (equal result1 result2) ; (IF x y y) = y
                             result1
                             (cons-term* 'IF lit1 result1 result2))))
          (t (make itt
                   :size new-size
                   :rtests new-rtests
                   :result (if (equal result1 result2)
                               result1
                               (cons-term* 'IF lit2 result2 result1)))))))

(defun fuse-complementary-itts-lst (itt1 itt2-lst)
  (cond ((endp itt2-lst) nil)
        (t (add-to-set-equal (fuse-complementary-itts itt1 (car itt2-lst))
                             (fuse-complementary-itts-lst itt1 (cdr itt2-lst))))))

(defun find-biggest-itt1 (itt-lst ans)
  (cond ((endp itt-lst) ans)
        ((< (access itt ans :size) (access itt (car itt-lst) :size))
         (find-biggest-itt1 (cdr itt-lst) (car itt-lst)))
        (t (find-biggest-itt1 (cdr itt-lst) ans))))

(defun find-biggest-itt (itt-lst)
  (cond ((endp itt-lst)
         (er hard 'find-biggest-itt
             "We have been given an empty list of IF-TRACKER itts.  This ~
              should never happen."))
        (t (find-biggest-itt1 (cdr itt-lst) (car itt-lst)))))

(defun shrink-itt (itt)
  (make itt
        :size (- (access itt itt :size) 1)
        :rtests (cdr (access itt itt :rtests))
        :result (access itt itt :result)))

(defun itt-term-recovery (itt-lst clause itt-lst0)

; The term recovery algorithm operates on a list of ITTs, iteratively
; applying the rules above.  The last two arguments are for error
; reporting only and should be the clause that we simplified to get
; itt-lst0 and the initial value of itt-lst.

  (cond
   ((endp itt-lst)
; This error message is copied below!  Keep the two copies in sync.
    (er hard 'itt-term-recovery
        "While simplifying~%~X10~%under the hypothesis~%~X20~%we produced the ~
         following set of ITTs, each of the form~%(size rtests ~
         result):~%~X30.~%On these ITTs The Algorithm produced the final ~
         set~%~X40.~%We cannot determine the answer term."
        nil ; evisc tuple
        (car (last clause))
        (case (len clause)
          (1 T)
          (2 (dumb-negate-lit (car clause)))
          (otherwise `(AND ,@(dumb-negate-lit-lst
                              (all-but-last clause)))))
        itt-lst0
        itt-lst))
   ((and (endp (cdr itt-lst))
         (eql (access itt (car itt-lst) :size) 0))
    (access itt (car itt-lst) :result))
   (t (mv-let
       (itt1 itt2-lst)
       (find-matching-itts itt-lst)
       (cond
        ((null itt1)

; There are no complementary itts.  So we delete the leading literal of the
; biggest itt, if any.

         (let ((itt (find-biggest-itt itt-lst)))
           (cond ((eql (access itt itt :size) 0)
; Keep this error message in sync with the one above just to provide maximal
; info if the algorithm fails.
                  (er hard 'itt-term-recovery
                      "While simplifying~%~X10~%under the ~
                       hypothesis~%~X20~%we produced the following set of ~
                       ITTs, each of the form~%(size rtests ~
                       result):~%~X30.~%On these ITTs The Algorithm produced ~
                       the final set~%~X40.~%We cannot determine the answer ~
                       term."
                      nil ; evisc tuple
                      (car (last clause))
                      (case (len clause)
                        (1 T)
                        (2 (dumb-negate-lit (car clause)))
                        (otherwise `(AND ,@(dumb-negate-lit-lst
                                            (all-but-last clause)))))
                      itt-lst0
                      itt-lst))
                 (t (itt-term-recovery ; ITT Rule 2
                     (add-to-set-equal (shrink-itt itt)
                                       (remove1-equal itt itt-lst))
                     clause itt-lst0)))))
        (t

; We have found complementary matching pairs of itts.  We replace them with the
; result of fusing them together.

         (itt-term-recovery                          ; ITT Rule 1
          (union-equal (fuse-complementary-itts-lst itt1 itt2-lst)
                       (remove1-equal itt1
                                      (set-difference-equal itt-lst itt2-lst)))
          clause itt-lst0)))))))

#||
; Below I define some useful testing functions and macros.  However, one must
; be careful testing itt-term-recovery because it's ability to reconstruct a
; term depends on the input being something actually produced by the
; not-yet-defined simplify-under-hyps.  There are two sensitivites.  First, in
; actual applications, simplification can eliminate (prove) a clause.  This
; means there will be some missing itts.  But we can never prove a
; CODEWALKER-WRAPPER-TIP and so the only way for simplify-under-hyps to
; eliminate a clause is if the tests are contradictory.  For example, while
; simplification might have produced a case split on (p x) and then later on (q
; x), if (p x) --> (q x) then the itt with tests ((p x) (not (q x))) might be
; missing.  But the only time an itt can be missing is if such dependencies
; exist among the tests.  One minor implication of this is that you can't get
; realistic tests cases for itt-term-recovery if you limit yourself to
; propositional itts.  Second, itt-term-recovery depends on the ordering of the
; tests.  IF-TRACKER produces them in reverse chronological order: the first
; test split on is the last test in the IF-TRACKER list.  So if you make up
; tests cases, you must write the tests in the right order.  Itt-term-recovery
; is probably also sensitive to the ordering of the itts themselves.  For these
; reasons it is best to limit tests to those actually produced via
; simplify-under-hyps.  In the tests below, I ran simplify-under-hyps on a
; terms, produced a set of itts, then reconstructed an equivalent term.  Then
; using trace$ I grabbed the set of itts given to itt-term-recovery to embed in
; the test.

; Note: The macros below treat every itt as though the results were always
; boolean.  That is, to test correctness we prove (with THM) the
; IFF-equivalence of the given set of ITTs (interpreted as formulas) and the
; recovered term.  In actual applications, the results are not generally
; Boolean and the true meaning of an ITT is a formula concluding in an EQUALity
; of the result with whatever term is being simplified.

(defun itt! (itt)
  `(implies (and ,@(access itt itt :rtests))
            ,(access itt itt :result)))

(defun itt*1 (lst)
  (cond ((endp lst) nil)
        (t (cons
            (itt! (car lst))
            (itt*1 (cdr lst))))))

(defun itt* (lst)
  (let ((temp (itt*1 lst)))
    (cond ((null temp) t)
          ((null (cdr temp)) (car temp))
          (t (cons 'and temp)))))

(defmacro fusion-thm (itt1 itt2)
  (let ((itt (fuse-complementary-itts itt1 itt2)))
    `(thm (implies ',itt
                   (iff (and ,(itt! itt1) ,(itt! itt2))
                        ,(itt! itt))))))

(defmacro recovery-thm (lst term)
  `(thm (and ,(equal (itt-term-recovery lst nil nil) term)
             (iff ,(itt* lst) ,term))))

(defmacro itt*-equal (itt1 itt2)
  `(thm (iff ,(itt* itt1) ,(itt* itt2))))

(defstub f (x) t)
(defstub g (x) t)
(defstub h (x) t)
(defstub p (x) t)
(defstub r (x y) t)
(defaxiom f1-f2-f3 (equal (f x) (if (p x) (g x) (h x))))
(defaxiom p->pg (implies (p x) (p (g x))))

; From simplify-under-hyps
; (if (f x) a b)
(recovery-thm
 ((2 ((NOT (H X)) (NOT (P X))) B)
  (2 ((H X) (NOT (P X))) A)
  (2 ((NOT (G X)) (P X)) B)
  (2 ((G X) (P X)) A))
 (IF (P X) (IF (G X) A B) (IF (H X) A B)))

; From simplify-under-hyps
; (if (f x) (r (f a) (f b)) (r (f a) (f c)))
(recovery-thm
 ((4 ((NOT (P C))
      (NOT (P A))
      (NOT (H X))
      (NOT (P X)))
     (R (H A) (H C)))
  (4 ((NOT (P C))
      (P A)
      (NOT (H X))
      (NOT (P X)))
     (R (G A) (H C)))
  (4 ((P C)
      (NOT (P A))
      (NOT (H X))
      (NOT (P X)))
     (R (H A) (G C)))
  (4 ((P C) (P A) (NOT (H X)) (NOT (P X)))
     (R (G A) (G C)))
  (4 ((NOT (P B))
      (NOT (P A))
      (H X)
      (NOT (P X)))
     (R (H A) (H B)))
  (4 ((NOT (P B)) (P A) (H X) (NOT (P X)))
     (R (G A) (H B)))
  (4 ((P B) (NOT (P A)) (H X) (NOT (P X)))
     (R (H A) (G B)))
  (4 ((P B) (P A) (H X) (NOT (P X)))
     (R (G A) (G B)))
  (4 ((NOT (P C))
      (NOT (P A))
      (NOT (G X))
      (P X))
     (R (H A) (H C)))
  (4 ((NOT (P C)) (P A) (NOT (G X)) (P X))
     (R (G A) (H C)))
  (4 ((P C) (NOT (P A)) (NOT (G X)) (P X))
     (R (H A) (G C)))
  (4 ((P C) (P A) (NOT (G X)) (P X))
     (R (G A) (G C)))
  (4 ((NOT (P B)) (NOT (P A)) (G X) (P X))
     (R (H A) (H B)))
  (4 ((NOT (P B)) (P A) (G X) (P X))
     (R (G A) (H B)))
  (4 ((P B) (NOT (P A)) (G X) (P X))
     (R (H A) (G B)))
  (4 ((P B) (P A) (G X) (P X))
     (R (G A) (G B))))
 (IF (P X)
     (IF (G X)
         (IF (P A)
             (IF (P B)
                 (R (G A) (G B))
                 (R (G A) (H B)))
             (IF (P B)
                 (R (H A) (G B))
                 (R (H A) (H B))))
         (IF (P A)
             (IF (P C)
                 (R (G A) (G C))
                 (R (G A) (H C)))
             (IF (P C)
                 (R (H A) (G C))
                 (R (H A) (H C)))))
     (IF (H X)
         (IF (P A)
             (IF (P B)
                 (R (G A) (G B))
                 (R (G A) (H B)))
             (IF (P B)
                 (R (H A) (G B))
                 (R (H A) (H B))))
         (IF (P A)
             (IF (P C)
                 (R (G A) (G C))
                 (R (G A) (H C)))
             (IF (P C)
                 (R (H A) (G C))
                 (R (H A) (H C)))))))

; From simplify-under-hyps
; (if (f a) (r (f (g a)) (h a)) b)
(recovery-thm
 ((3 ((NOT (P (G A))) (H A) (NOT (P A)))
     (R (H (G A)) (H A)))
  (3 ((P (G A)) (H A) (NOT (P A)))
     (R (G (G A)) (H A)))
  (2 ((NOT (H A)) (NOT (P A))) B)
  (2 ((NOT (G A)) (P A)) B)
  (2 ((G A) (P A)) (R (G (G A)) (H A))))
 (IF (P A)
     (IF (G A) (R (G (G A)) (H A)) B)
     (IF (H A)
         (IF (P (G A))
             (R (G (G A)) (H A))
             (R (H (G A)) (H A)))
         B)))

||#

; The following variable controls the max number of iterations of simplify-clause1
; while trying to explore the paths.

(defconst *simplify-clause1*-cnt* 100)

(defun simplify-under-hyps (hyps term state)

; Hyps is a list of fully-translated hypothesis terms, and term is the
; fully-translated term to simplify under the conjunction of hyps.  We return
; the resulting term or cause an error.  The resulting term is always in IF
; normal form (unless some case splitting heuristic of the ACL2 simplifier
; produces clauses containing IFs).

  (let ((wrld (w state))
        (clause (append (dumb-negate-lit-lst hyps)
                        (list (fcons-term* 'IF-TRACKER *nil* term)))))
    (mv-let (clause-lst forcing-occurredp)
            (simplify-clause1* clause
                               nil ; hist
                               (make-rcnst (ens state) wrld state
                                           :force-info t) ; allow forcing
                               wrld
                               state
                               (initial-step-limit wrld state)
                               *simplify-clause1*-cnt*
                               nil nil)
            (let ((itt-lst
                   (delete-pure-tests-from-itt-lst
                    (collect-if-tracker-triples clause-lst))))
              (prog2$
               (if forcing-occurredp
                   (cw "~%~%~
                        =================================================================~%~
                        We have FORCEd some hypotheses and ignored the ~
                        corresponding proof obligations!  The resulting ~
                        simplification is sound only if those proof obligations ~
                        are valid under the given hypotheses.  Thus, the ~
                        success of any subsequent proof of correctness depends ~
                        on our being able to establish the forced ~
                        hypotheses.  You should disable forcing (see :DOC ~
                        DISABLE-FORCING) to avoid forcing.  Unfortunately, this ~
                        utility does not support the use of forcing rounds or ~
                        ``immediate'' forcing.~%~
                        =================================================================~%~%")
                   nil)
               (itt-term-recovery itt-lst clause itt-lst))))))

