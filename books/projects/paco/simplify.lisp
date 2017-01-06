(in-package "PACO")

; In this section we develop rewrite-clause.

(defun split-on-assumptions (assumptions cl ans)

; Cl is a clause and ans is a set of clauses that will be our answer.
; Assumptions is a list of literals.  For each lit in assumptions
; we add a new clause to ans, obtained by adding lit to cl.

  (cond ((endp assumptions) ans)
        (t (split-on-assumptions
            (cdr assumptions)
            cl
            (conjoin-clause-to-clause-set
             (add-literal (car assumptions) cl nil)
             ans)))))

(defun rewrite-clause-action (lit branches)

; Lit is a term. Branches is the result of clausifying the result of
; rewriting lit.  We want to know if anything has happened.  The table
; below indicates our result:

; branches      result            meaning
;  {}          'shown-true      Lit was rewritten and clausified to
;                               the empty set, i.e., lit is T under our
;                               assumptions.
;  {NIL}       'shown-false     Lit was rewritten and clausified to
;                               the set containing the empty clause, i.e.,
;                               lit is NIL under our assumptions.
;  {{lit}}     'no-change       Neither rewrite nor clausify did anything.

;  otherwise   'change

  (cond ((consp branches)
         (cond ((null (cdr branches))
                (cond ((null (car branches))
                       'shown-false)
                      ((and (null (cdr (car branches)))
                            (equal lit (car (car branches))))
                       'no-change)
                      (t 'change)))
               (t 'change)))
        (t 'shown-true)))

(defun rewrite-clause-type-alist (tail new-clause ens wrld)

; We construct a type alist in which we assume (a) the falsity of
; every literal in tail except the first, and (b) the falsity of every
; literal in new-clause.

; We return a pair, (mv contradictionp type-alist), where
; contradictionp is t or nil and indicates whether we derived a contradiction.
; Type-alist is the constructed type-alist (or nil if we got a contradiction).

  (type-alist-clause (append new-clause (cdr tail)) nil ens wrld))

(defun rewrite-atm (atm not-flg type-alist wrld rcnst)

; This function rewrites atm in the given context, maintaining iff.

  (mv-let (knownp nilp)
          (known-whether-nil atm type-alist
                             (access rewrite-constant rcnst :ens)
                             wrld)
          (cond
           ((and knownp not-flg nilp)

; So we have reduced the atm to nil but it occurs negated in the
; clause and so we have reduced the literal to t, proving the clause.
; We report this reduction.  We don't report reductions of the literal
; to nil because that sometimes erases hypotheses added by hints.  See
; the comment in ACL2's rewrite-atm.  Paco doesn't support hints per
; se, but this rather subtle interaction of hints with the rewriter
; would be hard to track down if Paco didn't handle it this way.

            *nil*)
           ((and knownp (not not-flg) (not nilp))
            *t*)
           (t
            (rewrite-entry
             (rewrite atm nil)
             :type-alist type-alist
             :obj '?
             :iff-flg t
             :wrld wrld
             :fnstack nil
             :ancestors nil
             :rcnst rcnst
             :nnn *rewrite-nnn*)))))

; Now we develop the code for removing trivial equivalences.

(defun dumb-occurs-in-some-other-lit (term n cl i)

; We determine whether term occurs in some lit of clause cl other than
; the nth.  The number of the first literal of cl is i.

  (cond ((endp cl) nil)
        ((int= n i)
         (dumb-occurs-in-some-other-lit term n (cdr cl) (1+ i)))
        ((dumb-occur term (car cl)) t)
        (t (dumb-occurs-in-some-other-lit term n (cdr cl) (1+ i)))))


(defun find-trivial-equivalence1 (not-just-quotep-flg tail i cl avoid-lst)

; Cl is a clause.  Tail is a tail of cl and i is the position number
; of its first literal, starting from 0 for the first lit in cl.  See
; find-trivial-equivalence for the rest of the spec.

; It is important to keep in mind that the clause upon which we are working has
; not necessarily been rewritten.  Indeed, it is often the product of previous
; substitutions by the driver of this very function.  (Aside: once upon a time,
; the driver did not evaluate literals as they got stuffed with constants.  At
; the moment it does evaluate fns on constant args.  But that may
; change and so this function is written in a way that assumes the worst: there
; may be reducible terms in the clause.)  Thus, for example, a clause like
;    {(not (equal x 'a)) (not (equal y 'b)) (not (equal x y)) y ...}
; may first produce
;    {(not (equal y 'b)) (not (equal 'a y)) y ...}
; and then
;    {(not (equal 'a 'b)) 'b ...}
; which contains two unexpected sorts of literals: an equivalence with
; constant args and a constant literal.  We must therefore not be
; surprised by such literals.  However, we do not expect them to arise
; often enough to justify making our caller cope with the possibility
; that we've proved the clause.  So if we find such a literal and can
; decide the clause, we will just immediately report that there are no
; more usable equivalences and let the simplifier rediscover the
; literal.  If we find such a literal and can't decide the clause
; quickly based on equal and iff facts then we will just continue
; looking for usable equivalences.  The idea is that if the discovered
; lit makes the clause true, we don't expect to have screwed it up by
; continuing to substitute; and if the discovered lit just drops out,
; then our continued substitution is what we should have done.
; (Aside: If we persist in our decision to reduce literals when they
; are stuffed with constants, then these cases will not arise and all
; of the above is irrelevant.)

; Recall our output spec from find-trivial-equivalence.  The five results we
; return are the name of the condition detected (disposable or keeper), the
; location i of the literal, lhs, rhs and the literal itself.  Otherwise
; we return 5 nils.  (When we succeed, the "lhs" of our result is the term for
; which we are to substitute and "rhs" is the term by which we replace lhs.
; They may in fact come from the opposite sides of the equivalence term.)

  (cond ((endp tail) (mv nil nil nil nil nil))
        ((member-equal (car tail) avoid-lst)
         (find-trivial-equivalence1
          not-just-quotep-flg (cdr tail) (1+ i) cl avoid-lst))

; Below we handle variable V as though it were the literal (not (equal
; V nil)).  ACL2 handles (NOT V) as though it were (NOT (IFF V t)),
; but ACL2 supports equivalence relations (like IFF) and Paco doesn't.
; So we cannot handle (NOT V) as an equivalence.

        ((quotep (car tail))

; If the discovered lit is nil, then we just ignore it because it will drop
; out.  If the discovered lit is non-nil, this clause is true.  So we signal
; that there are no more usable equivs and let the simplifier get its hands
; on the clause to rediscover that it is true.

         (if (equal (car tail) *nil*)
             (find-trivial-equivalence1
              not-just-quotep-flg (cdr tail) (1+ i) cl avoid-lst)
             (mv nil nil nil nil nil)))
        ((or (variablep (car tail))
             (and (eq (ffn-symb (car tail)) 'NOT)
                  (and (nvariablep (fargn (car tail) 1))
                       (not (fquotep (fargn (car tail) 1)))
                       (eq (ffn-symb (fargn (car tail) 1)) 'EQUAL))))
         (let* ((atm
                 (if (variablep (car tail))
                     (fcons-term* 'equal (car tail) *nil*)
                   (fargn (car tail) 1)))
                (lhs (fargn atm 1))
                (rhs (fargn atm 2)))

; We have discovered an equiv hyp (NOT (EQUAL lhs rhs)) that is not on
; avoid-lst.

           (cond ((and (quotep lhs)
                       (quotep rhs))

; Oh! It has constant args.  We decide which way this lit goes and act
; accordingly, as we did for a quotep lit above.

                  (if (equal lhs rhs)
                      (find-trivial-equivalence1
                       not-just-quotep-flg (cdr tail) (1+ i) cl avoid-lst)
                    (mv nil nil nil nil nil)))

; So below we know that if one side is a quotep then the other side is
; not (but we don't yet know that either side is a quotep).  Observe
; that if one side is a quotep we are always safe in answering that we
; can substitute for the other side and it is only a question of
; whether we have a disposable lit or a keeper.

                 ((and not-just-quotep-flg
                       (variablep lhs)
                       (not (dumb-occur lhs rhs)))

; The 'disposable condition is met: lhs is a variable not in rhs.  But
; it could be that rhs is also a variable not in lhs.  If so, we'll
; substitute the term-order smaller for the bigger just so the user
; knows which way the substitutions will go.

                  (cond ((variablep rhs)
                         (cond
                          ((term-order lhs rhs)
                           (mv 'disposable i rhs lhs (car tail)))
                          (t (mv 'disposable i lhs rhs (car tail)))))
                        (t (mv 'disposable i lhs rhs (car tail)))))
                 ((and not-just-quotep-flg
                       (variablep rhs)
                       (not (dumb-occur rhs lhs)))
                  (mv 'disposable i rhs lhs (car tail)))
                 ((and (quotep rhs)
                       (dumb-occurs-in-some-other-lit lhs i cl 0))

; The 'keeper conditions are met: lhs is a non-quote with at least one
; occurrence in another lit and rhs is a quote.  Note that in the case
; that not-just-quotep-flg is nil, we might be giving the ``wrong''
; first answer, since if lhs is a variable then 'keeper should be
; 'disposable.  However, if not-just-quotep-flg is nil, then we will
; be ignoring that answer anyhow; see the call of
; subst-equiv-and-maybe-delete-lit in remove-trivial-equivalences.

                  (mv 'keeper i lhs rhs (car tail)))
                 ((and (quotep lhs) ; thus rhs is a non-quotep
                       (dumb-occurs-in-some-other-lit rhs i cl 0))
                  (mv 'keeper i rhs lhs (car tail)))
                 (t (find-trivial-equivalence1
                     not-just-quotep-flg
                     (cdr tail) (1+ i) cl avoid-lst)))))
        (t (find-trivial-equivalence1
            not-just-quotep-flg
            (cdr tail) (1+ i) cl avoid-lst))))

(defun find-trivial-equivalence (not-just-quotep-flg cl avoid-lst)

; We look for a literal of cl of the form (NOT (EQUAL lhs rhs)) where
; either of two conditions apply.
;    name          condition
; disposable:    lhs is a variable and rhs does not contain lhs.
; keeper:        lhs is any non-quotep and rhs is a quotep and lhs has
;                 an occurrence in some other literal of the clause

; In addition, we accept commuted version of the equivalence and we
; treat each variablep literal, var, as the trivial equivalence (NOT
; (EQUAL var 'NIL)).

; If we find such a literal we return 5 values: the name of the condition
; detected, the location i of the literal, lhs, rhs and the literal
; itself.  Otherwise we return 5 nils.

; The driver of this function, remove-trivial-equivalences, will substitute rhs
; for lhs throughout cl, possibly delete the literal, and then call us again to
; look for the next trivial equivalence.  This raises a problem.  If the driver
; doesn't delete the literal, then we will return the same one again and loop.
; So the driver supplies us with a list of literals to avoid, avoid-lst, and
; will put onto it each of the literals that has been used but not deleted.

; So consider a clause like
; (implies (and (equal (foo b) 'evg)   [1]
;               (equal a b))           [2]
;          (p (foo a) (foo b)))

; The first trivial equivalence is [1].  The driver substitutes 'evg
; for (foo b) but doesn't delete the literal.  So we get:
; (implies (and (equal (foo b) 'evg)   [1]
;               (equal a b))           [2]
;          (p (foo a) 'evg))
; and the admotion against using (equal (foo b) 'evg).  But now we see
; [2] and the driver substitutes a for b (because a is smaller) and deletes
; [2].  So we get:
; (implies (equal (foo a) 'evg)        [1]
;          (p (foo a) 'evg))
; and the old admotion against using (equal (foo b) 'evg).  Here we find [1]
; ``again'' because it is no longer on the list of things to avoid.  Indeed, we
; can even use it to good effect.  Of course, once it is used both it and the
; old avoided literal are to be avoided.

; So can this loop?  No.  Every substitution reduces term-order.

  (find-trivial-equivalence1 not-just-quotep-flg cl 0 cl avoid-lst))

(defun subst-equiv-and-maybe-delete-lit (new old n cl i delete-flg ens wrld)

; Substitutes new for old (which are EQUAL) in every literal of cl
; except the nth one.  The nth literal is deleted if delete-flg is t
; and is skipped but included if delete-flg is nil.  We return the new
; clause.  It is possible that this fn will return a clause
; dramatically shorter than cl, because lits may evaporate upon
; evaluation or merge with other literals.  We may also prove the
; clause.

  (cond
   ((endp cl) nil)
   ((int= n i)
    (let ((cl1
           (subst-equiv-and-maybe-delete-lit new old n (cdr cl) (1+ i)
                                             delete-flg ens wrld)))
      (cond
       (delete-flg cl1)
       (t (add-literal (car cl) cl1 nil)))))
   ((dumb-occur old (car cl))
    (mv-let (hitp lit)
            (subst-equiv-expr new old (car cl) ens wrld)
            (declare (ignore hitp))
            (let ((cl1
                   (subst-equiv-and-maybe-delete-lit new old n (cdr cl) (1+ i)
                                                     delete-flg ens wrld)))
              (add-literal lit cl1 nil))))
   (t (let ((cl1
             (subst-equiv-and-maybe-delete-lit new old n
                                               (cdr cl) (1+ i)
                                               delete-flg ens wrld)))
        (add-literal (car cl) cl1 nil)))))

; In the ACL2 version of remove-trivial-equivalences there is no nnn.
; The argument that it terminates is based on the observation, above,
; that every substitution reduces term order.  But I don't want to
; prove that and it is not possible to prove the termination of this
; function without carefully analyzing the conditions on the choice of
; the trivial equivalence and what happens during substitution and
; evaluation.  In particular, there is no argument based solely on the
; growth of avoid-lst and the fact that the choice of trivial
; equivalence comes from cl and is not in avoid-lst.  Imagine that
; literals are the natural numbers and that the first literal in the
; initial cl is 0.  Imagine that find-trivial-equivalence chooses the
; first literal.  Imagine that subst-equiv-and-maybe-delete-lit
; deletes the first literal and replaces it by the integer one
; greater.  Then this function will repeatedly select ever increasing
; naturals and avoid-lst will always contain all naturals below the
; next one selected.

(defun remove-trivial-equivalences1 (cl remove-flg ens wrld hitp avoid-lst nnn)

; This function looks for two kinds of equivalence hypotheses in cl and uses
; them to do substitutions.  By "equivalence hypothesis" we mean a literal of
; the form (not (EQUAL lhs rhs)) that is not on avoid-lst.  The two kinds are
; called "trivial var equivalences" and "trivial quote equivalences."  If we
; find an equation of the first sort we substitute one side for the other and
; delete the equivalence (provided remove-flg is t).  If we find an equation of
; the second sort, we substitute one side for the other but do not delete the
; equivalence.  See find-trivial-equivalence for more details, especially
; concerning avoid-lst.  Hitp is an accumulator that records whether we did
; anything.

; The justification for deleting (not (EQUAL var term)) when var occurs nowhere
; in the clause is (a) it is always sound to throw out a literal, and (b) it is
; heuristically safe here because var is isolated and EQUAL is reflexive: if
; (implies (EQUAL var term) p) is a theorem so is p because (EQUAL term term).

; We return (mv hitp' cl').

; No Change Loser.

  (declare (xargs :measure (acl2-count nnn)))
  (if (zp nnn)
      (mv hitp cl)
    (mv-let (condition lit-position lhs rhs lit)
            (find-trivial-equivalence remove-flg cl avoid-lst)
            (cond
             (lit-position
              (let ((new-cl (subst-equiv-and-maybe-delete-lit
                             rhs lhs lit-position cl 0
                             (and remove-flg (eq condition 'disposable))
                             ens wrld)))
                (remove-trivial-equivalences1 new-cl remove-flg ens wrld t
                                              (cons lit avoid-lst)
                                              (- nnn 1))))
             (t (mv hitp cl))))))

(defun remove-trivial-equivalences (cl remove-flg ens wrld hitp avoid-lst)
  (remove-trivial-equivalences1 cl remove-flg ens wrld hitp avoid-lst
                                (len cl)))

; The termination argument for the next clique was interesting.  It
; took me a while to find it!  Ultimately what I did was imagine
; eliminating subsumes entirely by expanding the call to it in
; subsumes1.  Then I recognized the lex order on <tl1,tl2> and so then
; added the counter to give subsumes1 permission to call subsumes.

(mutual-recursion

(defun subsumes (cl1 cl2 alist)

  (declare (xargs :measure (acl2::nat-list-measure
                            (list (acl2-count cl1) 1 (acl2-count cl2)))))

; We return t iff some instance of clause cl1 is a subset of
; clause cl2 (where the instance is an extension of alist).

  (cond ((endp cl1) t)
        (t (subsumes1 (car cl1) (cdr cl1) cl2 cl2 alist))))

(defun subsumes1 (lit tl1 tl2 cl2 alist)

  (declare (xargs :measure (acl2::nat-list-measure
                            (list (acl2-count tl1) 2 (acl2-count tl2)))))

; If we can extend alist to an alist1 so that lit/alist1 is a member
; of tl2 and tl1/alist1 is a subset of cl2, we return t.  Else we
; return nil.

  (cond ((endp tl2) nil)
        (t (mv-let (wonp alist1)
             (one-way-unify1 lit (car tl2) alist)
             (cond ((and wonp (subsumes tl1 cl2 alist1))
                    t)
                   (t (subsumes1 lit tl1 (cdr tl2) cl2 alist)))))))

)

(defun some-member-subsumes (cl-set cl)
  (cond ((endp cl-set) nil)
        ((subsumes (car cl-set) cl nil) t)
        (t (some-member-subsumes (cdr cl-set) cl))))

(defrec built-in-clause (nume all-fnnames . clause))

; The world global, (global-val 'built-in-clauses wrld), will be an
; alist pairing function symbols with lists of built-in-clause
; records.  The global is set from the corresponding ACL2 global when
; the Paco world is built.  See database.lisp.

(defun built-in-clausep2 (bic-lst cl fns ens)
  (cond ((endp bic-lst) nil)
        ((and (enabled-numep (access built-in-clause (car bic-lst) :nume)
                             ens)
              (subsetp-eq (access built-in-clause (car bic-lst) :all-fnnames)
                          fns)
              (subsumes (access built-in-clause (car bic-lst) :clause)
                        cl nil))
         (<built-in-clausep2-id>
          t))
        (t (built-in-clausep2 (cdr bic-lst) cl ens fns))))

(defun built-in-clausep1 (bic-alist cl ens fns)

; Bic-alist is the alist of built-in clauses, organized via top fnname.  Cl is
; a clause and fns is the all-fnnames-lst of cl.  This function is akin to
; some-member-subsumes in the sense of some built-in clause subsumes cl.  We
; only try subsumption on built-in clauses whose :all-fnnames field is
; a subset of fns.

  (cond ((endp bic-alist) nil)
        ((or (null (caar bic-alist))
             (member-eq (caar bic-alist) fns))

; All the built-in clauses in this pot have the same top-fnname and that name
; occurs in cl.  So these guys are all candidate subsumers.  Note:  if (car
; bic-alist) is null then this is the special pot into which we have put all
; the built-in clauses that have no "function symbols" in them, as computed by
; all-fnnames-subsumer.  I don't see how this can happen, but if it does we're
; prepared!

         (or (built-in-clausep2 (cdr (car bic-alist)) cl ens fns)
             (built-in-clausep1 (cdr bic-alist) cl ens fns)))
        (t (built-in-clausep1 (cdr bic-alist) cl ens fns))))

(defun trivial-clause-p (cl ens wrld)
  (or (member-equal *t* cl)
      (tautologyp (disjoin cl) ens wrld)))

(defun built-in-clausep (cl ens wrld)

; We return t iff cl is ``built in''.

  (cond ((trivial-clause-p cl ens wrld) t)
        (t (built-in-clausep1 (global-val 'built-in-clauses wrld)
                              cl
                              ens
                              (all-fnnames-lst cl)))))

(defun crunch-clause-segments1 (seg1 cl)

; This function reverses seg1 and appends it to cl, like (revappend seg1
; cl), However, if a literal in seg1 already occurs in cl, it is merged
; into that literal.

  (cond ((endp seg1) cl)
        (t (crunch-clause-segments1 (cdr seg1)
                                    (add-literal (car seg1) cl nil)))))

(defun crunch-clause-segments2 (cl seg1)

; See crunch-clause-segments.  We scan down cl until we see the marker
; literal, accumulating the earlier lits into seg1. We return (mv seg1
; cl).

  (cond ((endp cl) (mv seg1 nil))
        ((and (consp (car cl))
              (eq (ffn-symb (car cl)) 'car)
              (eq (fargn (car cl) 1) :crunch-clause-segments-marker))
         (mv seg1 (cdr cl)))
        (t (crunch-clause-segments2 (cdr cl)
                                    (cons (car cl) seg1)))))

(defun crunch-clause-segments (seg1 seg2 ens wrld)

; This function is a special purpose subroutine of rewrite-clause.  Seg1 and
; seg2 are just lists of literals.  Pts1 is in weak 1:1 correspondence with
; seg1 and enumerates the parent trees of the corresponding literals of seg1.
; Consider the clause obtained by appending these two segments.

; {lit4 ... lit7 lit1' ... lit2' lit3a ... lit3z}    ; cl

; |  <- seg1 -> | <- seg2 ->                   |

;  unrewritten  |  rewritten

; Context: The rewriter is sweeping through this clause, rewriting each literal
; and assembling a new clause.  It has rewritten none of the seg1 literals and
; all of the seg2 literals.  It has just rewritten some literal called lit3.
; After clausifying the result (and getting in this case lit3a ... lit3z) it is
; about to start rewriting the first literal of seg1, lit4.  It has already
; rewritten lit1'...lit2'.  The rewriter actually keeps the unrewritten part of
; the clause (seg1) separate from the rewritten part (seg2) so that it knows
; when it is done.  In the old days, it would just proceed to rewrite the first
; literal of seg1.

; But suppose lit3 was something like (not (member x '(...))).  Then
; we will get lots of segs, each of the form (equal x '...).  We are
; trying to optimize our handling of this by actually stuffing the
; constant into the clause and running any terms we can.  We do this
; in what we think is a very elegant way: We actually create cl and
; call remove-trivial-equivalences on it.  Then we recover the two
; parts, unrewritten and rewritten.  The trick is how we figure out
; which is which.  We put a marker literal into the clause, after seg1
; and before seg2.  Remove-trivial-equivalences may do a lot of
; literal evaluation and deletion.  But then we find the marker
; literal and consider everything to its left unrewritten and
; everything else rewritten.

; We return two values: The unrewritten part of cl and the rewritten
; part of cl.

  (let* ((marker '(car :crunch-clause-segments-marker))
         (cl (crunch-clause-segments1 seg1 (cons marker seg2))))
    (mv-let (hitp cl)
            (remove-trivial-equivalences cl nil ;;; see Note below
                                         ens wrld nil nil)

; Note: In the call of remove-trivial-equivalences above we use
; remove-flg = nil.  At one time, we used remove-flg = t.  But if
; there is auxiliary information around -- e.g., the linear arithmetic
; database in ACL2 -- that data may mention the eliminated variable.
; So we keep them until we are at the top of the process again.

            (cond
             ((null hitp)
              (mv seg1 seg2))
             (t (mv-let (seg1 seg2)
                        (crunch-clause-segments2 cl nil)
                        (mv seg1 seg2)))))))


(mutual-recursion

(defun rewrite-clause (tail new-clause wrld rcnst flg ans nnn)

; Note: When rewrite-clause is called, nnn should be set to (len
; tail), where tail is the first argument supplied to rewrite-clause.
; See the note below about the admission of this function.

  (declare (xargs :measure (acl2::nat-list-measure (list nnn 1 0))
                  :hints (("Goal" :in-theory
                           (disable remove-trivial-equivalences
                                    crunch-clause-segments
                                    DISJOIN-CLAUSE-SEGMENT-TO-CLAUSE-SET
                                    NORMALIZE
                                    type-alist-clause
                                    strip-branches
                                    acl2-count)))))

; We are to rewrite the literals of the clause cl formed by appending
; tail to new-clause.  We assume rcnst has the correct top-clause and
; current-clause.  We return (mv flg ans), where flg indicates whether
; anything was done and ans is a set of clauses whose conjunction
; implies cl.

  (cond
   ((or (endp tail)
        (zp nnn))

; We choose nnn large enough so that (endp tail) will always be true
; before or when (zp nnn) becomes true.  But just in case, if we run
; out of nnn before rewriting all the literals in tail, we just tack
; them onto the rewritten part, new-clause, and call that our result.
; We never expect this to happen.  See the discussion below about the
; termination of rewrite-clause.

    (let ((new-clause (crunch-clause-segments1 tail new-clause)))
      (cond
       ((built-in-clausep1 (global-val 'built-in-clauses wrld)
                           new-clause
                           (access rewrite-constant rcnst :ens)
                           (all-fnnames-lst new-clause))
        (mv t ans))
       (t (mv flg (cons new-clause ans))))))
   (t
    (mv-let
     (not-flg atm)
     (strip-not (car tail))
     (let ((local-rcnst
            (change rewrite-constant rcnst
                    :current-literal
                    (make current-literal
                          :not-flg not-flg
                          :atm atm))))
       (mv-let
        (contradictionp type-alist)
        (rewrite-clause-type-alist tail new-clause
                                   (access rewrite-constant rcnst :ens)
                                   wrld)
        (cond
         (contradictionp
          (mv t ans))
         (t
          (let* ((val1 (rewrite-atm atm not-flg type-alist wrld local-rcnst))
                 (val2 (if not-flg (dumb-negate-lit val1) val1))
                 (branches (clausify val2
                                     (access rewrite-constant rcnst :ens)
                                     wrld))
                 (action (rewrite-clause-action (car tail) branches))
                 (segs

; Perhaps we can simply use branches below.  But that requires some thought,
; because the form below handles true clauses (including *true-clause*) with
; special care.  This issue arose as we removed old-style-forcing from the
; code.

                  (disjoin-clause-segment-to-clause-set nil branches)))
            (rewrite-clause-lst segs
                                (cdr tail)
                                new-clause
                                wrld
                                rcnst
                                (or flg (not (eq action 'no-change)))
                                ans
                                (- nnn 1)))))))))))


(defun rewrite-clause-lst (segs cdr-tail new-clause wrld rcnst flg ans nnn)
  (declare (xargs :measure (acl2::nat-list-measure (list nnn 2 (len segs)))))
  (cond
   ((endp segs) (mv flg ans))
   (t
    (mv-let
     (flg1 ans1)
     (rewrite-clause-lst (cdr segs) cdr-tail new-clause wrld rcnst flg ans nnn)
     (mv-let (unrewritten rewritten)
             (crunch-clause-segments
              cdr-tail
              (append new-clause
                      (set-difference-equal (car segs) new-clause))
              (access rewrite-constant rcnst :ens)
              wrld)
             (rewrite-clause unrewritten
                             rewritten
                             wrld
                             rcnst
                             flg1
                             ans1
                             nnn))))))

)

; Essay on the Admission of Rewrite-clause

; In ACL2, rewrite-clause does not have the nnn argument.  It is there in
; Paco only to make the termination argument easier.  Consider the definition
; of rewrite-clause and rewrite-clause-lst obtained by removing all mention of
; nnn.  I could get that definition admitted if I could prove:

; (defthm len-car-crunch-clause-segments
;   (<= (len (car (crunch-clause-segments seg1 seg2 ens wrld)))
;       (len seg1))
;  :rule-classes :linear)

; But this cannot be proved without a lot of reasoning about the
; world. Here is the problem.  The definition of
; crunch-clause-segments conses a marker literal between the two
; segments, runs remove-trivial-equivalences on the resulting clause,
; and then extracts the two segments.  The "theorem" above says that
; the first extracted segment is no longer than the original input
; segment.  But what happens if remove-trivial-equivalences eliminates
; the marker literal, e.g., by evaluating it to NIL?  Then the
; extracted segment is the whole clause, which is in general longer
; than seg1 alone.  Why do I know remove-trivial-equivalences cannot
; eliminate the marker?  The marker is (CAR
; :CRUNCH-CLAUSE-SEGMENTS-MARKER).  Call this (CAR :C) for short.  I
; could probably prove that (CAR :C) will not evaluate to NIL if I
; knew :C doesn't occur elsewhere in the clause.  But for all I know,
; there is a literal elsewhere that says (CAR :C) is NIL.  What stops
; that?  :C is not a legal variable symbol.  But where have I
; established that?  I don't want to go this deeply into the problem.

; Instead, I introduced nnn.  It should be set initially to the length
; of the first argument, tail, in rewrite-clause.  That is the number
; of unrewritten literals.  It will not grow.  It could shrink if some
; unrewritten literals evaluate to NIL in remove-trivial-equivalences.
; But no new unrewritten literals are ever introduced.  So this definition
; is easier to admit, just as powerful as ACL2's, and only marginally
; less efficient.

(defun simplify-clause1 (top-clause rcnst wrld)

; Top-clause is a clause with history hist.  We assume that rcnst
; contains appropriate settings (i.e., from induct) and we install the
; rewrite-specific fields below.

; We return 2 values.  The first indicates whether we changed
; top-clause.  If we did not, the second is nil.  If we did change
; top-clause, the second is a list of new clauses whose conjunction
; implies top-clause.

  (mv-let (hitp current-clause)
          (remove-trivial-equivalences top-clause t
                                       (access rewrite-constant rcnst :ens)
                                       wrld nil nil)
          (let ((local-rcnst (change rewrite-constant rcnst
                                     :top-clause top-clause
                                     :current-clause current-clause)))

; When we call rewrite-clause, below, we pass in as the initial value
; of its ``did we change anything?'' accumulator the flg, hitp, that
; indicates whether remove-trivial-equations changed anything.  Thus,
; this call may answer ``yes, something was changed'' when in fact,
; nothing was done by rewrite-clause itself.

            (rewrite-clause current-clause nil wrld local-rcnst
                            hitp nil (len current-clause)))))

(defun some-element-dumb-occur-lst (lst1 lst2)
  (cond ((endp lst1) nil)
        ((dumb-occur-lst (car lst1) lst2) t)
        (t (some-element-dumb-occur-lst (cdr lst1) lst2))))

; The Spec Vars of Prove -- pspv

; The theorem prover, prove, uses so many special variables that are rarely
; modified that we bundle them up.  Because simplify-clause, below, is a
; clause processor in the waterfall, it is the first function in this
; development that is high enough up in the hierarchy to see prove's
; bundle of variables.  So it is time to lay out prove's spec vars:

(defrec prove-spec-var
  (((rewrite-constant . induct-hint-val)
    .
    (induction-hyp-terms . induction-concl-terms))
   .
   (((do-not-processes . hint-settings)
     .
     (global-ens . unused-slot)))))

;=================================================================

; Clause Histories

; Clauses carry with them their histories, which describe which
; processes have produced them.  A clause history is a list of
; history-entry records.  It is in reverse chronological order.  A
; process, such as simplify-clause, might inspect the history of its
; input clause to help decide whether to perform a certain
; transformation.

(defrec history-entry
  (processor clause . alist))

; Processor is a waterfall processor (e.g., 'simplify-clause).  Clause
; is its input.  The alist is an alist produced by the processor on
; clause used to record what that processor did, in a format that is
; essentially unique for each processor.  However, any processor that
; introduces new variables into a clause must include in its alist
; a pair of the form (:VARIABLES . vars), where vars are the newly
; introduced variables.

; Each history-entry is built in the waterfall, but we inspect them
; for the first time in this file.

(defun settled-since-inductionp (hist)

; Scan back to the last induct-clause (or to the beginning of hist)
; and determine whether there is a settled-down-clause since then.
; Below are some examples, where simp means a simplify-clause history
; entry, etc.

; hist                                     ; result

; (simp simp)                                nil
; (simp settled simp)                        t
; (simp induct simp settled simp)            nil
; (settled simp induct simp settled simp)    t

  (cond ((endp hist) nil)
        ((eq (access history-entry (car hist) :processor)
             'settled-down-clause)
         t)
        ((eq (access history-entry (car hist) :processor)
             'induct-clause)
         nil)
        (t (settled-since-inductionp (cdr hist)))))

(defun simplify-clause (id cl hist pspv wrld)

; This is the main "clause processor" of the waterfall.  Its input and
; output spec is consistent with that of all such processors.  See the
; waterfall for a general discussion.

  (declare (ignore id))

; Cl is a clause with clause id id and history hist.  We can obtain a
; rewrite-constant from the prove spec var pspv.  We assume nothing
; about the rewrite-constant except that it has the appropriate
; contextual settings (e.g., from induct).  We install
; rewrite-specific fields when necessary.

; We return 4 values.  The first is a signal that in general is 'HIT,
; 'MISS, 'ABORT, or anything else, indicating an unexpected error.  In
; this case, the signal is always either 'HIT or 'MISS.  When the
; signal is 'MISS, the other 3 values are irrelevant.  When the signal
; is 'HIT, the second result is the list of new clauses, the third is
; an alist (in this case nil) that will become the :alist component of
; the history-entry for this simplification, and the fourth is the new
; (but in this case unmodified) pspv.  The third and fourth return
; values here are present only to follow the standard calling
; conventions for waterfall processors.

; If the first result is 'HIT then the conjunction of the new clauses
; returned implies cl.  Equivalently, under the assumption that cl is
; false, cl is equivalent to the conjunction of the new clauses.

  (cond ((settled-since-inductionp hist)

; The clause has settled down under rewriting with the
; induction-hyp-terms ignored and the induction-concl-terms forcibly
; expanded.  In general, we now want to stop treating those terms
; specially and continue simplifying.  However, there is a special
; case that will save a little time.  Suppose that the clause just
; settled down -- i.e., the most recent hist entry is the one we just
; found.  And suppose that none of the specially treated terms occurs
; in the clause we're to simplify.  Then we needn't simplify it again.

         (cond ((and (eq 'settled-down-clause
                         (access history-entry (car hist) :processor))
                     (not (some-element-dumb-occur-lst
                           (access prove-spec-var
                                   pspv
                                   :induction-hyp-terms)
                           cl)))

; Since we know the induction-concl-terms couldn't occur in the clause --
; they would have been expanded -- we are done.  This test should
; speed up base cases and preinduction simplification at least.

                (mv 'miss nil nil nil))
               (t

; We now cease interfering and let the heuristics do their job.

                (mv-let (changedp clauses)
                        (simplify-clause1
                         cl
                         (access prove-spec-var pspv :rewrite-constant)
                         wrld)
                        (cond (changedp

; Note: It is possible that our input, cl, is a member-equal of our
; output, clauses!  Such simplifications are said to be "specious."
; But we do not bother to detect that here because we want to report
; the specious simplification as though everything were ok and then
; pretend nothing happened.  This gives the user some indication of
; where the loop is.  In the old days, we just signalled a 'miss if
; (member-equal cl clauses) and that caused a lot of confusion among
; experienced users, who saw simplifiable clauses being passed on to
; elim, etc.  See :DOC specious-simplification.

                               (mv 'hit clauses nil pspv))
                              (t (mv 'miss nil nil nil)))))))
        (t

; The clause has not settled down yet.  So we arrange to ignore the
; induction-hyp-terms and to expand the induction-concl-terms without
; question.  The local-rcnst created below is not passed out of this
; function.

         (let* ((rcnst (access prove-spec-var pspv :rewrite-constant))
                (local-rcnst
                 (change rewrite-constant
                         rcnst
                         :terms-to-be-ignored-by-rewrite
                         (append
                          (access prove-spec-var
                                  pspv :induction-hyp-terms)
                          (access rewrite-constant
                                  rcnst :terms-to-be-ignored-by-rewrite))
                         :expand-lst
                         (append (access prove-spec-var
                                          pspv :induction-concl-terms)
                                 (access rewrite-constant
                                         rcnst :expand-lst)))))
           (mv-let (changedp clauses)
                   (simplify-clause1 cl local-rcnst wrld)
                   (cond
                    (changedp (mv 'hit clauses nil pspv))
                    (t (mv 'miss nil nil nil))))))))

; Inside the waterfall, the settled-down-clause processor immediately
; follows simplify-clause.  Its presence in the waterfall causes us to
; add a 'settled-down-clause hist-entry to the history of the clause
; when simplify-clause finishes with it.  The "hit state" of the
; waterfall leads back to the simplifier, where the code above detects
; this settling down and turns off the handling of the induction hyp
; and concl terms.  The "miss state" of the waterfall leads to the
; next processor.

(defun hit-it-againp (hist)

; This function should only be called in settled-down-clause, i.e.,
; when the clause has settled down.  The question is: do we want to
; hit the clause with another round of simplification, by claiming a
; HIT now?  Why would we do that?  If we've come from induction,
; simplify-clause has short-circuited the normal heuristics.  Claiming
; a HIT here will cause simplify-clause to behave ``normally.''  There
; is no point in going back to the top of the waterfall if (a) we
; haven't seen an induction yet (i.e., the user's input didn't change
; under the first simplification), or (b) there is an induction in the
; history but the clause already settled-down after it.

  (cond
   ((endp hist) nil)
   ((eq (access history-entry (car hist) :processor) 'induct-clause)
    t)
   ((eq (access history-entry (car hist) :processor) 'settled-down-clause)
    nil)
   (t (hit-it-againp (cdr hist)))))

(defun settled-down-clause (id clause hist pspv wrld)

; This is the processor in the waterfall just after simplify-clause.
; If we get here, simplify-clause has MISSed.

  (declare (ignore id wrld))
  (cond ((hit-it-againp hist)
         (mv 'HIT (list clause) nil pspv))
        (t (mv 'MISS nil nil nil))))
