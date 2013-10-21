;; Patch by Matt Kaufmann to permit forcing in some cases where ACL2 disables it.

(in-package "ACL2")

(mutual-recursion

(defun lambda-subtermp (term)

; We determine whether some lambda-expression is used as a function in term.

  (if (or (variablep term)
          (fquotep term))
      nil
    (or (flambdap (ffn-symb term))
        (lambda-subtermp-lst (fargs term)))))

(defun lambda-subtermp-lst (termlist)
  (if termlist
      (or (lambda-subtermp (car termlist))
          (lambda-subtermp-lst (cdr termlist)))
    nil))

)

(defun rewrite-atm (atm not-flg bkptr gstack type-alist wrld
                        simplify-clause-pot-lst rcnst current-clause state)

; This function rewrites atm with nth-update-rewriter, recursively.
; Then it rewrites the result with rewrite, in the given context,
; maintaining iff.

; Note that not-flg is only used heuristically, as it is the
; responsibility of the caller to account properly for it.
; Current-clause is also used only heuristically.

; It is used to rewrite the atoms of a clause as we sweep across.  It
; is just a call of rewrite -- indeed, it didn't exist in Nqthm and
; rewrite was called in its place -- except for one thing: it first
; gives type-set a chance to decide things.  See the note about
; pegate-lit in rewrite-clause.

  (mv-let (knownp nilp ttree)
          (known-whether-nil atm type-alist
                             (access rewrite-constant rcnst
                                     :current-enabled-structure)
                             (ok-to-force rcnst)
                             wrld
                             nil)
          (cond

; Before Version  2.6 we had

;           (knownp
;            (cond (nilp (mv *nil* ttree))
;                  (t (mv *t* ttree))))

; but this allowed type-set to remove ``facts'' from a theorem which
; may be needed later.  The following transcript illustrates the previous
; behavior:
#|
 ACL2 !>(defthm fold-consts-in-+
          (implies (and (syntaxp (consp c))
                        (syntaxp (eq (car c) 'QUOTE))
                        (syntaxp (consp d))
                        (syntaxp (eq (car d) 'QUOTE)))
                   (equal (+ c d x)
                          (+ (+ c d) x))))
 ACL2 !>(defthm helper
          (implies (integerp x)
                   (integerp (+ 1 x))))
 ACL2 !>(thm
          (implies (integerp (+ -1/2 x))
                   (integerp (+ 1/2 x)))
          :hints (("Goal" :use ((:instance helper
                                           (x (+ -1/2 x)))))))

 [Note:  A hint was supplied for our processing of the goal above.
 Thanks!]

 ACL2 Warning [Use] in ( THM ...):  It is unusual to :USE an enabled
 :REWRITE or :DEFINITION rule, so you may want to consider disabling
 (:REWRITE HELPER).


 We now augment the goal above by adding the hypothesis indicated by
 the :USE hint.  The hypothesis can be derived from HELPER via instantiation.
 The augmented goal is shown below.

 Goal'
 (IMPLIES (IMPLIES (INTEGERP (+ -1/2 X))
                   (INTEGERP (+ 1 -1/2 X)))
          (IMPLIES (INTEGERP (+ -1/2 X))
                   (INTEGERP (+ 1/2 X)))).

 By case analysis we reduce the conjecture to

 Goal''
 (IMPLIES (AND (OR (NOT (INTEGERP (+ -1/2 X)))
                   (INTEGERP (+ 1 -1/2 X)))
               (INTEGERP (+ -1/2 X)))
          (INTEGERP (+ 1/2 X))).

 This simplifies, using primitive type reasoning, to

 Goal'''
 (IMPLIES (INTEGERP (+ -1/2 X))
          (INTEGERP (+ 1/2 X))).

 Normally we would attempt to prove this formula by induction.  However,
 we prefer in this instance to focus on the original input conjecture
 rather than this simplified special case.  We therefore abandon our
 previous work on this conjecture and reassign the name *1 to the original
 conjecture.  (See :DOC otf-flg.)

 No induction schemes are suggested by *1.  Consequently, the proof
 attempt has failed.

 Summary
 Form:  ( THM ...)
 Rules: ((:DEFINITION IMPLIES)
         (:DEFINITION NOT)
         (:FAKE-RUNE-FOR-TYPE-SET NIL))
 Warnings:  Use
 Time:  0.03 seconds (prove: 0.02, print: 0.01, other: 0.00)

 ******** FAILED ********  See :DOC failure  ******** FAILED ********
 ACL2 !>
|#

; Note that in the transition from Goal'' to Goal''', the needed
; fact --- (INTEGERP (+ 1 -1/2 X)) --- was removed by type reasoning.
; This is not good.  We now only use type reasoning at this point if
; it will give us a win.

; One might ask why we only disallow type-set from removing facts here.
; Why not elswhere, and what about rewrite?  We do it this way because
; it is only here that the user cannot prevent this removal from
; happening by manipulating the enabled structure.

           ((and knownp not-flg nilp)

; We have reduced the atm to nil but it occurs negated in the
; clause and so we have reduced the literal to t, proving the clause.
; So we report this reduction.

            (mv *nil* ttree))
           ((and knownp (not not-flg) (not nilp))
            (mv *t* ttree))
           (t
            (mv-let
             (hitp atm1 ttree1)
; Rockwell Addition
             (cond
              ((eq (nu-rewriter-mode wrld) :literals)
               (nth-update-rewriter t atm nil
                                    (access rewrite-constant rcnst
                                            :current-enabled-structure)
                                    wrld state))
              (t (mv nil nil nil)))
             (let ((atm2 (if hitp
                             (lambda-abstract
                              (cleanup-if-expr atm1 nil nil)
                              (pkg-witness (current-package state)))
                           atm)))
               (mv-let (ans1 ans2)
                       (rewrite-entry
                        (rewrite atm2
                                 nil
                                 bkptr)
                        :rdepth (rewrite-stack-limit wrld)
                        :type-alist type-alist
                        :obj '?
                        :geneqv *geneqv-iff*
                        :wrld wrld
                        :fnstack nil
                        :ancestors nil
                        :backchain-limit (backchain-limit wrld)
                        :simplify-clause-pot-lst simplify-clause-pot-lst
                        :rcnst rcnst
                        :gstack gstack
                        :ttree (if hitp ttree1 nil))

; But we need to do even more work to prevent type-set from removing
; ``facts'' from the goal.  Here is another (edited) transcript:

#|
 ACL2 !>(defun foo (x y)
   (if (acl2-numberp x)
       (+ x y)
     0))

 ACL2 !>(defthm foo-thm
   (implies (acl2-numberp x)
            (equal (foo x y)
                   (+ x y))))
 ACL2 !>(in-theory (disable foo))
 ACL2 !>(thm
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (equal (foo x y) x))
           (equal y 0)))

 This simplifies, using the :type-prescription rule FOO, to

 Goal'
 (IMPLIES (AND (ACL2-NUMBERP Y)
               (EQUAL (FOO X Y) X))
          (EQUAL Y 0)).

 Name the formula above *1.

 No induction schemes are suggested by *1.  Consequently, the proof
 attempt has failed.

 Summary
 Form:  ( THM ...)
 Rules: ((:TYPE-PRESCRIPTION FOO))
 Warnings:  None
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

 ******** FAILED ********  See :DOC failure  ******** FAILED ********
|# ; |

; Note that in the transition from Goal to Goal' we removed the critical fact
; that x was an acl2-numberp.  This fact can be derived from the third
; hypothesis --- (equal (foo x y) x) --- via :type-prescription rule FOO as
; indicated.  However, when we then go on to rewrite the third hypothesis, we
; are not able to rederive this fact, since the type-alist used at that point
; does not use use the third hypothesis so as to prevent tail-biting.

; Robert Krug has seen this sort of behavior in reasoning about floor and mod.
; In fact, that experience motivated him to provide the original version of the
; code below not to remove certain additional facts.

; Finally, note that even before this additional care, the lemma

#|
 (thm
  (implies (and (acl2-numberp y)
                (equal (foo x y) x)
                (acl2-numberp x))
           (equal y 0)))
|# ;|

; does succeed, since the (acl2-numberp x) hypothesis now appears after the
; (equal (foo x y) x) hypothesis, hence does not get removed until after it has
; been used to relieve the hypothesis of foo-thm.  This kind of situation in
; which a proof succeeds or fails depending on the order of hypotheses really
; gets Robert's goat.

		 (cond ((not (or (equal ans1 *nil*)
                                 (equal ans1 *t*)))

; We have, presumably, not removed any facts, so we allow this rewrite.

                        (mv ans1 ans2))
                       ((and (nvariablep atm2)
                             (not (fquotep atm2))
                             (equivalence-relationp (ffn-symb atm2)
                                                    wrld))

; We want to blow away equality (and equivalence) hypotheses, because for
; example there may be a :use or :cases hint that is intended to blow away (by
; implication) such hypotheses.

                        (mv ans1 ans2))
                       ((equal ans1 (if not-flg *nil* *t*))

; We have proved the original literal from which atm is derived; hence we have
; proved the clause.  So we report this reduction.

                        (mv ans1 ans2))
                       ((all-type-reasoning-tags-p ans2)

; Type-reasoning alone has been used, so we are careful in what we allow.

			(cond ((lambda-subtermp atm2)

; We received an example from Jared Davis in which a hypothesis of the form
; (not (let ...)) rewrites to true with a tag tree of nil, and hence was kept
; without this lambda-subtermp case.  The problem with keeping that hypothesis
; is that it has calls of IF in a lambda body, which do not get eliminated by
; clausification -- and this presence of IF terms causes the :force-info field
; to be set to 'weak in the rewrite constant generated under simplify-clause.
; That 'weak setting prevented forced simplification from occurring that was
; necessary in order to make progress in Jared's proof!

; A different solution would be to ignore IF calls in lambda bodies when
; determining whether to set :force-info to 'weak.  However, that change caused
; a regression suite failure: in books/symbolic/tiny-fib/tiny-rewrites.lisp,
; theorem next-instr-pop.  The problem seemed to be premature forcing, of just
; the sort we are trying to prevent with the above-mentioned check for IF
; terms.

; Robert Krug points out to us, regarding the efforts here to keep hypotheses
; that rewrote to true, that for him the point is simply not to lose Boolean
; hypotheses like (acl2-numberp x) in the example above.  Certainly we do not
; expect terms with lambda calls to be of that sort, or even to make any sorts
; of useful entries in type-alists.  If later we find other reasons to keep *t*
; or *nil*, we can probably feel comfortable in adding conditions as we have
; done with the lambda-subtermp test above.

                               (mv ans1 ans2))
                              ((eq (fn-symb atm2) 'implies)

; We are contemplating throwing away the progress made by the above call of
; rewrite.  However, we want to keep progress made by expanding terms of the
; form (IMPLIES x y), so we do that expansion (again) here.  It seems
; reasonable to keep this in sync with the corresponding use of subcor-var in
; rewrite.

                               (try-type-set-and-clause
                                (subcor-var (formals 'implies wrld)
                                            (list (fargn atm2 1)
                                                  (fargn atm2 2))
                                            (body 'implies t wrld))
                                ans1 ans2 current-clause wrld
                                (access rewrite-constant rcnst
                                        :current-enabled-structure)))
			      (t

; We make one last effort to allow removal of certain ``trivial'' facts from
; the goal.

			       (try-type-set-and-clause
                                atm2
                                ans1 ans2 current-clause wrld
                                (access rewrite-constant rcnst
                                        :current-enabled-structure)))))
		       (t
			(mv ans1 ans2))))))))))
